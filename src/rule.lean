import .util .table
open tactic robot
@[derive decidable_eq]
meta structure hyp :=
(n : name) (bi : binder_info) (type : expr)
meta def telescope := list hyp
meta def telescope.to_pis : expr → telescope → expr := list.foldl (λ e ⟨n,b,y⟩, expr.pi n b y e)
meta def telescope.to_lambdas : expr → telescope → expr := list.foldl (λ e ⟨n,b,y⟩, expr.lam n b y e)
private meta def telescope.of_pis_aux : telescope → expr → telescope × expr
| acc (expr.pi n bi y b) := telescope.of_pis_aux (⟨n,bi,y⟩::acc) b
| acc x := ⟨acc,x⟩
meta def telescope.of_pis : expr → (telescope × expr) := telescope.of_pis_aux []

meta def telescope.to_pattern_core : expr → tactic (expr × list expr)
|(expr.lam n bi y b) := do
   un        ← mk_fresh_name,
   let x     := expr.local_const un n bi b,
   let b := expr.instantiate_var b x,
   (p, xs) ← telescope.to_pattern_core b,
   return (p, x::xs)
|x := pure (x, [])

meta def telescope.to_pattern (t : telescope) (e : expr) : tactic pattern := do
    (e,xs) ← telescope.to_pattern_core $ telescope.to_lambdas e t,
    mk_pattern [] xs e [] xs

@[derive decidable_eq]
meta structure rule := -- relation is always `=` for now.
(id : name)
(ctxt : telescope) -- arguments, local context. [IDEA] instead; do this by just having a tactic that creates the right environment?
(lhs  : expr) 
(rhs  : expr)
(type : expr)
(pf   : expr) -- the proof expression of the given rule.

namespace rule
    meta instance has_lt : has_lt rule := ⟨λ r1 r2, (r1.lhs,r1.rhs) < (r2.lhs,r2.rhs)⟩
    meta instance has_decidable_lt 
        : decidable_rel ((<) : rule → rule → Prop)
        := by apply_instance

    meta instance : has_to_string rule := ⟨λ r, (to_string r.lhs) ++ " = " ++ (to_string r.rhs)⟩
    meta instance : has_to_tactic_format rule := 
    ⟨λ r, do
        plhs ← tactic.pp r.lhs, prhs ← tactic.pp r.rhs,
        pure $ plhs ++ " = " ++ prhs
    -- infer_type r.pf >>= whnf >>= tactic_format_expr
    ⟩

    meta def of_prf (id : name) : expr → tactic rule := λ pf, do
        t ← infer_type pf >>= whnf,
        -- trace t, 
        ⟨ctxt,`(%%lhs = %%rhs)⟩ ← pure $ telescope.of_pis t 
        | (do pft ← pp pf, ppt ← pp t, fail $ (to_fmt "rule.of_prf: supplied expression ") ++ pft ++ " : " ++ ppt ++ " is not an equality proof "),
        pure {id := id, ctxt := ctxt, lhs := lhs, rhs := rhs, pf := pf, type := t}

    meta def flip (r : rule) : tactic rule := do
        let P := r.ctxt.foldl (λ e ⟨n,b,y⟩, expr.pi n b (to_pexpr y) e) $ ```(%%r.rhs = %%r.lhs),
        T ← to_expr $ P,
        pf ← tactic.fabricate (some T) (do
            tactic.intros,
            tactic.applyc `eq.symm,
            tactic.apply_core r.pf {new_goals := new_goals.non_dep_only},
            all_goals $ try $ prop_assumption,
            skip
        ),
        pure { ctxt := r.ctxt
             , lhs  := r.rhs
             , rhs  := r.lhs
             , type := r.type
             , pf   := pf
             , id := r.id ++ `flipped
             }

    -- meta def add_simp_lemma : simp_lemmas → rule → tactic simp_lemmas := λ sl r, simp_lemmas.add sl r.pf
    meta def is_wf (r : rule) : tactic bool := do r' ← of_prf r.id $ pf $ r, pure $ r = r'
    meta def of_name (n : name) : tactic rule := resolve_name n >>= pure ∘ pexpr.mk_explicit >>= to_expr >>= rule.of_prf n
    meta def head_rewrite : rule → expr → tactic rule := λ r lhs, do
        T ← tactic.infer_type lhs,
        rhs ← tactic.mk_meta_var T,
        target ← tactic.mk_app `eq [lhs,rhs],
        pf ← tactic.fabricate target ( do
                lhspp ← pp lhs,
                rulepp ← pp r,
                --trace $ ("rewriting " : format) ++ lhspp ++" with " ++ rulepp,
                tactic.apply_core r.pf,
                all_goals $ try (apply_instance <|> prop_assumption), -- clean up typeclass instances.
                --trace_state,
                -- result >>= trace,
                pure ()
            ),  -- if new goals are created then tactic.fabricate will throw.
        of_prf r.id pf

    /-`match_rhs e r` matches `e` with `r.rhs` (ie, metavariables in r.rhs can be assigned) and returns the result. New goals might be present. -/
    -- meta def match_rhs : expr → rule → tactic unit
    -- |e r := do
    --     notimpl

    /--Returns true when the left hand side is a variable or metavariable. -/
    meta def lhs_wildcard : rule → bool := λ r, expr.is_var r.lhs || expr.is_mvar r.lhs
    /--Returns true when the right hand side is a variable or metavariable. -/
    meta def rhs_wildcard : rule → bool := λ r, expr.is_var r.rhs || expr.is_mvar r.rhs
    private meta def specify_aux : nat → expr → expr
    |0 acc := acc
    |(n+1) acc := specify_aux n $ expr.app acc (expr.var n)
    
    private meta def specify_aux₂ : list (hyp × option expr) → expr → expr
    |[] e := e
    |(⟨⟨n,b,y⟩, some E⟩::rest) e := specify_aux₂ rest $ expr.instantiate_var e E
    |(⟨⟨n,b,y⟩, none⟩ :: rest) e := specify_aux₂ rest $ expr.lam n b y e

    meta def specify : list (option expr) → rule → tactic rule | vals r := do
        when (r.ctxt.length ≠ vals.length) (fail "context assignment list is a different length to the rule's context. "),
        let rctxt := list.zip r.ctxt vals,
        let pf := specify_aux r.ctxt.length r.pf,
        let pf := specify_aux₂ rctxt pf, 
        infer_type pf, -- make sure it's valid
        of_prf r.id pf

    meta def lhs_pattern (r : rule) : tactic pattern := telescope.to_pattern r.ctxt r.lhs

    meta def to_mvars (r : rule) : tactic (rule × list expr) := do
        gs ← get_goals,
        res ← mk_mvar,
        set_goals [res],
        ms ← apply_core r.pf {instances := ff},
        res ← instantiate_mvars res,
        r ← rule.of_prf r.id res,
        set_goals gs,
        pure (r, prod.snd <$> ms)
    meta def instantiate_mvars (r : rule) : tactic rule := tactic.instantiate_mvars r.pf >>= rule.of_prf r.id

    meta def get_local_const_dependencies (r : rule) : tactic (list expr) := do
        pf ← tactic.instantiate_mvars r.pf,
        let lcs :=  list_local_consts pf,
        pure lcs

    meta def is_local_hypothesis (r : rule) : tactic bool := do 
        lcds ← r.get_local_const_dependencies >>= list.mmap infer_type >>= list.mmap is_prop ,
    -- [HACK] I am assuming that there are no subtypings and so on which is probably a bad assumption.
        pure $ list.foldl bor ff lcds

    meta def count_metas (r : rule) : tactic nat := do
        lhs ← tactic.instantiate_mvars r.lhs,
        pure $ table.size $ expr.fold r.lhs (table.empty) (λ e _ t, if expr.is_mvar e then table.insert e t else t)


    meta def is_commuter (r : rule) : tactic bool :=
    match r.lhs, r.rhs with
    | (expr.app (expr.app f1 (n1)) (m1))
    , (expr.app (expr.app f2 (n2)) (m2)) := (do
        tactic.is_def_eq f1 f2,
        tactic.is_def_eq n1 m2,
        tactic.is_def_eq n2 m1,
        pure tt) <|> pure ff
    |_, _ := pure ff 
    end

    meta def is_def_eq (r₁ r₂ : rule) : tactic bool :=
        tactic.is_success $ (do 
        tactic.is_def_eq r₁.lhs r₂.lhs,
        tactic.is_def_eq r₁.rhs r₂.rhs
        )

end rule