import .util
open tactic
@[derive decidable_eq]
meta structure hyp :=
(n : name) (bi : binder_info) (type : expr)
meta def telescope := list hyp
meta def telescope.to_pis : expr → telescope → expr := list.foldl (λ e ⟨n,b,y⟩, expr.pi n b y e)
private meta def telescope.of_pis_aux : telescope → expr → telescope × expr
| acc (expr.pi n bi y b) := telescope.of_pis_aux (⟨n,bi,y⟩::acc) b
| acc x := ⟨acc,x⟩
meta def telescope.of_pis : expr → (telescope × expr) := telescope.of_pis_aux []

@[derive decidable_eq]
meta structure rule := -- relation is always `=` for now.
(ctxt : telescope) -- arguments, local context. [IDEA] instead; do this by just having a tactic that creates the right environment?
(lhs  : expr) 
(rhs  : expr)
(type : expr)
(pf   : expr) -- the proof expression of the given rule. Note that sometimes 

namespace rule
    meta instance has_lt : has_lt rule := ⟨λ r1 r2, (r1.lhs,r1.rhs) < (r2.lhs,r2.rhs)⟩
    meta instance has_decidable_lt 
        : decidable_rel ((<) : rule → rule → Prop)
        := by apply_instance

    meta instance : has_to_string rule := ⟨λ r, (to_string r.lhs) ++ " = " ++ (to_string r.rhs)⟩
    meta instance : has_to_tactic_format rule := ⟨λ r, infer_type r.pf >>= whnf >>= tactic_format_expr⟩

    meta def of_prf : expr → tactic rule := λ pf, do
        t ← infer_type pf >>= whnf,
        ⟨ctxt,`(%%lhs = %%rhs)⟩ ← pure $ telescope.of_pis t,
        pure {ctxt := ctxt, lhs := lhs, rhs := rhs, pf := pf, type := t}

    meta def flip (r : rule) : tactic rule := do
        let P := r.ctxt.foldl (λ e ⟨n,b,y⟩, expr.pi n b (to_pexpr y) e) $ ```(%%r.rhs = %%r.lhs),
        T ← to_expr $ P,
        pf ← tactic.fabricate (some T) (do
            tactic.intros,
            tactic.applyc `eq.symm,
            tactic.apply r.pf,
            skip
        ),
        pure { ctxt := r.ctxt
             , lhs  := r.rhs
             , rhs  := r.lhs
             , type := r.type
             , pf   := pf
             }

    -- meta def add_simp_lemma : simp_lemmas → rule → tactic simp_lemmas := λ sl r, simp_lemmas.add sl r.pf
    meta def is_wf (r : rule) : tactic bool := do r' ← of_prf $ pf $ r, pure $ r = r'
    meta def of_name (n : name) : tactic rule := resolve_name n >>= pure ∘ pexpr.mk_explicit >>= to_expr >>= rule.of_prf
    meta def head_rewrite : rule → expr → tactic rule := λ r lhs, do
        T ← tactic.infer_type lhs,
        rhs ← tactic.mk_meta_var T,
        target ← tactic.mk_app `eq [lhs,rhs],
        pf ← tactic.fabricate target ( do
                lhspp ← pp lhs,
                rulepp ← pp r,
                --trace $ ("rewriting " : format) ++ lhspp ++" with " ++ rulepp,
                --trace_state,
                tactic.apply r.pf,
                all_goals $ try apply_instance, -- clean up typeclass instances.
                -- result >>= trace,
                pure ()
            ),  -- if new goals are created then tactic.fabricate will throw.
        of_prf pf

    /--`match_rhs e r` matches `e` with `r.rhs` (ie, metavariables in r.rhs can be assigned) and returns the result. New goals might be present. -/
    -- meta def match_rhs : expr → rule → tactic unit
    -- |e r := do
    --     notimpl

    meta def is_wildcard : rule → bool := λ r, expr.is_var r.lhs || expr.is_mvar r.lhs
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
        of_prf pf

    meta def to_conv (r : rule) : conv unit := do
        apply r.pf,
        try $ all_goals $ apply_instance <|> assumption,
        pure ()


end rule