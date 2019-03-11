/- Author: E.W.Ayers © 2019 -/
import .util .table
open tactic
/-- Member of a telescope.-/
@[derive decidable_eq]
meta structure hyp :=
(n : name) (bi : binder_info) (type : expr)
/-- A telescope keeps track of all of the names and types of the free variables in the context. -/
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
(id : name) -- a way of identifying the rule.
(ctxt : telescope) -- arguments, local context.
(lhs  : expr) 
(rhs  : expr)
(type : expr)
(pf   : expr) -- the proof expression of the given rule.
(was_flipped : option (name × expr)) -- [HACK] needed to make sure `rule.flip` doesn't keep applying `eq.symm`. 

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

    /-- Create a `rule` from a proof term and a name. -/
    meta def of_prf (id : name) : expr → tactic rule := λ pf, do
        t ← infer_type pf >>= whnf,
        -- trace t, 
        ⟨ctxt,`(%%lhs = %%rhs)⟩ ← pure $ telescope.of_pis t 
        | (do pft ← pp pf, ppt ← pp t, fail $ (to_fmt "rule.of_prf: supplied expression ") ++ pft ++ " : " ++ ppt ++ " is not an equality proof "),
        pure {id := id, ctxt := ctxt, lhs := lhs, rhs := rhs, pf := pf, type := t, was_flipped := none}

    /-- Swap the LHS and RHS. -/
    meta def flip (r : rule) : tactic rule := 
    match r.was_flipped with
    |none := do
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
             , was_flipped := some (r.id, r.pf)
             }
    |some pf := of_prf pf.1 pf.2
    end
    /-- Sanity check that the LHS, RHS actually correspond to what the proof says.-/
    meta def is_wf (r : rule) : tactic bool := do r' ← of_prf r.id $ pf $ r, pure $ r = r'
    /-- Take a name `n` and try to make a rule from the lemma at the name's declaration. -/
    meta def of_name (n : name) : tactic rule := resolve_name n >>= pure ∘ pexpr.mk_explicit >>= to_expr >>= rule.of_prf n

    /--Returns true when the left hand side is a variable or metavariable. -/
    meta def lhs_wildcard : rule → bool := λ r, expr.is_var r.lhs || expr.is_mvar r.lhs
    /--Returns true when the right hand side is a variable or metavariable. -/
    meta def rhs_wildcard : rule → bool := λ r, expr.is_var r.rhs || expr.is_mvar r.rhs
    
    -- private meta def specify_aux : nat → expr → expr
    -- |0 acc := acc
    -- |(n+1) acc := specify_aux n $ expr.app acc (expr.var n)
    -- private meta def specify_aux₂ : list (hyp × option expr) → expr → expr
    -- |[] e := e
    -- |(⟨⟨n,b,y⟩, some E⟩::rest) e := specify_aux₂ rest $ expr.instantiate_var e E
    -- |(⟨⟨n,b,y⟩, none⟩ :: rest) e := specify_aux₂ rest $ expr.lam n b y e
    -- meta def specify : list (option expr) → rule → tactic rule | vals r := do
    --     when (r.ctxt.length ≠ vals.length) (fail "context assignment list is a different length to the rule's context. "),
    --     let rctxt := list.zip r.ctxt vals,
    --     let pf := specify_aux r.ctxt.length r.pf,
    --     let pf := specify_aux₂ rctxt pf, 
    --     infer_type pf, -- make sure it's valid
    --     of_prf r.id pf

    meta def instantiate_mvars (r : rule) : tactic rule := tactic.instantiate_mvars r.pf >>= rule.of_prf r.id

    meta def get_local_const_dependencies (r : rule) : tactic (list expr) := do
        pf ← tactic.instantiate_mvars r.pf,
        let lcs :=  expr.list_local_consts pf,
        pure lcs

    meta def is_local_hypothesis (r : rule) : tactic bool := do 
        lcds ← r.get_local_const_dependencies >>= list.mmap infer_type >>= list.mmap is_prop ,
    -- [HACK] I am assuming that there are no subtypings and so on which is probably a bad assumption.
        pure $ list.foldl bor ff lcds

    meta def is_commuter (r : rule) : tactic bool :=
    match r.lhs, r.rhs with
    | (expr.app (expr.app f1 (expr.var n1)) (expr.var m1))
    , (expr.app (expr.app f2 (expr.var n2)) (expr.var m2)) :=
        pure $ f1 = f2 ∧ n1 = m2 ∧ n2 = m1
    |_, _ := pure ff 
    end

    meta def is_def_eq (r₁ r₂ : rule) : tactic bool :=
        tactic.is_success $ (do 
        tactic.is_def_eq r₁.lhs r₂.lhs,
        tactic.is_def_eq r₁.rhs r₂.rhs
        )

end rule