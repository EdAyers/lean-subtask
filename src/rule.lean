import .util
open tactic
meta structure hyp :=
(n : name) (bi : binder_info) (type : expr)
meta def telescope := list hyp
meta structure rule := -- relation is always `=` for now.
(ctxt : telescope) -- arguments, local context.
(lhs : expr) 
(rhs : expr)
(pf : expr) -- the proof expression of the given rule. Note that sometimes 

namespace rule
    -- potential [BUG] what if the same rule exists with the parameters in a different order? this is just annoying so I will ignore for now.
    meta instance has_lt : has_lt rule := ⟨λ r1 r2, (r1.lhs,r1.rhs) < (r2.lhs,r2.rhs)⟩
    meta instance has_decidable_lt : decidable_rel ((<) : rule → rule → Prop)
        := by apply_instance

    meta instance : has_to_string rule := ⟨λ r, (to_string r.lhs) ++ " = " ++ (to_string r.rhs)⟩
    meta instance : has_to_tactic_format rule := ⟨λ r, infer_type r.pf >>= whnf >>= tactic_format_expr⟩

    meta def as_pis : expr → (telescope × expr)
    | (expr.pi n bi y b) := let ⟨ys,b⟩ := as_pis b in ⟨⟨n,bi,y⟩::ys,b⟩
    | x := ⟨[],x⟩

    meta def of_prf : expr → tactic rule := λ pf, do
        t ← infer_type pf >>= whnf,
        ⟨ctxt,`(%%lhs = %%rhs)⟩ ← pure $ as_pis t,
        pure {ctxt := ctxt, lhs := lhs, rhs := rhs, pf := pf}

    meta def equality_type (r : rule) : tactic expr := to_expr ```(%%r.lhs = %%r.rhs)

    meta def flip (r : rule) : tactic rule := do
        p ← to_expr ```(%%r.rhs = %%r.lhs),
        let type := expr.pis (hyp.type <$> r.ctxt) p, 
        pf ← tactic.fabricate type (do intros, applyc `eq.symm, apply r.pf, pure ()),
        pure {ctxt := r.ctxt, lhs := r.rhs, rhs := r.lhs, pf := pf}

    meta def add_simp_lemma : simp_lemmas → rule → tactic simp_lemmas := λ sl r, simp_lemmas.add sl r.pf


    meta def head_rewrite : rule → expr → tactic rule := λ r lhs, do
        T ← tactic.infer_type lhs,
        rhs ← tactic.mk_meta_var T,
        target ← tactic.mk_app `eq [lhs,rhs],
        pf ← tactic.fabricate target ( do
                lhspp ← pp lhs,
                rulepp ← pp r,
                --trace $ ("rewriting " : format) ++ lhspp ++" with " ++ rulepp,
                tactic.apply r.pf,
                --trace_state,
                --result >>= trace,
                pure ()
            ), -- if new goals are created then tactic.fabricate will throw.
        of_prf pf

    /--`match_rhs e r` matches `e` with `r.rhs` (ie, metavariables in r.rhs can be assigned) and returns the result. New goals might be present. -/
    meta def match_rhs : expr → rule → tactic unit
    |e r := do
        notimpl

    meta def is_wildcard : rule → bool := λ r, expr.is_var r.lhs || expr.is_mvar r.lhs

end rule