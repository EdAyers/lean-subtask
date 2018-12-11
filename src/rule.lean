import .data .util
open tactic

meta structure rule := -- relation is always `=` for now.
(telescope : list expr) -- arguments.
(lhs : expr) 
(rhs : expr)
(pf : expr)

namespace rule
    -- potential [BUG] what if the same rule exists with the parameters in a different order? this is just annoying so I will ignore for now.
    meta instance : has_lt rule := ⟨λ r1 r2, (r1.lhs,r1.rhs) < (r2.lhs,r2.rhs)⟩
    meta instance rule.has_decidable_lt : decidable_rel ((<) : rule → rule → Prop)
    := by apply_instance
    meta instance : has_to_string rule := ⟨λ r, (to_string r.lhs) ++ " = " ++ (to_string r.rhs)⟩
    meta instance : has_to_tactic_format rule := ⟨λ r, infer_type r.pf >>= tactic_format_expr⟩

    meta def as_pis: expr → (list expr × expr)
    | (expr.pi _ _ y b) := let ⟨ys,b⟩ := as_pis b in ⟨y::ys,b⟩
    | x := ⟨[],x⟩

    meta def of_prf : expr → tactic rule := λ pf, do
        t ← infer_type pf,
        ⟨telescope,`(%%lhs = %%rhs)⟩ ← pure $ as_pis t,
        pure {telescope := telescope, lhs := lhs, rhs := rhs, pf := pf}

    meta def equality_type (r : rule) : tactic expr := to_expr ```(%%r.lhs = %%r.rhs)

    meta def flip (r : rule) : tactic rule := do
        p ← to_expr ```(%%r.rhs = %%r.lhs),
        let type := expr.pis (r.telescope) p, 
        pf ← tactic.fabricate type (do intros, applyc `eq.symm, apply r.pf, pure ()),
        pure {telescope := r.telescope, lhs := r.rhs, rhs := r.lhs, pf := pf}

    meta def add_simp_lemma : simp_lemmas → rule → tactic simp_lemmas := λ sl r, simp_lemmas.add sl r.pf

end rule