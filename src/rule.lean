import .data
open tactic
namespace rule
    meta def of_prf : expr → tactic rule
    |prf := do
        e@`(%%lhs = %%rhs) ← infer_type prf,
        pure {e := e, prf := pure prf}

    meta def split : rule → tactic (expr × expr)
    | ⟨`(%%lhs = %%rhs),_⟩ := return (lhs,rhs)
    | _ := fail "target is not an equation" -- [TODo] support 'iff' later.
    meta def lhs (r : rule) : tactic expr := prod.fst <$> split r
    meta def rhs (r : rule) : tactic expr := prod.snd <$> split r

    /--Swap the LHS and the RHS of the rule. -/
    meta def flip : rule → tactic rule
    | ⟨_,prf⟩ := prf >>= mk_eq_symm >>= of_prf
end rule