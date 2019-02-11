import .util .table .zipper
namespace robot
open tactic robot ez

-- @[derive decidable_eq]
-- meta structure rule2 :=
-- (id : name)
-- (ctxt : telescope)
-- (lhs : expr)
-- (rhs : expr)
-- (type : expr)
-- (pf : expr)

@[derive decidable_eq]
meta structure rule_app :=
(rule : rule)
(lhs : zipper)
(rhs : zipper)
(pf : expr)

meta def head_rewrite : rule → zipper → tactic rule_app := λ r lhs, do
  T ← tactic.infer_type lhs.current,
  rhs ← tactic.mk_meta_var T,
  target ← tactic.mk_app `eq [lhs.current,rhs],
  pf ← tactic.fabricate target (do
    tactic.apply_core r.pf,
    all_goals $ try (apply_instance <|> prop_assumption),
    pure ()
  ),
  (rhs',pf') ← zipper.apply_congr (rhs,pf) lhs,
  pure $ { rule := r,  lhs := lhs, rhs := lhs.set_current rhs, pf := pf' }



end robot