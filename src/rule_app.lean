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
(r : rule)
(lhs : expr)
(rhs : expr)
(adr : address)
(pf : expr)

namespace rule_app

meta instance : has_to_tactic_format rule_app := 
⟨λ r, do
  plhs ← tactic.pp r.lhs,
  prhs ← tactic.pp r.rhs,
  pure $ plhs ++ " = " ++ prhs
 ⟩

/--Take the given rule, replace all of the arguments with metavariables and return a rule_app and a list of the metavariables. -/
meta def of_rule (r : rule) : tactic (rule_app × list expr) := do
    gs ← get_goals,
    pf ← mk_mvar,
    set_goals [pf],
    ms ← apply_core r.pf {instances := ff},
    pf ← instantiate_mvars pf,
    ms ← pure $ prod.snd <$> ms,
    `(%%lhs = %%rhs) ← infer_type pf >>= whnf,
    ra ← pure $ {rule_app . r := r, lhs := lhs, rhs := rhs, adr := [], pf := pf},
    set_goals gs,
    pure (ra, ms)

meta def is_def_eq (r₁ r₂ : rule_app) : tactic bool :=
  tactic.is_success $ (do
    tactic.is_def_eq r₁.lhs r₂.lhs,
    tactic.is_def_eq r₁.rhs r₂.rhs
  )




/--Returns true if the LHS zipped to the rule use is a metavariable. -/
meta def lhsz_is_meta : rule_app → bool := λ ra,
  ff <| (expr.is_mvar <$> zipper.current <$> zipper.down_address ra.adr ra.lhs)

meta instance has_lt : has_lt rule_app := ⟨λ r₁ r₂, (r₁.lhs,r₁.rhs) < (r₂.lhs,r₂.rhs) ⟩

meta def instantiate_mvars : rule_app → tactic rule_app
|{r:=r,lhs:=lhs,rhs:=rhs,adr:=adr,pf:=pf} := do
  lhs ← tactic.instantiate_mvars lhs,
  rhs ← tactic.instantiate_mvars rhs,
  pf ← tactic.instantiate_mvars pf,
  pure $ {r:=r,lhs:=lhs,rhs:=rhs,adr:=adr,pf:=pf} 

meta def head_rewrite : rule_app → zipper → tactic rule_app := λ r lhs, do
  T ← tactic.infer_type lhs.current,
  rhs ← tactic.mk_meta_var T,
  target ← tactic.mk_app `eq [lhs.current,rhs],
  pf ← tactic.fabricate target (do
    tactic.apply_core r.pf,
    all_goals $ try (apply_instance <|> prop_assumption),
    pure ()
  ),
  (rhs',pf') ← zipper.apply_congr (rhs,pf) lhs,
  let adr := zipper.address lhs ++ r.adr, 
  let ra : rule_app := { r := r.r,  lhs:= lhs.unzip, rhs := rhs', adr := adr , pf := pf' },
  ra ← instantiate_mvars ra,
  pure ra

  -- meta def apply_rule : rule_app → zipper → tactic rule_app := λ r z, do
  --     r ← r.head_rewrite z.current,
  --     (rhs', pf') ← apply_congr (r.rhs,r.pf) z,
  --     --tactic.infer_type pf' >>= trace,
  --     --trace pf',
  --     r' ← rule.of_prf r.id pf',
  --     --trace "hello",
  --     pure r'

meta def head_rewrite_conv : rule_app → conv unit := λ r, do
  lhs ← conv.lhs >>= tactic.instantiate_mvars,
  transitivity,
  apply r.pf,
  try $ all_goals $ apply_instance <|> prop_assumption,
  gs ← tactic.get_goals,
  when (gs.length ≠ 1) (fail "failed to head rewrite. "),
  pure ()

/--Use the given rule application on the lhs of the target. Will look for congruences. -/
meta def rewrite_conv : rule_app → conv unit := λ r, do
        lhs ← conv.lhs >>= tactic.instantiate_mvars,
        sub ← tactic.instantiate_mvars r.lhs,
        l ← ez.zipper.find_occurences (zipper.zip lhs) r.lhs,
        -- trace_m "rewrite_conv: " $ (lhs,r, l),
        (z::rest) ← pure l,
        r ← head_rewrite r z,
        transitivity,
        apply r.pf,
        --trace_state, trace r,
        try $ all_goals $ apply_instance <|> prop_assumption,
        pure ()

meta def is_local_hypothesis (r : rule_app) : tactic bool := r.r.is_local_hypothesis
meta def is_commuter (r : rule_app) : tactic bool := r.r.is_commuter

meta def count_metas (r : rule_app) : tactic nat := do
        lhs ← tactic.instantiate_mvars r.lhs,
        pure $ table.size $ expr.fold r.lhs (table.empty) (λ e _ t, if expr.is_mvar e then table.insert e t else t)


end rule_app

end robot