/- Author: E.W.Ayers © 2019 -/
import .util .table .expr_zipper
namespace robot
open tactic robot expr

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

meta def rule_rewrite : rule → zipper → tactic rule_app := λ r lhs, do
    T ← tactic.infer_type lhs.current,
    -- tactic.infer_type r.pf >>= tactic.trace_m "rule_rewrite: ",
    rhs ← tactic.mk_meta_var T,
    target ← tactic.mk_app `eq [lhs.current,rhs],
    pf ← tactic.fabricate target (do
        /- [FIXME] apply_core is the performance bottleneck.
           one idea to resolve this is to make a pattern for each rule and hope that `match_pattern` is faster. -/
        --timetac "apply_core" $
        /- [BUG] this fails when it shouldn't on matching eg `X (Y * Z)` -/
        tactic.apply_core r.pf {md := transparency.none, unify := tt, instances := ff},
        all_goals $ try $ apply_instance <|> prop_assumption,
        pure ()
    ),
    (rhs',pf') ← zipper.apply_congr (rhs,pf) lhs,
    let ra : rule_app :=
        { r := r
        , lhs := lhs.unzip
        , rhs := rhs'
        , adr := zipper.address lhs
        , pf := pf'
        },
    ra ← instantiate_mvars ra,
    pure ra



meta def head_rewrite : rule_app → zipper → tactic rule_app := λ r lhs, do
  T ← tactic.infer_type lhs.current,
  rhs ← tactic.mk_meta_var T,
  target ← tactic.mk_app `eq [lhs.current,rhs],
  pf ← tactic.fabricate target (do
    -- [FIXME] `unify` is the performance bottleneck.
    -- timetac "unify" $ 
    --tactic.unify r.lhs lhs.current transparency.none tt,
    -- timetac "apply_core" $
    tactic.apply_core r.pf {md := transparency.none, unify := tt, instances := ff},
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
        l ← zipper.find_occurences (zipper.zip lhs) r.lhs,
        (z::rest) ← pure l,
        r ← tactic.trace_fail $ head_rewrite r z,
        -- tactic.trace_m "rewrite_conv: " $ r,
        transitivity,
        apply r.pf,
        -- trace_state, trace r,
        try $ all_goals $ apply_instance <|> prop_assumption,
        pure ()

meta def is_local_hypothesis (r : rule_app) : tactic bool := r.r.is_local_hypothesis
meta def is_commuter (r : rule_app) : tactic bool := r.r.is_commuter

meta def count_metas (r : rule_app) : tactic nat := do
        lhs ← tactic.instantiate_mvars r.lhs,
        uns ← zipper.traverse_proper (λ t e, pure $ match (expr.as_mvar e.current) with |none := t |(some ⟨u,_,_⟩) := table.insert u t end) (table.empty) lhs,
        -- uns ← pure $ expr.mfold r.lhs (table.empty : table name) (λ e _ t, option.cases_on (expr.as_mvar e) t (λ ⟨u,_,_⟩, table.insert u t)),
        -- tactic.trace_m "count_metas: " $ (r,uns),
        pure $ table.size $ uns

meta def flip (ra : rule_app) : tactic rule_app := do
  rf ← rule.flip ra.r,
  pf ← mk_eq_symm ra.pf,
  pure {
    r := rf,
    rhs := ra.lhs,
    lhs := ra.rhs,
    adr := ra.adr,
    pf := pf
  }

end rule_app

end robot