open tactic

/-- `fabricate type s` uses tactic `s` to make an instance of `type`. It saves and restores the goals of the tactic. -/
meta def tactic.fabricate (type : expr) (strat : tactic unit) : tactic expr := do
    new_g ← mk_meta_var type,
    gs ← get_goals,
    set_goals [new_g],
    strat,
    n ← num_goals,
    when (n≠0) (fail "fabrication failed: there are unsolved goals."),
    set_goals gs,
    instantiate_mvars new_g