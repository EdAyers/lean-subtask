open tactic

universes u v
variables {α : Type u} {β : Type v}

meta def notimpl : α := undefined_core "not implemented"

meta def new_goal : option expr → tactic expr
|none := mk_mvar
|(some e) := mk_meta_var e

/-- `fabricate type s` uses tactic `s` to make an instance of `type`. It saves and restores the goals of the tactic. -/
meta def tactic.fabricate (type : option expr) (strat : tactic unit) : tactic expr := do
    new_g ← new_goal type,
    gs ← get_goals,
    set_goals [new_g],
    strat,
    n ← num_goals,
    when (n≠0) (fail "fabrication failed: there are unsolved goals."),
    set_goals gs,
    instantiate_mvars new_g

meta def expr.binding_body_all : expr → option expr
|(expr.pi _ _ _ b) :=  some b
|(expr.lam _ _ _ b) := some b
|(expr.elet _ _ _ b) :=some b
|_ := none

def list.mcollect {T} [alternative T] (f : α → T β) : list α → T (list β)
|[] := pure []
|(h::t) := pure (λ fh rest, option.cases_on fh rest (λ fh,fh::rest)) 
            <*> (some <$> f h <|> pure none) 
            <*> list.mcollect t