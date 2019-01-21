import .data
namespace robot
open tactic
meta def M : Type → Type := state_t state conv
meta instance M.monad : monad M := state_t.monad
meta instance M.monad_state : monad_state state M := state_t.monad_state
meta instance M.alternative : alternative M := state_t.alternative
meta instance M.of_tactic {α} : has_coe (tactic α) (M α)  := ⟨state_t.lift⟩
meta instance M.of_conv {α} : has_coe (conv α) (M α) := ⟨state_t.lift⟩
meta def get_ce : M expr := state_t.lift (conv.lhs >>= instantiate_mvars)
meta def get_rhs : M expr := state_t.lift (conv.rhs >>= instantiate_mvars)
meta def get_lookahead : M (list rule) := state.lookahead <$> get
meta def get_path : M _ := state.path <$> get
meta def get_rule_table : M rule_table := state.rt <$> get
meta def M.hypothetically {α} : M α → M (option α) := λ tac, ⟨λ s, do
    o ← tactic.hypothetically $ state_t.run tac s,
    pure $ (option.map prod.fst o, s)
⟩
meta def add_rule : rule → M unit := λ r, do
    s ← get,
    rt ← s.rt.insert r,
    put $ { rt := rt, ..s}
meta def repeat : M unit → M unit := λ t, t *> (repeat t <|> pure ())

/--Perform the conversion tactic and then update path and lookahead. -/
meta def run_conv : conv unit → M unit := λ c, do
    ce ← get_ce,
    c,
    ce' ← get_ce,
    state ← get,
    lookahead ← rule_table.rewrites ce' state.rt,
    let path := ce :: state.path,
    -- state_t.lift $ tactic.target >>= tactic.trace,
    put { state with 
      lookahead := lookahead, 
      path := path 
    }

meta def policy := list action → M (list action)

end robot