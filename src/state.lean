import .task .graph .rule_table

namespace robot

open tactic

/- Methods:

## `execute_Strategy`
we are given a strategy from `front`.
delete sibling strategies that dont have another parent from front.
If the strategy can be done in one move, do it and continue from `do_move` method
Otherwise, refine the strategy, producing a set of tasks and explore the whole task subtree and run `advance_front`.

## `do_move`
We are given a rule and a vertex that the rule should achieve. A __valid__ rule has the following properties:
- doesn't undo a member of `acheived_tasks`
- the rule doesn't fail
- the rule doesn't take us to a previously visited term. [NOTE] this constraint might be relaxed.
- the rule must achieve the current strategy or task.
if one of these conditions fails then the entire tactic fails.
Once the rule has been executed. Do the following:
ce ← rule.rhs
recompute the lookahead
get the list of strategies on the front that the move completes and make an empty list of tasks L.
look at all of the parents of these strategies
- if the parent is a task that is now achieved; add its parent to the front

- if the parent is a task that is not acheived, push it to L. push the given 
- if the parent is a strategy;



# Hmm

I think this is still too complicated. What is the most simple version of this idea?
What are the essential properties of the system?

- To have stacks of subtasks, once a subtask is completed we look at its parent.
- to be able to backtrack while still holding on to the lessons learnt from the backtracking
- be extensible - one can add their own subtasks.
- 
 -/

-- meta def compute_lookahead : expr → robot (list rule) := λ e, do
--     rt ← robot.rule_table,
--     rule_table.rewrites e rt

meta def propagate_tasks : list task → M unit
|[] := pure ()
|(t::ts) := do
    ce ← get_ce,
    passes ← task.test t ce,
    if passes then propagate_tasks ts else do -- [TODO] remove the given task from the graph?
    let v := V.Task t,
    e ← task.refine t,
    g ← get_graph,
    let e := e.filter (λ v, (v ∉ g) || ¬(g.has_loop v)),
    let new_tasks := e.tasks,
    let new_strategies := e.strategies,
    map_graph (digraph.set v e),
    map_front (table.insert_many new_strategies),
    propagate_tasks (ts ++ new_tasks)

meta def back_up_stack : list V → M unit
|[] := notimpl
|((v@(V.Task t))::vs) := notimpl
|((v@(V.Strategy str))::vs) := do
    s ← get,
    r ← strategy.execute str s.ce,
    r ← rule.head_rewrite r s.ce,
    when (state.visited.contains r.rhs) (fail "already visited node."),
    let ce := r.rhs,
    -- check that executing this strategy doesn't cause any achieved tasks to fail.
    s.acheived_tasks.mfold (λ t acc, do
        passes ← task.test t ce,
        when (¬passes) (fail "makes a previously passing test fail")
    ) (),
    



    -- the task v has been acheived. see if any of the parents can be achieved.
    
    /- Ok, so there might be more than one parent. The parents each correspond to a different reason to perform the move. -/



meta def execute_strategy (str : strategy) : M unit := do
    s ← get,
    when (bnot $ s.front.contains str) (fail "given strategy is not in strategy front."),
    r ← strategy.execute str s.ce, -- [TODO] if the strategy fails then refine it.
    r ← rule.head_rewrite r s.ce, -- make sure the returned rule works
    when (s.visited.contains r.rhs) (tactic.fail "already visited this node."),
    let ce := r.rhs,
    -- if any previously succeeding tasks fail now, then this strategy fails.

    let visited := s.visited.insert s.ce,
    lookahead ← s.config.rule_table.rewrites ce,
    -- [TODO] recalculate the front, graph
    put { s with
        ce := ce,
        lookahead := lookahead,
        visited   := visited,
    }



meta def apply_rule (r : rule) : M state := do
    r ← rule.head_rewrite r s.ce,


end robot