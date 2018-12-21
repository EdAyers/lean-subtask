
import .table .graph .rule .rule_table
namespace robot

meta inductive task 
|Create : expr → task
|ReduceDistance : expr → expr → task
meta def task.code : task → ℕ
|(task.Create _) := 0
|(task.ReduceDistance _ _) := 1
meta def task.lt : task → task → bool
|(task.Create e₁) (task.Create e₂) := e₁ < e₂
|(task.ReduceDistance a b) (task.ReduceDistance a' b') := (a,b) < (a',b')
|x y := task.code x < task.code y
meta instance task.has_lt : has_lt task := ⟨λ x y, task.lt x y⟩
meta instance task.decidable_lt: decidable_rel ((<) : task → task → Prop) := by apply_instance

meta inductive strategy
|Use : rule → strategy
meta def strategy.lt : strategy → strategy → bool
|(strategy.Use r₁) (strategy.Use r₂) := r₁ < r₂
meta instance strategy.has_lt : has_lt strategy := ⟨λ x y, strategy.lt x y⟩
meta instance strategy.decidable_lt : decidable_rel ((<) : strategy → strategy → Prop) := by apply_instance


meta inductive V
|Task : task → V
|Strategy : strategy → V
meta def V.code : V → ℕ
|(V.Task _) := 0
|(V.Strategy _) := 1
meta def V.lt : V → V → bool
|(V.Task t₁) (V.Task t₂) := t₁ < t₂
|(V.Strategy s₁) (V.Strategy s₂) := s₁ < s₂
|x y := V.code x < V.code y
meta instance V.has_lt : has_lt V := ⟨λ x y, V.lt x y⟩
meta structure E := 
(strategies : list strategy)
(tasks : list task)
meta def E.lt : E → E → bool
|⟨s₁,t₁⟩ ⟨s₂,t₂⟩ := (s₁ < s₂) || (¬(s₁ > s₂) && (t₁ < t₂))
meta instance E.has_lt : has_lt E := ⟨λ x y, E.lt x y⟩
meta def E.children : E → list V
|⟨ss,ts⟩ := (V.Task <$> ts) ++ (V.Strategy <$> ss)
meta def E.filter (p : V → bool) : E → E
|⟨ss,ts⟩ := ⟨ss.filter (λ s, p $ V.Strategy $ s), ts.filter (λ t, p $ V.Task $ t)⟩
meta instance : edge_col V E := ⟨E.children, E.filter⟩
meta def G := digraph V E
meta instance : has_mem V G := digraph.has_mem

meta structure config := 
(rule_table     : rule_table)
meta structure state :=
(ce             : expr)
(lookahead      : list rule)
(visited        : table expr)       -- terms that have already been visited.
(graph          : G)                -- the task-graph.
(front          : table strategy)   -- a list of strategies to choose from.
(acheived_tasks : table task)       -- a set of tasks that have recently been achieved and which should not be unachieved until their parent is achieved.
(config         : config)           -- some data that should remain fixed for the duration of the tactic. [NOTE] maybe put in a reader monad?
-- [TODO] proof object.

/-- The robot monad. -/
meta def M : Type → Type := state_t state tactic
meta instance : monad M := state_t.monad
meta instance : monad_state state M := state_t.monad_state
meta instance {α} : has_coe (tactic α) (M α) := ⟨state_t.lift⟩
meta def map_state  (f : state → state) : M unit := (f <$> get) >>= put
meta def get_rule_table : M rule_table := config.rule_table <$> state.config <$> get
meta def get_ce : M expr := state.ce <$> get
meta def get_visited : M $ table $ expr := state.visited <$> get
meta def get_front : M $ table $ strategy := state.front <$> get
meta def get_graph : M $ G := state.graph <$> get
meta def get_parents : V → M (table V) := λ v, digraph.get_parents v <$> get_graph
meta def put_front : table strategy → M unit := λ front, map_state (λ s, {s with front := front})
meta def put_graph (g : G) : M $ unit := map_state (λ s, {s with graph := g})
meta def map_graph : (G → G) → M unit := λ f, (f <$> get_graph) >>= put_graph
meta def map_front : (table strategy → table strategy) → M unit := λ f, (f <$> get_front) >>= put_front
meta def contains_task : task → M bool := λ t, do g ← get_graph, pure (V.Task t ∈ g)
meta def contains_strategy : strategy → M bool := λ s, do g ← get_graph, pure (V.Strategy s ∈ g)
meta def has_loop : V → M bool := λ v, do g ← get_graph, pure (digraph.has_loop v g)
end robot