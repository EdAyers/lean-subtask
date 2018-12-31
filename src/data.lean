
import .table .rule .rule_table
namespace robot
section equiv
    universes u
    variables {α : Type u} [has_lt α]
    def equiv : α → α → Prop := λ x y, ¬(x<y) ∧ ¬(y < x)
    instance dec_equiv [decidable_rel ((<) : α → α → Prop)] : decidable_rel (equiv : α → α → Prop) := λ x y, dite (x < y) (λ h, is_false (λ ⟨g,_⟩, absurd h g)) (λ h, dite (y < x) (λ h₂, is_false (λ ⟨_,g⟩, absurd h₂ g)) (λ h₂, is_true ⟨h,h₂⟩))
end equiv

meta inductive task : Type
|CreateAll : expr → task
|Create : expr → task
open task
meta def task.code : task → ℕ
|(task.Create _) := 0
|(task.CreateAll _) := 1
meta def task.lt : task → task → bool
|(task.Create e₁) (task.Create e₂) := e₁ < e₂
|(task.CreateAll e₁) (task.CreateAll e₂) := e₁ < e₂
|x y := task.code x < task.code y
meta instance task.has_lt : has_lt task := ⟨λ x y, task.lt x y⟩
meta instance task.decidable_lt: decidable_rel ((<) : task → task → Prop) := by apply_instance

meta inductive strategy : Type
|Use : rule → strategy
|ReduceDistance : expr → expr → strategy
open strategy
meta def strategy.code : strategy → ℕ
|(Use _) := 0
|(ReduceDistance _ _) := 1
meta def strategy.lt : strategy → strategy → bool
|(Use r₁) (Use r₂) := r₁ < r₂
|(ReduceDistance a b) (ReduceDistance a' b') := (a,b) < (a',b')
|s₁ s₂ := s₁.code < s₂.code
meta instance strategy.has_lt : has_lt strategy := ⟨λ x y, strategy.lt x y⟩
meta instance strategy.decidable_lt : decidable_rel ((<) : strategy → strategy → Prop) := by apply_instance

-- meta inductive V
-- |Task : task → V
-- |Strategy : strategy → V
-- meta def V.code : V → ℕ
-- |(V.Task _) := 0
-- |(V.Strategy _) := 1
-- meta def V.lt : V → V → bool
-- |(V.Task t₁) (V.Task t₂) := t₁ < t₂
-- |(V.Strategy s₁) (V.Strategy s₂) := s₁ < s₂
-- |x y := V.code x < V.code y
-- meta instance V.has_lt : has_lt V := ⟨λ x y, V.lt x y⟩
-- meta structure E := 
-- (strategies : list strategy)
-- (tasks : list task)
-- meta def E.lt : E → E → bool
-- |⟨s₁,t₁⟩ ⟨s₂,t₂⟩ := (s₁ < s₂) || (¬(s₁ > s₂) && (t₁ < t₂))
-- meta instance E.has_lt : has_lt E := ⟨λ x y, E.lt x y⟩
-- meta def E.children : E → list V
-- |⟨ss,ts⟩ := (V.Task <$> ts) ++ (V.Strategy <$> ss)
-- meta def E.filter (p : V → bool) : E → E
-- |⟨ss,ts⟩ := ⟨ss.filter (λ s, p $ V.Strategy $ s), ts.filter (λ t, p $ V.Task $ t)⟩
-- meta instance : edge_col V E := ⟨E.children, E.filter⟩
-- meta def G := digraph V E
-- meta instance : has_mem V G := digraph.has_mem

meta structure config := 
(rule_table     : rule_table)
-- meta structure state :=
-- (ce             : expr)
-- (lookahead      : list rule)
-- (visited        : table expr)       -- terms that have already been visited.
-- (graph          : G)                -- the task-graph.
-- (front          : table strategy)   -- a list of strategies to choose from.
-- (acheived_tasks : table task)       -- a set of tasks that have recently been achieved and which should not be unachieved until their parent is achieved.
-- (config         : config)           -- some data that should remain fixed for the duration of the tactic. [NOTE] maybe put in a reader monad?

meta inductive stack_entry : Type
|strategy (current : strategy)  : stack_entry
|task  (current : task) (siblings : list task) (achieved : list task) : stack_entry
meta instance stack_entry.of_strat : has_coe (strategy) (stack_entry) := ⟨stack_entry.strategy⟩
meta def stack := list stack_entry
meta structure state :=
(lookahead : list rule)
(visited : table expr)
-- (stack : stack)
(config : config)


-- [TODO] proof object.

/-- The robot monad. -/
meta def M : Type → Type := state_t state conv
meta instance : monad M := state_t.monad
meta instance : monad_state state M := state_t.monad_state
meta instance : alternative M := state_t.alternative
meta instance of_tactic {α} : has_coe (tactic α) (M α) := ⟨state_t.lift⟩
meta instance of_conv {α} : has_coe (conv α) (M α) := ⟨state_t.lift⟩
meta def map_state  (f : state → state) : M unit := (f <$> get) >>= put
meta def get_rule_table : M rule_table := config.rule_table <$> state.config <$> get
meta def get_ce : M expr := state_t.lift conv.lhs
meta def get_visited : M $ table $ expr := state.visited <$> get
meta def get_lookahead : M (list rule) := state.lookahead <$> get
meta def M.hypothetically {α} : M α → M (option α) := λ tac, ⟨λ s, do
    o ← tactic.hypothetically (state_t.run tac s) ,
    match o with
    |none := pure (none, s)
    |(some (a,s')) := pure (some a,s)
    end
⟩
-- meta def get_stack : M stack := state.stack <$> get
meta def stack.mfold_achieved {T} [monad T] {α} (f : α → task → T α) : α → stack → T α
| a [] := pure a
| a ((stack_entry.strategy _)::t) := stack.mfold_achieved a t
| a ((stack_entry.task current siblings achieved)::t) := achieved.mfoldl f a >>= λ a, stack.mfold_achieved a t
-- meta def mfold_achieved {α} (f : α → task → M α) : α → M α | a := get_stack >>= stack.mfold_achieved f a

meta def refinement := list task × list strategy

meta def task.test : task → M bool
|(task.Create e) := do ce ← get_ce, pure $ expr.occurs e ce
|_ := notimpl
meta def strategy.of_rule : rule → M strategy := λ r, pure $ strategy.Use $ r

/-- Do In One Move. Check the lookahead table and see if any of the entries in there cause the task to be achieved. -/
meta def task.diom : task → M (list strategy) := λ t, do
    ce ← get_ce,
    lookahead ← get_lookahead,
    winners : list rule ← list.mcollect (λ r, do 
        let rhs := rule.rhs r,
        let pf := rule.pf r,
        x : option rule ← M.hypothetically (do
                conv.update_lhs rhs pf, 
                result ← task.test t, 
                if result then pure r else tactic.fail ""
        ),
        match x with
        |(some r) := pure r
        |none := (tactic.fail "")
        end
    ) lookahead,
    winners.mmap (strategy.of_rule)
open ez

meta def try_dioms : task → M refinement | t := do dioms ← task.diom t, if ¬ dioms.empty then pure ([],dioms) else failure

meta def task.refine (t : task) : M refinement :=
try_dioms t <|>
match t with
|(task.Create e) := do
    ce ← get_ce,
    rt ← get_rule_table,
    submatches ← rt.submatch e,
    strats ← list.mmap strategy.of_rule $ list.filter (λ r, ¬ rule.is_wildcard r) $ submatches,
    pure $ ([],strats)
|(task.CreateAll a) := do
    ce ← get_ce,
    scs ← zipper.lowest_uncommon_subterms ce $ zipper.zip a,
    if scs.length = 0 then notimpl else do
    let scs := task.Create <$> zipper.current <$> scs,
    pure $ (scs, [])
end

meta def strategy.execute : strategy → conv unit
|(strategy.ReduceDistance a b) := notimpl
|(strategy.Use r)              := rule.to_conv r
open tactic
meta def strategy.refine : strategy → M refinement
|(strategy.ReduceDistance a b) := notimpl
|(strategy.Use r)              := do
    ce ← get_ce,
    ⟨r,ms⟩ ← rule.to_mvars r,
    subs : list zipper ← zipper.minimal_monotone (λ lz,
        if lz.is_mvar || lz.is_constant then failure else do
        ⟨r,ms⟩ ← rule.to_mvars r,
        l : list unit ← zipper.maximal_monotone (λ rz, (hypothetically' $ unify lz.current rz.current)) $ zipper.zip $ ce,
        if l.empty then pure lz else failure
    ) $ zipper.zip $ r.lhs,
    let subs := subs.map (λ z, task.Create $ z.current),
    pure ⟨subs, []⟩

meta def stack.append_subtasks : list task → stack → list (task × stack) 
|tasks stack := tasks.map_with_rest (λ c rest, (c,(stack_entry.task c rest []) :: stack)) 
meta def stack.append_substrats : list strategy → stack → list (strategy × stack)
|ss stack := ss.map(λ s, (s,stack_entry.strategy s :: stack))
meta def stack.has_task : stack → task → bool
|s t  := list.any s (λ x, match x with |(stack_entry.task x _ _) := equiv t x | _ := ff end)
meta def stack.has_strat : stack → strategy → bool
|s t  := list.any s (λ x, match x with |(stack_entry.strategy x) := equiv t x | _ := ff end)

meta def explore_tasks : list (task × stack) → list (strategy × stack) → M (list (strategy × stack))
|[] acc := pure acc
|((t,st) :: rest) acc := do
    state ← get,
    is_achieved ← task.test t,
    if is_achieved then explore_tasks rest acc else do
    (subtasks, substrats) ← task.refine t,
    let subtasks := st.append_subtasks $ subtasks.filter (λ t, stack.has_task st t), -- filter out subtasks that are already on the stack.
    let substrats := st.append_substrats $ substrats.filter (λ s, stack.has_strat st s),
    let acc := substrats ++ acc,
    explore_tasks (subtasks ++ rest) acc

meta def explore_task : (task × stack) → M (list (strategy × stack))
|ts := explore_tasks [ts] []

meta def explore_strategy : (strategy × stack) → M (list (strategy × stack))
| ⟨s,stack⟩ := do
    (subtasks, substrats) ← strategy.refine s,
    explore_tasks (stack.append_subtasks subtasks) (stack.append_substrats substrats)

meta def execute_strategy : strategy → stack → M unit
|s stack := do
    state ← get,
    ce ← get_ce,
    state_t.lift $ strategy.execute s,
    ce' ← get_ce,
    when (ce = ce') (tactic.fail "strategy did not change the goal."),
    stack.mfold_achieved (λ _ acheived, do 
        r ← acheived.test, 
        when (r) (tactic.fail "stategy caused a previously achieved task to fail.")
    ) (),
    lookahead ← rule_table.rewrites ce' state.config.rule_table,
    let visited := state.visited.insert ce,
    put {
        state with
         lookahead := lookahead
        , visited := visited
    }

meta def ascend : stack → M (list (strategy × stack))
|[] := pure []
|stack@((stack_entry.strategy s)::t) :=
    (execute_strategy s stack *> ascend t) 
    <|> (explore_strategy (s,stack))
|stack@((stack_entry.task current siblings achieved) :: tail) := do
    is_achieved ← task.test current,
    if (is_achieved) then
        let achieved := current::achieved in
        match siblings with
        |[] := ascend tail
        |_ :=
            let front := siblings.map_with_rest (λ subtask siblings, (subtask, (stack_entry.task subtask siblings achieved)::tail)) in
            explore_tasks front [] 
        end
    else 
        explore_task (current, stack)

meta def execute : (strategy × stack) → M (list (strategy × stack))
| ⟨strat, t⟩ := ascend t



end robot