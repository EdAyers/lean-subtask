
import .table .rule .rule_table
namespace robot
open tactic
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
namespace task
    meta def code : task → ℕ
    |(Create _) := 0
    |(CreateAll _) := 1
    meta def lt : task → task → bool
    |(Create e₁) (Create e₂) := e₁ < e₂
    |(CreateAll e₁) (CreateAll e₂) := e₁ < e₂
    |x y := code x < code y
    meta instance has_lt : has_lt task := ⟨λ x y, lt x y⟩
    meta instance decidable_lt : decidable_rel ((<) : task → task → Prop) := by apply_instance
    meta instance : has_to_tactic_format task := ⟨λ t, match t with
    |(Create x) := pure (λ x, "Create " ++ x) <*> tactic.pp x
    |(CreateAll x) := pure (λ x, "CreateAll " ++ x) <*> tactic.pp x
    end⟩
end task
meta inductive strategy : Type
|Use : rule → strategy
|ReduceDistance : expr → expr → strategy
open strategy
namespace strategy
    meta def code : strategy → ℕ
    |(Use _) := 0
    |(ReduceDistance _ _) := 1
    meta def lt : strategy → strategy → bool
    |(Use r₁) (Use r₂) := r₁ < r₂
    |(ReduceDistance a b) (ReduceDistance a' b') := (a,b) < (a',b')
    |s₁ s₂ := s₁.code < s₂.code
    meta instance has_lt : has_lt strategy := ⟨λ x y, lt x y⟩
    meta instance decidable_lt : decidable_rel ((<) : strategy → strategy → Prop) := by apply_instance
    meta instance : has_to_tactic_format robot.strategy := ⟨λ s, match s with
        | (Use x) := do x ← tactic.pp x, pure $ "Use " ++ x
        | (ReduceDistance x y) := pure (λ x y, "ReduceDistance " ++ x ++ " " ++ y) <*> tactic.pp x <*> tactic.pp y
     end⟩
end strategy
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
namespace stack_entry
    meta instance of_strat : has_coe (robot.strategy) (stack_entry) := ⟨stack_entry.strategy⟩
    meta instance has_to_tactic_format : has_to_tactic_format (stack_entry) := ⟨λ s, match s with
    |(strategy s) := tactic.pp s
    |(task c s a) := tactic.pp c
    end
    ⟩
end stack_entry
meta def stack := list stack_entry
namespace stack
    meta instance : has_to_tactic_format stack := ⟨λ s : list stack_entry, tactic.pp s⟩
end stack
meta structure state :=
(lookahead : list rule)
(visited : table expr)
-- (stack : stack)
(rt : rule_table)

/-- The robot monad. -/
meta def M : Type → Type := state_t state conv
meta instance : monad M := state_t.monad
meta instance : monad_state state M := state_t.monad_state
meta instance : alternative M := state_t.alternative
meta instance of_tactic {α} : has_coe (tactic α) (M α) := ⟨state_t.lift⟩
meta instance of_conv {α} : has_coe (conv α) (M α) := ⟨state_t.lift⟩
meta def map_state  (f : state → state) : M unit := (f <$> get) >>= put
meta def get_rule_table : M rule_table := state.rt <$> get
meta def add_rule : rule → M unit := λ r, do
    s ← get,
    rt ← s.rt.insert r,
    put $ { rt := rt, ..s}

meta def get_ce : M expr := state_t.lift (conv.lhs >>= instantiate_mvars)
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

meta def task.test : expr → task → M bool
|ce (task.Create e) := do
    e ← instantiate_mvars e,
    pp_ce ← pp ce, pp_e ← pp e,
    --trace_m "task.test: " $ (to_fmt "testing that " ++ pp_ce ++ " satisfies Create " ++ pp_e),
    matches : list ez.zipper ← ez.zipper.find_occurences ce e ,
    --trace_m "task.test: " $ matches,
    pure $ bnot matches.empty
|ce t@(task.CreateAll e) := do
    -- trace_m "task.test: " $ t,
    o ← hypothetically (unify e ce), 
    pure o.is_some
meta def strategy.of_rule : rule → M strategy := λ r, pure $ strategy.Use $ r

/-- Do In One Move. Check the lookahead table and see if any of the entries in there cause the task to be achieved. -/
meta def task.diom : task → M (list strategy) := λ t, do
    ce ← get_ce,
    lookahead ← get_lookahead,
    winners : list rule ← list.mcollect (λ r, do 
        let rhs := rule.rhs r,
        let pf := rule.pf r,
        x : option rule ← M.hypothetically (do
                result ← task.test rhs t,
                if result then do
                    ppr ← pp r, 
                    trace_m "task.diom: " $ (to_fmt "found a rule: ") ++ ppr,
                    pure r 
                else tactic.fail ""
        ),
        match x with
        |(some r) := pure r
        |none := (tactic.fail "")
        end
    ) lookahead,
    winners.mmap strategy.of_rule
open ez

meta def try_dioms : task → M refinement | t := do 
    -- trace "trying dioms",
    dioms ← task.diom t, 
    --trace dioms,
    if ¬ dioms.empty then pure ([],dioms) else failure

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
    tactic.trace "refine CreateAll",
    scs ← zipper.lowest_uncommon_subterms ce $ zipper.zip a,
    if scs.length = 0 then notimpl else do
    let scs := task.Create <$> zipper.current <$> scs,
    pure $ (scs, [])
end

meta def strategy.execute : strategy → conv unit
|(strategy.ReduceDistance a b) := notimpl
|s@(strategy.Use r)              := zipper.rewrite_conv r
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
    ce ← get_ce,
    is_achieved ← task.test ce t,
    tactic.trace_m "explore_tasks: " $ t,
    if is_achieved then explore_tasks rest acc else do
    (subtasks, substrats) ← task.refine t,
    pp_st ← pp subtasks, pp_ss ← pp substrats,
    trace_m "explore_tasks: " $ (to_fmt "found: " ++ pp_st ++ ", " ++ pp_ss),
    let subtasks := st.append_subtasks $ subtasks.filter (λ t, ¬ stack.has_task st t), -- filter out subtasks that are already on the stack.
    let substrats := st.append_substrats $ substrats.filter (λ s, ¬ stack.has_strat st s),
    let acc := substrats ++ acc,
    explore_tasks (subtasks ++ rest) acc

meta def explore_task : (task × stack) → M (list (strategy × stack))
|ts := explore_tasks [ts] []

meta def explore_strategy : (strategy × stack) → M (list (strategy × stack))
| ⟨s,stack⟩ := do
    (subtasks, substrats) ← strategy.refine s,
    explore_tasks (stack.append_subtasks subtasks) (stack.append_substrats substrats)

meta def explore : stack → M (list (strategy × stack))
|[] := failure
|s@((stack_entry.task t _ _) :: _) := explore_task (t,s)
|s@((stack_entry.strategy t) :: _) := explore_strategy (t,s)

meta def execute_strategy : strategy → stack → M unit
|s rest := do
    state ← get,
    ce ← get_ce,
    trace_m "execute_strategy: " $ s,
    state_t.lift $ strategy.execute s,
    ce' ← get_ce,
    when (ce = ce') (tactic.fail "strategy did not change the goal."),
    --trace_m "execute_strategy: " $ (list.tail rest),
    stack.mfold_achieved (λ _ acheived, do 
        r ← acheived.test ce', 
        when (¬r) (tactic.fail "stategy caused a previously achieved task to fail.")
    ) () $ list.tail $ rest,
    lookahead ← rule_table.rewrites ce' state.rt,
    let visited := state.visited.insert ce,
    put {
        state with
         lookahead := lookahead
        , visited := visited
    }

meta def ascend : stack → M (list (strategy × stack))
|[] := do trace_m "ascend: " $ "done!", pure []
|stack@((stack_entry.strategy s)::t) := do
    trace_m "ascend: " $ s,
    (do execute_strategy s stack, ascend t) 
    <|> (do trace "ascend: execute_strategy failed", explore_strategy (s,stack))
|stack@((stack_entry.task current siblings achieved) :: tail) := do
    trace_m "ascend: " $ current,
    ce ← get_ce,
    is_achieved ← task.test ce current,
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

meta def init (rt : rule_table) : M (list (strategy × stack)) := do
    (_,lhs,rhs) ← target_lhs_rhs,
    lookahead ← rt.rewrites lhs,
    put $ {
        lookahead := lookahead,
        visited := ∅,
        rt := rt
    },
    t ← pure $ task.CreateAll rhs,
    explore_task (t, [stack_entry.task t [] []])

meta def policy := list (strategy × stack) → M (strategy × stack)

/--A simple policy that just tries the first one. -/
meta def first_policy : policy
|[] := failure
|l@(h::t) := do
    pph ← pp h.1,
    ppl ← pp $ list.map prod.fst l,
    -- trace_m "first_policy: " $ (to_fmt "choose ") ++ ppl,
    pure h

meta def run_aux (π : policy) : state → list (strategy × stack) → nat → conv unit
|s [] n := pure ()
|_ _ 0 := fail "timeout"
|s l (n+1) := do
    -- target >>= trace_m "run_aux: ",
    ⟨r,s⟩ ← state_t.run (π l >>= execute) $ s,
    run_aux s r n

meta def run (π : policy) (rt : rule_table) : conv unit := do
    (_,lhs, rhs) ← target_lhs_rhs,
    lookahead ← rt.rewrites lhs,
    let s : state := {lookahead := lookahead, visited := ∅, rt := rt},
    let t := task.CreateAll rhs,
    ⟨r,s⟩ ←  state_t.run (explore_task (t, [stack_entry.task t [] []])) s,
    run_aux π s r 10,
    reflexivity


end robot