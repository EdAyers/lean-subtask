import .table .rule .rule_table .data
namespace robot
open tactic
section equiv
    universes u
    variables {α : Type u} [has_lt α]
    def equiv : α → α → Prop := λ x y, ¬(x<y) ∧ ¬(y < x)
    instance dec_equiv [decidable_rel ((<) : α → α → Prop)] : decidable_rel (equiv : α → α → Prop) := λ x y, dite (x < y) (λ h, is_false (λ ⟨g,_⟩, absurd h g)) (λ h, dite (y < x) (λ h₂, is_false (λ ⟨_,g⟩, absurd h₂ g)) (λ h₂, is_true ⟨h,h₂⟩))
end equiv

-- @[derive decidable_eq]
meta inductive stack_entry : Type
|strategy (current : strategy)  : stack_entry
|task  (current : task) (siblings : list task) (achieved : list task) : stack_entry
namespace stack_entry
    meta instance of_strat : has_coe (robot.strategy) (stack_entry) := ⟨stack_entry.strategy⟩
    meta instance has_to_tactic_format : has_to_tactic_format (stack_entry) := 
    ⟨λ s, match s with
        |(strategy s) := tactic.pp s
        |(task c s a) := tactic.pp c
    end⟩
    meta def code : stack_entry → ℕ
    |(strategy _) := 0
    |(task _ _ _) := 1
    meta def lt : stack_entry → stack_entry → bool
    |(strategy x) (strategy y) := x < y
    |(task x _ _) (task y _ _) := x < y
    |x y := code x < code y
    meta instance : has_lt stack_entry := ⟨λ x y, lt x y⟩
    meta instance : decidable_rel ((<) : stack_entry → stack_entry → Prop) := by apply_instance
end stack_entry
/--A stack of tasks and strategies. -/
meta def stack := list stack_entry
namespace stack
    meta instance : has_to_tactic_format stack := ⟨λ s : list stack_entry, tactic.pp s⟩
    -- meta instance : decidable_eq stack := λ a b, list.decidable_eq a b
end stack

meta inductive task_tree 
|branch (t : task) (children : list task_tree) : task_tree
|leaf (s : strategy) : task_tree

meta structure action :=
(strategy : strategy)
(stack : stack)

-- meta structure task_zipper :=
-- (stack : stack)
-- (tasks : task_tree)

meta def stack.append_subtasks : list task → stack → list (task × stack) 
|tasks stack := tasks.map_with_rest (λ c rest, (c,(stack_entry.task c rest []) :: stack)) 

-- namespace task_zipper
--     open task_tree
--     meta def as_task : task_zipper → option task
--     |⟨_,(leaf s)⟩ := none
--     |⟨_,(branch t ch)⟩ := some t
--     meta def down : task_zipper → action ⊕ (list task_zipper) 
--     |⟨stack, task_tree.leaf s⟩ := sum.inl $ ⟨s,stack⟩
--     |⟨stack, task_tree.branch t ch⟩ := 
--         let neighbours := ch.choose as_task in

--         sum.inr $ ch.map_with_rest (λ c rest, ⟨(stack_entry.task c rest []) :: stack, c⟩)
--     meta def to_actions : task_zipper → list action → list action
--     |⟨stack,task_tree.leaf s⟩ acc :=  :: acc
--     |z acc := down z
-- end task_zipper

namespace task_tree
    meta def of_stacks_aux : list (list stack_entry) → option task_tree
    | lls :=
            match lls.head with 
            |[] := none
            |((stack_entry.task t _ _)::_) := 
                let llls := list.partition_many (λ s₁ s₂, equiv (list.take1 s₁) (list.take1 s₂)) lls in
                --trace "asdf" $
                some $ task_tree.branch t $ llls.choose (of_stacks_aux ∘ list.tail)
            |((stack_entry.strategy s ) :: _) :=
                some (task_tree.leaf s)
            end
    meta def of_stacks : list stack → option task_tree := of_stacks_aux ∘ (list.map list.reverse)
    meta def of_actions : list action → option task_tree := of_stacks ∘ (list.map action.stack)
    meta def pretty : task_tree → tactic format
    |(task_tree.branch t ch) := do
        ppt ← pp t,
        ppch ← format.group <$> format.join <$> list.map ((++) (format.line ++ "├─ ")) <$> list.mmap pretty ch,
        pure $ "─┬─" ++ ppt ++ format.indent (ppch) 1
    |(task_tree.leaf s) := do pps ← pp s, pure $ "▶ " ++ pps
    meta instance : has_to_tactic_format task_tree := ⟨pretty⟩
end task_tree
-- meta instance action.decidable_eq : decidable_eq action := λ a₁ a₂, a₁.stack = a₂.stack
/-- A rough backtracking mechanism. [TODO] I don't think I need to hold on to tactic state. Instead I should use the tactic monad itself or some modification thereof. -/
meta def memento := (tactic_state × list action)
meta structure state :=
(lookahead : list rule)
(path : list expr)
-- (stack : stack)
(rt : rule_table)
(backtracks : list memento) -- [TODO] consult people on whether this is the best thing to do.

namespace action
    meta instance : has_to_tactic_format action := ⟨λ ⟨s,ss⟩, pp s⟩
    meta def of_strategy : robot.strategy → robot.stack → action := λ str stack, ⟨str,stack_entry.strategy str :: stack⟩
    -- meta def append_task : robot.task → robot.stack → action := λ str stack, ⟨str,stack_entry.strategy str :: stack⟩
end action
/-- The robot monad. -/
meta def M : Type → Type := state_t state conv
meta instance : monad M := state_t.monad
meta instance : monad_state state M := state_t.monad_state
meta instance : alternative M := state_t.alternative
meta instance of_tactic {α} : has_coe (tactic α) (M α) := ⟨state_t.lift⟩
meta instance of_conv {α} : has_coe (conv α) (M α) := ⟨state_t.lift⟩
meta def map_state  (f : state → state) : M unit := (f <$> get) >>= put
meta def get_rule_table : M rule_table := state.rt <$> get
meta def get_backtracks : M (list memento) := state.backtracks <$> get
meta def set_backtracks (bs : list memento): M unit := map_state (λ x, { backtracks := bs , ..x})
meta def pop_backtracks : M (memento) := do (h::t) ← get_backtracks | failure, set_backtracks t,  pure h
meta def push_backtracks : list action → M unit := λ h, do s ← tactic.read, l ← get_backtracks, set_backtracks (⟨s,h⟩::l)

meta def get_ce : M expr := state_t.lift (conv.lhs >>= instantiate_mvars)
meta def get_path : M $ list $ expr := state.path <$> get
meta def M.hypothetically {α} : M α → M (option α) := λ tac, ⟨λ s, do
    o ← tactic.hypothetically $ state_t.run tac s,
    pure $ (option.map prod.fst o, s)
⟩
meta def M.timetac {α}: string → M α → M α := λ s m, ⟨λ st, timetac s (m.run st)⟩
-- meta def get_stack : M stack := state.stack <$> get
meta def stack.mfold_achieved {T} [monad T] {α} (f : α → task → T α) : α → stack → T α
| a [] := pure a
| a ((stack_entry.strategy _)::t) := stack.mfold_achieved a t
| a ((stack_entry.task current siblings achieved)::t) := achieved.mfoldl f a >>= λ a, stack.mfold_achieved a t
-- meta def mfold_achieved {α} (f : α → task → M α) : α → M α | a := get_stack >>= stack.mfold_achieved f a

meta def refinement := list task × list strategy
meta def refinement.empty : refinement := ([],[])
meta def refinement.of_strategy (s : strategy) : refinement := ([],[s])

meta def strategy.of_rule : rule → M strategy := λ r, pure $ strategy.Use $ r


open ez






meta def trace_path : M unit := do
    ce ← get_ce,
    -- ppce ← pp ce,
    path ← get_path,
    -- trace path
    r ← (ce::path).reverse.mmap (λ x, tactic.pp x),
    trace $ (format.nest 2 $ format.join $ list.intersperse (format.line ++ "= ") $ r)






open tactic

meta def stack.append_substrats : list strategy → stack → list action
|ss stack := ss.map(λ s, ⟨s,stack_entry.strategy s :: stack⟩)
meta def stack.has_task : stack → task → bool
|s t  := list.any s (λ x, match x with |(stack_entry.task x _ _) := equiv t x | _ := ff end)

meta def equal_up_to_mvars (e₁ e₂ : expr) : bool
:= let o : option (dict name name) := expr.mfold2 (λ e₁ e₂ d, match e₁, e₂ with
|(expr.mvar n _ _) , (expr.mvar n₂ _ _) := option.rec_on (dict.get n d) (some (dict.insert n n₂ d)) (λ n₃, if n₂ = n₃ then some d else none)
|_ , _ := none
end
) e₁ e₂ (∅ : dict name name)  in option.is_some o

/-- Check if two strategies are 'effectively equal'.-/
meta def strategy.equiv : strategy → strategy → bool
|(strategy.Use r₁) (strategy.Use r₂) :=
    (equal_up_to_mvars r₁.lhs r₂.lhs)
    ∨ (equal_up_to_mvars r₁.lhs r₂.rhs)
    -- if r₁ = r₂ ∨ (r₁.rhs = r₂.lhs ∧ r₁.lhs = r₂.rhs) then pure true else do
    -- test if they are the same, unifying mvars
|s₁ s₂ :=  equiv s₁ s₂

meta def stack.has_strat : stack → strategy → bool
-- [BUG] is not spotting identical strategies when they contain metavariables.
|s t  := list.any s (λ x, match x with |(stack_entry.strategy x) := strategy.equiv t x  | _ := ff end)

-- meta def explore_task' : stack → task → M (stack × task_tree)
-- |s t := do
--     state ← get, ce ← get_ce,
--     is_achieved ← task.test ce t,
--     if is_achieved then pure (s,task_tree.branch t []) else do
--     (subtasks, substrats) ← task.refine t,
--     let subtasks := st.append_subtasks $ subtasks.filter (λ t, ¬ stack.has_task st t), -- filter out subtasks that are already on the stack.
--     let substrats := st.append_substrats $ substrats.filter (λ s, ¬ stack.has_strat st s),
--     let acc := substrats ++ acc,
--     subtasks ← subtasks.mfold (explore_task' ())

meta def indent_by : nat → format → format
|0 f := f
|(n+1) f := indent_by n ("  " ++ f)

meta def explore_tasks (depth : nat) : list (task × stack) → list action → M (list action)
|[] acc := pure acc
|((t,st) :: rest) acc := do
    state ← get,
    ce ← get_ce,
    is_achieved ← task.test ce t,
    ppt ← pp t,
    tactic.trace $ indent_by (st.length - depth) $ ppt,
    if is_achieved then explore_tasks rest acc else do
    (subtasks, substrats) ← task.refine t,
    -- pp_st ← pp subtasks, pp_ss ← pp substrats,
    -- trace_m "explore_tasks: " $ (to_fmt "found: " ++ pp_st ++ ", " ++ pp_ss),
    let subtasks := st.append_subtasks $ subtasks.filter (λ t, ¬ stack.has_task st t), -- filter out subtasks that are already on the stack.
    let substrats := st.append_substrats $ substrats.filter (λ s, ¬ stack.has_strat st s),
    substrats.mmap' (λ s, do pps ← pp s, tactic.trace $ indent_by (st.length - depth + 1) $ pps),
    let acc := substrats ++ acc,
    -- tactic.trace_m "explore_tasks: " $ subtasks ++ rest,
    explore_tasks (subtasks ++ rest) acc

meta def explore_task : (task × stack) → M (list action)
|ts := explore_tasks (ts.2.length) [ts] []

meta def explore_strategy : action → M (list action)
| ⟨s,stack⟩ := do
    -- pps ← pp s,
    tactic.trace $ s,
    (subtasks, substrats) ← strategy.refine s,
    explore_tasks (stack.length) (stack.append_subtasks subtasks) (stack.append_substrats substrats)

meta def explore : stack → M (list action)
|[] := failure
|s@((stack_entry.task t _ _) :: _) := explore_task (t,s)
|s@((stack_entry.strategy t) :: _) := explore_strategy ⟨t,s⟩


meta def trace_done_path : M unit := do
    ce ← get_ce,
    rhs ← conv.rhs,
    rest ←pure $ if ce = rhs then [ce] else [rhs,ce],
    -- ppce ← pp ce,
    path ← get_path,
    -- trace path
    r ← (rest ++ path).reverse.mmap (λ x, tactic.pp x),
    trace $ (format.nest 2 $ format.join $ list.intersperse (format.line ++ "= ") $ r)

meta def execute_strategy : strategy → stack → M unit
|s rest := do
    state ← get,
    ce ← get_ce,
    --trace_m "execute_strategy: " $ s,
    strategy.execute s,
    ce' ← get_ce,
    path ← get_path,
    when (ce' ∈ path.tail) (tactic.trace "strategy went through previously tried state." *> failure),
    --trace_m "execute_strategy: " $ (list.tail rest),
    stack.mfold_achieved (λ _ acheived, do 
        r ← acheived.test ce', 
        when (¬r) (tactic.trace "stategy caused a previously achieved task to fail." *> failure)
    ) () $ list.tail $ rest,
    -- state_t.lift $ tactic.target >>= tactic.trace,
    when (path.length > 1) (do
        trace "current path:"
        trace_path, 
        trace " "
    )

meta def ascend : stack → M (list action)
|[] := do 
    trace "done!",
    trace_done_path,
    pure []
|stack@((stack_entry.strategy s)::t) := do
    -- trace_m "ascend: " $ s,
    (do execute_strategy s stack, ascend t) 
    <|> (do 
        -- trace "ascend: execute_strategy failed", 
        explore_strategy ⟨s,stack⟩
    )
|stack@((stack_entry.task current siblings achieved) :: tail) := do
    -- trace_m "ascend: " $ current,
    ce ← get_ce,
    is_achieved ← task.test ce current,
    if (is_achieved) then
        let achieved := current::achieved in
        match siblings with
        |[] := ascend tail
        |_ := do
            let front := siblings.map_with_rest (λ subtask siblings, (subtask, (stack_entry.task subtask siblings achieved)::tail)), 
            actions ← explore_tasks (stack.length + 1) front [],
            -- trace_m "ascend: " $ actions,
            if (actions.empty) then ascend tail else pure actions 
        end
    else do 
        -- trace_m "ascend: not yet achieved " $ current,
        --trace_m "ascend: " $ (siblings, achieved),
        explore_task (current, stack)
        
meta def execute : action → M (list action)
| a := do 
    ss ← ascend (a.stack),
    -- trace_m "execute: " $ ss,
    pure $ ss.map (λ ⟨s,ss⟩, action.mk s ss)

meta def policy := list action → M (list action)

/--A simple policy that just tries the first one. -/
meta def first_policy : policy
|[] := failure
|l@(h::t) := do
    pph ← pp h.1,
    ppl ← pp $ list.map action.strategy l,
    -- trace_m "first_policy: " $ (to_fmt "choose ") ++ ppl,
    pure l


/- Refine to ReduceDistance when the children of the given term are all present in the expression. -/


/- [TODO] sort out backtracking. -/

meta def backtrack : M (list action) := do
    trace "backtrack",
    -- bts ← get_backtracks,
    -- i ←  list.maxidx (λ x, list.length $ prod.snd $ x) bts,
    -- (ts,actions)::bts ← pure $ list.skip i bts | failure,
    -- set_backtracks bts,
    (ts,actions) ← pop_backtracks,
    write ts,
    pure actions

meta def run_aux (π : policy) : state → list action → nat → conv unit
|_ _ 0 := fail "timeout"
|s As (n+1) :=
    reflexivity 
    <|> (do ⟨As,s⟩ ← state_t.run (do
            -- state_t.lift $ target >>= trace_m "run_aux: ",
            -- state_t.lift $ trace_m "run_aux: " $ As,
            (A::rest) ← π As |(state_t.lift $ trace "policy failed") *> failure,
            push_backtracks rest,
            As ← execute A,
            -- state_t.lift $ tactic.try $ (
            --    do tsks ← trace_fail $ tactic.returnopt $ task_tree.of_actions As,
            --     trace_m "run_aux: \n" $ tsks
            -- ),
            pure As
        ) s,
        run_aux s As n
        -- <|> (do (As,s) ← state_t.run backtrack s, run_aux s As (n / 2)) 
    )

/--Add all of the rules which appear in the local context. -/
meta def add_hyp_rules (rt : rule_table) : tactic rule_table :=
    local_context >>= list.mfoldl (λ rt r, (do 
        r ← rule.of_prf r, 
        rev ← rule.flip r, 
        pure rt >>= rule_table.insert r >>= rule_table.insert rev
    ) <|> pure rt) rt

meta def run (π : policy) (rt : rule_table) : conv unit := do
    rt ← add_hyp_rules rt,
    (_,lhs, rhs) ← target_lhs_rhs,
    lookahead ← rt.rewrites lhs,
    -- trace rt,
    let s : state := {lookahead := lookahead, rt := rt, backtracks := [], path := []},
    let t := task.CreateAll rhs,
    ⟨r,s⟩ ←  state_t.run (explore_task (t, [stack_entry.task t [] []])) s,
    run_aux π s r 20
    --reflexivity

meta def fake_run (π : policy) (rt : rule_table) : tactic unit := trace "fake_run: hello"

end robot
