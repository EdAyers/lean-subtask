
import .table .rule .rule_table
namespace robot
open tactic
section equiv
    universes u
    variables {α : Type u} [has_lt α]
    def equiv : α → α → Prop := λ x y, ¬(x<y) ∧ ¬(y < x)
    instance dec_equiv [decidable_rel ((<) : α → α → Prop)] : decidable_rel (equiv : α → α → Prop) := λ x y, dite (x < y) (λ h, is_false (λ ⟨g,_⟩, absurd h g)) (λ h, dite (y < x) (λ h₂, is_false (λ ⟨_,g⟩, absurd h₂ g)) (λ h₂, is_true ⟨h,h₂⟩))
end equiv
@[derive decidable_eq]
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
    |(Create x) := pure ((++) "Create ") <*> tactic.pp x
    |(CreateAll x) := pure (λ x, "CreateAll " ++ x) <*> tactic.pp x
    end⟩
end task
@[derive decidable_eq]
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
    meta instance : has_to_tactic_format robot.strategy := 
    ⟨λ s, match s with
        | (Use x) := do x ← tactic.pp x, pure $ "Use " ++ x
        | (ReduceDistance x y) := pure (λ x y, "ReduceDistance " ++ x ++ " " ++ y) <*> tactic.pp x <*> tactic.pp y
    end⟩
end strategy

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
meta def add_rule : rule → M unit := λ r, do
    s ← get,
    rt ← s.rt.insert r,
    put $ { rt := rt, ..s}

meta def get_ce : M expr := state_t.lift (conv.lhs >>= instantiate_mvars)
meta def get_path : M $ list $ expr := state.path <$> get
meta def get_lookahead : M (list rule) := state.lookahead <$> get
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

meta def task.test : expr → task → M bool
|ce (task.Create e) := do
    e ← instantiate_mvars e,
    pp_ce ← pp ce, pp_e ← pp e,
    --trace_m "task.test: " $ (to_fmt "testing that " ++ pp_ce ++ " satisfies Create " ++ pp_e),
    matches : list ez.zipper ← ez.zipper.find_occurences (ez.zipper.zip ce) e ,
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
                    -- trace $ (to_fmt "found a rule: ") ++ ppr,
                    pure r 
                else failure
        ),
        match x with
        |(some r) := pure r
        |none := failure
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
    -- trace_m "task.refine: " $ submatches,
    strats ← list.mmap strategy.of_rule $ list.filter (λ r, ¬ rule.is_wildcard r) $ submatches,
    pure $ ([],strats)
|(task.CreateAll a) := do
    ce ← get_ce,
    -- tactic.trace "refine CreateAll",
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
    tactic.trace $  indent_by (st.length - depth) $ ppt,
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

meta def trace_path : M unit := do
    ce ← get_ce,
    -- ppce ← pp ce,
    path ← get_path,
    -- trace path
    r ← (ce::path).reverse.mmap (λ x, tactic.pp x),
    trace $ (format.nest 2 $ format.join $ list.intersperse (format.line ++ "= ") $ r)

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
    state_t.lift $ strategy.execute s,
    ce' ← get_ce,
    when (ce = ce') (tactic.trace "strategy did not change the goal." *> failure),
    --trace_m "execute_strategy: " $ (list.tail rest),
    stack.mfold_achieved (λ _ acheived, do 
        r ← acheived.test ce', 
        when (¬r) (tactic.trace "stategy caused a previously achieved task to fail." *> failure)
    ) () $ list.tail $ rest,
    lookahead ← rule_table.rewrites ce' state.rt,
    let path := ce :: state.path,
    -- state_t.lift $ tactic.target >>= tactic.trace,
    put {
        state with
         lookahead := lookahead
        , path := path
    },
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
        explore_task (current, stack)
        
meta def execute : action → M (list action)
| a := do 
    ss ← ascend (a.stack),
    -- trace_m "execute: " $ ss,
    pure $ ss.map (λ ⟨s,ss⟩, action.mk s ss)

meta def init (rt : rule_table) : M (list action) := do
    (_,lhs,rhs) ← target_lhs_rhs,
    lookahead ← rt.rewrites lhs,
    put $ {
        lookahead := lookahead,
        path := [],
        rt := rt,
        backtracks := []
    },
    t ← pure $ task.CreateAll rhs,
    explore_task (t, [stack_entry.task t [] []])

meta def policy := list action → M (list action)

/--A simple policy that just tries the first one. -/
meta def first_policy : policy
|[] := failure
|l@(h::t) := do
    pph ← pp h.1,
    ppl ← pp $ list.map action.strategy l,
    -- trace_m "first_policy: " $ (to_fmt "choose ") ++ ppl,
    pure l

meta def score_rule (r : rule) : M int := do
    is_local ← r.is_local_hypothesis,
    meta_count ← r.count_metas, 
    ce ← get_ce,
    /- IDEA: add a point for every large common subterm between ce and lhs  -/
    lcsts ← zipper.largest_common_subterms (zipper.zip ce) (zipper.zip r.lhs),
    let lcsts :=  lcsts.foldl (λ acc z, if z.is_terminal then acc else acc + 1 ) 0 ,
    --trace_m "score_rule: " $ lcsts,

    -- IDEA: score by symbol overlap
    ce_symbs ← zipper.count_symbols $ ce,
    lhs_symbs ← zipper.count_symbols $ r.lhs,
    let overlap := table.size $ ce_symbs ∩ lhs_symbs,
    let symm_diff := table.size (ce_symbs ∪ lhs_symbs) - overlap,

    pure $ 0 + (if is_local then 10 else 0) - meta_count + lcsts - symm_diff

meta def score_strategy : strategy → M int
|(strategy.ReduceDistance a b) := pure 0
|(strategy.Use r) := score_rule r

/- Refine to ReduceDistance when the children of the given term are all present in the expression. -/

meta def score_policy : policy
|[] := failure
|l  := do
    -- when (l.length >= 10) (failure), -- idea is that too many choices means we are better backtracking.
    scores ← list.mmap (score_strategy ∘ action.strategy) l,
    scoreboard ← pure $ list.zip l scores,
    let scoreboard := scoreboard.qsort (λ x y, x.2 > y.2),
    ppsb ← scoreboard.mmap (λ ⟨s,b⟩, do pps ← pp s, pure $ (to_fmt $ to_string b) ++ format.space ++ pps),
    tactic.trace_m "\n score: \n" $ ppsb,
    tactic.trace " ",
    let scoreboard := scoreboard.map prod.fst,
    -- ⟨a,_⟩ ← list.maxby (prod.snd) $ list.zip l scores,
    pure scoreboard

    /- [TODO] give a human-tuned, ad-hoc score based on:
        - [ ] what previous strategies were chosen from? That is, suppose a strategy came up earlier, then it would be good to detect that it should be a good idea now.
        - [ ] Is the strategy a diom? If yes then it should be preferred, but only if it doesn't introduce too many more metas.
        - [ ] How many siblings does the strategy have? If this number is low we should prefer it.
        - [x] Is the rule an assumption, or a library rule?
        - [ ] Does the rule have high definitional depth?
        - [x] How many metas are introduced?
        - [ ] Some type-theoretical information??? eg, if the rule is for a specific type or for any type.
        - [x] on a `Use`, if there are large subterms already present then that's good.

    [TODO] backtrack when there are lots of possible actions all with bad scores.
     -/ 

    /- [TODO] general
        - Implement ReduceDistance.
        - It is too eager to perform commutativity. It scores higly because 
    
     -/

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
