import .refine
namespace robot
open tree.zipper tactic robot.tactic

/-- Backtracking state. -/
meta structure memento :=
(score : ℤ)
(candidates : evaluation)
(snapshot : snapshot)

meta inductive engine_mode
|Explore
|Right
|Execute (s : strategy) 
|Backtrack
|Ascend
|Done
meta structure engine_state := 
(mode : engine_mode) 
(cursor : task_zipper)
(backtracks : list memento )
meta def engine_state.with : engine_mode → Z → engine_state → M engine_state
|m c es := pure {mode := m, cursor := c, ..es}
open engine_state

open engine_mode
open tree_entry

/--Returns true if the given task is already present strictly above the current position. -/
meta def has_task : Z → task → tactic bool
|z t := (bnot ∘ list.empty) <$> (z.strict_above.mfilter $ tree_entry.is_eq (tree_entry.task t []))

/-- `fits l r` Returns true if the left item's mvars can be filled in to be defeq with `r` -/
meta def fits : expr → expr → tactic bool
|r l := (do
    r' ← hypothetically' (do
        unify l r transparency.none,
        instantiate_mvars r
    ),
    pure $ r = r') <|> pure ff

/--Returns true if the given strategy is already present strictly above the current position.
   [HACK] If the strategy is a `Use`, it also makes sure that the flip of the rule_app is not present.
 -/
meta def has_strat : Z → strategy → tactic bool
|z (strategy.Use r) := (bnot ∘ list.empty) <$> 
    (z.strict_above.mfilter $ ( λ x, match x with
        |(tree_entry.strat (strategy.Use r₂) _) := (do
            fr ← fits r.lhs r₂.lhs,
            fr2 ← fits r.rhs r₂.rhs,
            if fr && fr2 then pure tt else do
            fl ← fits r.lhs r₂.rhs,
            fl2 ← fits r.rhs r₂.lhs,
            if fl && fl2 then pure tt else pure ff

            ) <|> pure ff
        |_ := pure ff
        end
    ))
|z t := (bnot ∘ list.empty) <$> (z.strict_above.mfilter $ tree_entry.is_eq (tree_entry.strat t []))

meta def refine : tree_entry → M refinement
|(tree_entry.task t a) := task.refine t
|(tree_entry.strat s a) := strategy.refine s

/-- If the input is a task, check if the task is achieved wrt the current expression. -/
meta def is_achieved : tree_entry → M bool
|(tree_entry.task t a) := do ce ← get_ce, task.test ce t
|_ := pure $ ff

/-- Add the given task as an achieved subtask. -/
meta def push_achieved : task → Z → Z := map_item ∘ tree_entry.push_achieved

/-- Fold over all of the achieved tasks above the current zipper. -/
meta def mfold_achieved {T} [monad T] {α} (f : α → task → T α) : α → Z → T α
|a z := z.strict_above.mfoldl (λ a t, list.mfoldl f a $ tree_entry.achieved $ t) a

/-- Perform a step of the engine. The engine is implemented as a state machine with the states listed in `engine_mode`.
    It used to be a load of recursive functions but it was difficult to tweak and reason about.  -/
meta def step (π : policy) : engine_state → M engine_state := λ estate, do
let z := estate.cursor,
ppz ← pp_item_with_indent z,
match estate.mode with
|Explore := do
    ppz ← pp_item_with_indent z,
    tactic.trace_m "explore: " ppz,
    /- In `Explore`, we refine the current item and decide to explore its children -/
    state ← get,
    ce ← get_ce,
    is_achieved ← is_achieved z.item,
    if is_achieved then estate.with Ascend z else do
    (subtasks,substrats) ← refine z.item,
    -- filter out tasks and strategies that are already above us on the task stack.
    subtasks  ← (list.mfilter (λ t, bnot <$> has_task  z t) $ subtasks),
    substrats ← (list.mfilter (λ t, bnot <$> has_strat z t) $ substrats),
    -- add these as children to the zipper.
    z ← pure $ z.grow $ (subtasks.map tree_entry.of_task) ++ (substrats.map tree_entry.of_strat),
    -- extract the child zippers.
    actions : list action      ← pure $ list.choose (λ z, (λ s, (s,z)) <$> (as_strat $ item z)) $ tree.zipper.down_all $ z,
    subtasks : list (task × Z) ← pure $ list.choose (λ z, (λ s, (s,z)) <$> (as_task  $ item z)) $ tree.zipper.down_all $ z,
        candidates ← π.evaluate actions | failure,
        overall_score ← π.get_overall_score candidates,
    ( do
        -- In this case, there is at least one sub-strategy.
        -- [TODO] cross-check the actions here with actions found on previously explored branches of the subtask tree.
        --        Perhaps this should be done in the policy?
        if overall_score > 0 then do
            (⟨⟨s,sz⟩,s_score⟩::others) ← pure candidates | failure,
            others_overall_score ← π.get_overall_score others, 
            snapshot ← M.get_snapshot,
            pure { mode := Execute s
                 , cursor := sz
                 , backtracks := estate.backtracks.cons 
                    $ memento.mk others_overall_score others snapshot
                 }
        else 
            -- this task has no good strategies for it.
            failure
    ) <|> (do 
        -- we couldn't find any good strategies to achieve this node.
        match subtasks with
        |[] := do
            snapshot ← M.get_snapshot,
            pure {
                mode := Right, cursor := z,
                backtracks := ⟨overall_score,candidates,snapshot⟩ :: engine_state.backtracks estate
            }
        |(⟨t,tz⟩ :: rest) := estate.with Explore tz
        end
    ) 
|Execute s := do
    tactic.trace_m "execute: " ppz,
    state ← get,
    ce ← get_ce,
    (do strategy.execute s,
        ce' ← get_ce,
        path ← get_path,
        -- now we do some sanity tests that it was a good idea to do this
        (do when (ce' ∈ path.tail) (trace_m  "loop detected: " ce' *> failure),
            mfold_achieved (λ _ ach, do
                r ← ach.test ce',
                -- tactic.trace_m "test:" $ (r, ach, ce', s),
                
                when (¬r) (trace "strategy caused a previously achieved task to fail" *> failure)
            ) () z,
            targ ← target,
            trace targ,
            z ← up_drop z | estate.with Done z, 
            estate.with Ascend z
        )
        -- if the above sanity checks fail, then backtrack. 
        <|> estate.with Backtrack z
    ) 
    <|> (do -- strategy execution failed.
        -- [TODO] sometimes this is unrecoverable: eg using a group hom law when it is not a group hom.
        estate.with Explore  z
    )
|Ascend := do
    tactic.trace " ascend",
    match z.item with
    |(tree_entry.task t _) := do
        ce ← get_ce,
        is_achieved ← task.test ce t,
        if is_achieved then do
            match up_drop z with
            |none := do 
                estate.with Done z
            |(some z) := do
                z ← pure $ push_achieved t z,
                estate.with Ascend z
            end
        else do
            estate.with Explore z
    |(tree_entry.strat s _) := estate.with (Execute s) z
    end
|Right := do
    trace_m "  right: " $ ppz,
    some ⟨z,i⟩ ← pure $ tree.zipper.up_with_index z | estate.with Backtrack z,
    (do z ← down (i + 1) z,
        if z.item.is_strat then estate.with Right z else        
        estate.with Explore z 
    ) 
    <|> (
        if z.item.is_strat then estate.with Backtrack z else do
        estate.with Right z
    )
|Backtrack := do
    trace "backtrack",
    /- 
     When do we use this?
       When we have deduced that the chosen strategy is impossible or likely to be a dead end.

     What does this do?
     - look through the backtracking points in the state.
     - pick the one that has the lowest overall score.

     What is a backtracking point?
       It's a task_zipper and a state snapshot. Once we have backtracked we throw away all of our work.
       [TODO] Maybe there is a way of retaining what we learned on this branch?
     -/
    let backtracks := estate.backtracks,
    (⟨entropy,candidates,snapshot ⟩::backtracks) ← pure $ list.reverse $ list.qsortby (λ mem, memento.score mem) backtracks | failure,
    ⟨⟨s,sz⟩,score⟩ :: candidates ← pure $ candidates 
        | pure $ {engine_state . mode := Right, cursor := z, backtracks := backtracks},
    -- [TODO] if candidate list is empty, this tells us that the parent subtask is impossible.
    --        this means we can go up to the ancestor strategy and remove that too. For now just discard it.
    entropy' ← policy.get_overall_score π candidates,
    sn ← pure snapshot, 
    backtracks ← pure $ {memento . score := entropy', candidates := candidates, snapshot := sn} :: backtracks,
    M.set_snapshot snapshot,
    pure $ {engine_state . mode := Execute s, cursor :=sz, backtracks := backtracks}
|Done := fail "already done!"
end 


meta def trace_path : M unit := do
    ce ← get_ce,
    -- ppce ← pp ce,
    path ← get_path,
    -- trace path
    r ← (ce::path).reverse.mmap (λ x, tactic.pp x),
    trace $ (format.nest 2 $ format.join $ list.intersperse (format.line ++ "= ") $ r)

meta def run_aux (π : policy) : ℕ → engine_state → M engine_state
|0 s := fail "timeout reached"
|(n+1) s :=
    match s.mode with
    |Done := do trace "done!", trace_path, pure s
    |_ := step π s >>= run_aux n
    end

/--Add all of the rules which appear in the local context. -/
meta def add_hyp_rules (rt : rule_table) : tactic rule_table :=
    local_context >>= list.mfoldl (λ rt r, (do 
        n ← expr.const_name r | failure,
        r ← rule.of_prf n r, 
        rev ← rule.flip r, 
        pure rt >>= rule_table.insert r >>= rule_table.insert rev
    ) <|> pure rt) rt

meta def run (π : policy) (rt : rule_table) : conv unit := do
    rt ← add_hyp_rules rt,
    (_,lhs,rhs) ← target_lhs_rhs,
    lookahead ← rt.rewrites lhs,
    let s :state := {lookahead := lookahead, rt := rt, path := [], bgc := bigram.empty},
    let t := task.CreateAll rhs,
    -- ⟨r,s⟩ ← state_t.run (explore $  ) s,
    let estate : engine_state := {cursor := zip $ tree.branch (tree_entry.task t []) [], backtracks := [], mode := Explore},
    ⟨estate,s⟩ ← state_t.run (run_aux π 100 estate) s,
    reflexivity,
    pure ()

end robot