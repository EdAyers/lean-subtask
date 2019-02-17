import .refine
namespace robot
open tree.zipper tactic robot.tactic

meta inductive engine_mode
|Explore
|Right
|Execute (s : strategy) 
|Backtrack
|Ascend
meta structure engine_state := 
(mode : engine_mode) 
(z : task_zipper) 
open engine_mode
open tree_entry

/--Returns true if the given task is strictly above the current position. -/
meta def has_task : Z → task → tactic bool
|z t := (bnot ∘ list.empty) <$> (z.strict_above.mfilter $ tree_entry.is_eq (tree_entry.task t []))
meta def has_strat : Z → strategy → tactic bool
|z (strategy.Use r) := (bnot ∘ list.empty) <$> 
    (z.strict_above.mfilter $ ( λ x, match x with
        |(tree_entry.strat (strategy.Use r₂) _) := pure $ r = r₂ ∨ (r.lhs = r₂.rhs ∧ r.rhs = r₂.lhs) 
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

/-- Fold over all of the achieved tasks above the current zipper. -/
meta def mfold_achieved {T} [monad T] {α} (f : α → task → T α) : α → Z → T α
|a z := z.strict_above.mfoldl (λ a t, list.mfoldl f a $ tree_entry.achieved $ t) a

meta def step (π : policy) : engine_state → M engine_state
|⟨Explore, z⟩ := do
    /- In `Explore`, we refine the current item and decide to explore its children -/
    state ← get,
    ce ← get_ce,
    is_achieved ← is_achieved z.item,
    if is_achieved then pure ⟨Ascend, z⟩ else do
    (subtasks,substrats) ← refine z.item,
    -- filter out tasks and strategies that are already above us on the task stack.
    subtasks  ← (list.mfilter (λ t, bnot <$> has_task  z t) $ subtasks),
    substrats ← (list.mfilter (λ t, bnot <$> has_strat z t) $ substrats),
    -- add these as children to the zipper.
    z ← pure $ z.grow $ (subtasks.map tree_entry.of_task) ++ (substrats.map tree_entry.of_strat),
    -- extract the child zippers.
    actions : list action      ← pure $ list.choose (λ z, (λ s, (s,z)) <$> (as_strat $ item z)) $ tree.zipper.down_all $ z,
    subtasks : list (task × Z) ← pure $ list.choose (λ z, (λ s, (s,z)) <$> (as_task  $ item z)) $ tree.zipper.down_all $ z,
    ( do 
        -- In this case, there is at least one sub-strategy.
        ⟨score, ⟨⟨s,sz⟩,s_score⟩::others⟩ ← π actions | failure,
        -- [TODO] cross-check the actions here with actions found on previously explored branches of the subtask tree.
        --      Perhaps this should be done in the policy?
        if score > 0 then
            -- by committing to `top`, we are not committing to a large search. [TODO] in the future this should be a best-first dealio.
            -- [TODO] we might have still made a mistake, so add a backtracking point.
            pure $ engine_state.mk (Execute s) sz
        else 
            -- this task has no good strategies for it.
            failure
    ) <|> (do 
        -- we couldn't find any good strategies to achieve this node.
        match subtasks with
        |[] := pure $ ⟨Right, z⟩
        |(⟨t,tz⟩ :: rest) := pure $ ⟨Explore, tz⟩
        end
    )
|⟨Execute s, z⟩ := do
    state ← get,
    ce ← get_ce,
    strategy.execute s,
    ce' ← get_ce,
    path ← get_path,

    -- now we do some sanity tests that it was a good idea to do this:
    -- if this fails, we should backtrack.
    (do  
        when (ce' ∈ path.tail) (fail "loop detected."),
        mfold_achieved (λ _ ach, do
                r ← ach.test ce',
                -- tactic.trace_m "test:" $ (r, ach, ce', s),
                when (¬r) (fail "strategy caused a previously achieved task to fail")
        ) () z,
        targ ← target,
        trace targ,

        
    ) <|> pure ⟨Backtrack, z⟩

end robot