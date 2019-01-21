import .data .refine
namespace robot
open tree.zipper tactic

meta def has_task : Z → task → tactic bool
|z t := (bnot ∘ list.empty) <$> (z.above.mfilter $ tree_entry.is_eq (tree_entry.task t []))
meta def has_strat : Z → strategy → tactic bool
|z (strategy.Use r) := (bnot ∘ list.empty) <$> 
    (z.above.mfilter $ ( λ x, match x with
        |(tree_entry.strat (strategy.Use r₂) _) := pure $ r = r₂ ∨ (r.lhs = r₂.rhs ∧ r.rhs = r₂.lhs) 
        |_ := pure ff
        end
    ))
|z t := (bnot ∘ list.empty) <$> (z.above.mfilter $ tree_entry.is_eq (tree_entry.strat t []))

meta def explore_tasks : list Z → list action → M (list action)
|[] acc := pure acc
|(z::rest) acc := do
  ppz ← pp_item_with_indent z, 
  match z.item with
  |(tree_entry.strat s _) := explore_tasks rest $ (s,z) :: acc
  |(tree_entry.task t _) := do  
    state ← get,
    ce ← get_ce,
    is_achieved ← task.test ce t,
    --trace_state,
    trace_m "" $ ppz,
    if is_achieved then explore_tasks rest acc else do
    (subtasks,substrats) ← task.refine t,
    subtasks ← list.map (tree_entry.of_task) <$> (list.mfilter (λ t, bnot <$> has_task z t) $ subtasks),
    substrats ← list.map (tree_entry.of_strat) <$> (list.mfilter (λ t, bnot <$> has_strat z t) $ substrats),
    let children := substrats ++ subtasks,
    -- trace_m "explore: " children, 
    let z := z.grow children,
    let zs := z.children,
    explore_tasks (zs ++ rest) acc
  end

meta def explore : Z → M (list action) := λ z, explore_tasks [z] []
meta def explore_strategy : action → M (list action)
|⟨s,z⟩ := do
  (subtasks,substrats) ← strategy.refine s,
--   trace_m "explore_strategy: " $ subtasks,
  subtasks ← list.map (tree_entry.of_task) <$> (list.mfilter (λ t, bnot <$> has_task z t) $ subtasks),
  substrats ← list.map (tree_entry.of_strat) <$> (list.mfilter (λ t, bnot <$> has_strat z t) $ substrats),
  let children := substrats ++ subtasks,
--   trace_m "explore_strategy: " $ children,
  explore_tasks (tree.zipper.children $ tree.zipper.grow children $ z) []

meta def push_achieved : task → Z → Z := map_item ∘ tree_entry.push_achieved
/-- Fold over all of the achieved tasks strictly above the current zipper. -/
meta def mfold_achieved {T} [monad T] {α} (f : α → task → T α) : α → Z → T α
|a z := z.above.mfoldl (λ a t, list.mfoldl f a $ tree_entry.achieved $ t) a

meta def execute : action → M unit
|⟨s,z⟩ := do
  state ← get,
  ce ← get_ce,
  strategy.execute s,
  ce' ← get_ce,
  path ← get_path,
  when (ce' ∈ path.tail) (fail "expression looped back"),
  mfold_achieved (λ _ ach, do
    r ← ach.test ce',
    when (¬r) (fail "strategy caused a previously achieved task to fail")
  ) () z,
  targ ← target, trace targ

meta def trace_path : M unit := do
    ce ← get_ce,
    -- ppce ← pp ce,
    path ← get_path,
    -- trace path
    r ← (ce::path).reverse.mmap (λ x, tactic.pp x),
    trace $ (format.nest 2 $ format.join $ list.intersperse (format.line ++ "= ") $ r)

meta def ascend : Z → M (list action) := λ z,
  match z.item with
  |(tree_entry.task t _) := do
    ce ← get_ce,
    is_achieved ← task.test ce t,
    -- trace_m "ascend: " $ (t,is_achieved,ce,z.above), 
    if is_achieved then do
    --   z.up_drop >>= (λ z, pure $ tree.zipper.item <$> z.children) >>= λ p, tactic.trace p,
      match up_drop z with
      |none := do trace "done!", trace_path, pure []
      |some z := do
        z ← pure $ push_achieved t z,
        -- trace $ z.above,
        -- (ach,r) ← @list.mpartition _ _ _ task _ (λ z, 
        --     match tree.zipper.item z with
        --     |zi@(tree_entry.task tsk _) := do 
        --         is_achieved ← task.test ce t,
        --         if is_achieved then pure $ sum.inl t
        --         else pure $ sum.inr z.current
        --     |te := pure $ sum.inr z.current
        --     end
        -- ) z.children,
        -- trace_m "ascend: " $ tree.zipper.item <$> z.children, 
        -- trace_m "ascend: " $ tree.head_item <$> r, 
        --z ← pure $ list.foldl (λ z t, push_achieved t z) z ach,
        -- z ← pure $ z.set_children r,
        match z.children with
        |[] := ascend z
        |ch@(h::t) := do

          -- [FIXME] currently assuming all of t's siblings are also tasks!
          actions ← explore_tasks ch [], 
          -- trace_m "ascend: " $ actions, 
          if actions.empty then ascend z else pure actions
        end
      end
    else explore z
  |(tree_entry.strat s _) :=
    (do execute (s,z), z ← up_drop z | pure [], ascend z)
    <|> 
    (do explore_strategy ⟨s,z⟩)
  end

meta def step : action → M (list action)
|⟨s,z⟩ :=  ascend z

meta def run_aux (π : policy) : state → list action → ℕ → conv unit
|_ _ 0 := fail "timeout"
|s actions (n+1) :=
  reflexivity
  <|> (do
    ⟨actions,s⟩ ← state_t.run (do
      (a::rest) ← π actions | state_t.lift $ fail "policy failed",
      -- state_t.lift $ trace a,
      actions ← step a,
      -- state_t.lift $ tactic.trace_state,
      pure actions
    ) s,
    -- if actions.empty then (trace_m "run_aux:" $ "no actions left") *> reflexivity else 
    run_aux s actions n
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
    let s : state := { lookahead := lookahead, rt := rt, path := []},
    let t := task.CreateAll rhs,
    ⟨r,s⟩ ← state_t.run (explore $ zip $ tree.branch (tree_entry.task t []) []) s,
    run_aux π s r 20

end robot