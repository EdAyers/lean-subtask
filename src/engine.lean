import .data .refine
namespace robot
open tree.zipper tactic

meta def has_task : Z → task → bool
|z t := z.any_above $ λ x, match x with (tree_entry.task x _) := t = x | (tree_entry.strat s _ ) := ff end

meta def has_strat : Z → strategy → bool
|z t := z.any_above $ λ x, match x with (tree_entry.strat x _) := t = x | (tree_entry.task s _ ) := ff end

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
    let subtasks := list.map (tree_entry.of_task) $ list.filter (λ t, ¬ has_task z t) $ subtasks,
    let substrats := list.map (tree_entry.of_strat) $ list.filter (λ s, ¬ has_strat z s) $ substrats,
    let children := substrats ++ subtasks,
    --trace_m "explore: " $ children,
    let z := z.grow children,
    let zs := z.children,
    explore_tasks (zs ++ rest) acc
  end

meta def explore : Z → M (list action) := λ z, explore_tasks [z] []
meta def explore_strategy : action → M (list action)
|⟨s,z⟩ := do
  (subtasks,substrats) ← strategy.refine s,
  let subtasks := list.map tree_entry.of_task $ subtasks,
  let substrats := list.map tree_entry.of_strat $ substrats,
  explore_tasks (children $ grow (substrats ++ subtasks) $ z) []

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
  ) () z

meta def ascend : Z → M (list action) := λ z,
  match z.item with
  |(tree_entry.task t _) := do
    ce ← get_ce,
    is_achieved ← task.test ce t,
    -- trace_m "ascend: " $ (t,is_achieved,ce), 
    if is_achieved then
      match up_drop z with
      |none := do trace "done!", pure []
      |some z := do
        z ← pure $ push_achieved t z,
        match z.children with
        |[] := ascend z
        |ch := do
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