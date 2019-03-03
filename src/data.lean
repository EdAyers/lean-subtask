import .table .rule .rule_table .tree .bigram
namespace robot

@[derive decidable_eq]
meta inductive task : Type
|CreateAll : expr → task
|Create : ℕ → expr → task
/- Use a term annihilation move. For example `X * X⁻¹ = e` annihilates anything in X. -/
|Annihilate : expr → task
/- passes when we remove the given term from the CE. 
Generally this is only used when a variable appears in the CE but not 
in the target and there are no rules explicitly removing the variable. -/
|Destroy : expr.zipper → task
|Merge : expr → task
namespace task
    protected meta def code : task → ℕ
    |(Create _ _) := 0
    |(CreateAll _) := 1
    |(Annihilate _) := 2
    |(Merge _) := 3
    |(Destroy _) := 4
    protected meta def lt : task → task → bool
    |(Create n₁ e₁) (Create n₂ e₂) := (n₁,e₁) < (n₂,e₂)
    |(CreateAll e₁) (CreateAll e₂) := e₁ < e₂
    |(Annihilate e₁) (Annihilate e₂) := e₁ < e₂
    |(Merge e₁) (Merge e₂) := e₁ < e₂
    |x y := task.code x < task.code y
    meta instance has_lt : has_lt task := ⟨λ x y, task.lt x y⟩
    meta instance decidable_lt : decidable_rel ((<) : task → task → Prop) := by apply_instance
    meta instance : has_to_tactic_format task := ⟨λ t, match t with
    |(Create n x) :=
        if n = 0 then notimpl /- should not happen -/ else
        if n = 1 then pure ((++) "Create ") <*> tactic.pp x else
        pure (λ ppn ppx, "Create(×" ++ ppn ++ ") " ++ ppx) <*> tactic.pp n <*> tactic.pp x
    |(CreateAll x) := pure (λ x, "CreateAll " ++ x) <*> tactic.pp x
    |(Annihilate x) := pure ((++) "Annihilate ") <*> tactic.pp x
    |(Destroy x) := pure ((++) "Destroy ") <*> tactic.pp x
    |(Merge x) := pure ((++) "Merge ") <*> tactic.pp x
    end⟩
    meta def is_def_eq : task → task → tactic bool
    |(Create n₁ x) (Create n₂ y) := if n₁ ≠ n₂ then pure ff else tactic.is_success $ tactic.is_def_eq x y
    |(CreateAll x) (CreateAll y) := tactic.is_success $ tactic.is_def_eq x y
    |(Annihilate x) (Annihilate y) := tactic.is_success $ tactic.is_def_eq x y
    |(Merge x) (Merge y) := tactic.is_success $ tactic.is_def_eq x y
    -- |(Create2 x) (Create2 y) := tactic.is_success $ tactic.is_def_eq x y
    |_ _ := pure ff
end task
open task

@[derive decidable_eq]
meta inductive strategy : Type
|Use : rule_app → strategy
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
    meta def is_def_eq : strategy → strategy → tactic bool
    |(Use r₁) (Use r₂) := rule_app.is_def_eq r₁ r₂
    |(ReduceDistance a b) (ReduceDistance c d) :=
        tactic.is_success $ (do tactic.is_def_eq a c, tactic.is_def_eq b d)
    |_ _ := pure ff
end strategy

meta inductive tree_entry : Type
|task (t : task) (achieved : list task)
|strat (s : strategy) (achieved : list task)
namespace tree_entry
    meta def code : tree_entry → ℕ
    |(task _ _) := 0 | (strat _ _) := 1
    meta def lt : tree_entry → tree_entry → bool
    |(task t₁ a₁) (task t₂ a₂) := t₁ < t₂
    |(strat s₁ _) (strat s₂ _) := s₁ < s₂
    |x y := x.code < y.code
    meta instance has_lt : has_lt tree_entry := ⟨λ x y, lt x y⟩
    meta instance decidable_lt : decidable_rel ((<) : tree_entry → tree_entry → Prop) := by apply_instance
    meta def of_task : robot.task → tree_entry := λ t, tree_entry.task t []
    meta def as_task : tree_entry → option robot.task |(tree_entry.task t _) := some t | _ := none
    meta def of_strat : robot.strategy → tree_entry := λ t, tree_entry.strat t []
    meta def as_strat : tree_entry → option robot.strategy |(tree_entry.strat t _) := some t | _ := none
    meta def is_strat : tree_entry → bool := option.is_some ∘ as_strat
    /-- Get the achieved child subtasks for this entry. -/
    meta def achieved : tree_entry → list robot.task | (tree_entry.strat _ a) := a | (tree_entry.task _ a) := a
    meta def map_achieved (f : list robot.task → list robot.task) : tree_entry → tree_entry 
    | (tree_entry.strat s a) := (tree_entry.strat s $ f a) | (tree_entry.task t a) := tree_entry.task t $ f a
    meta def push_achieved (t : robot.task) : tree_entry → tree_entry := map_achieved ((::) t)
    meta instance : has_to_tactic_format tree_entry := ⟨λ x, match x with |(task t _ ) := tactic.pp t | (strat s _ ) := tactic.pp s end⟩
    meta def is_def_eq : tree_entry → tree_entry → tactic bool
    |(task a _) (task b _) := task.is_def_eq a b
    |(strat a _) (strat b _) := strategy.is_def_eq a b 
    |_ _ := pure ff
    meta def is_eq : tree_entry → tree_entry → tactic bool
    |(task a _) (task b _) := pure $ a = b
    |(strat a _) (strat b _) := pure $ a = b
    |_ _ := pure ff
end tree_entry

meta def task_tree := tree tree_entry 
meta def task_zipper := tree.zipper tree_entry
notation `Z` := task_zipper

meta structure state :=
(lookahead : list rule_app)
(path : list expr)
(rt : rule_table)
(bgc : bigram_cache)

meta def refinement := list task × list strategy
meta instance : has_append refinement := ⟨λ ⟨ts₁,ss₁⟩ ⟨ts₂,ss₂⟩, ⟨ts₁ ++ ts₂, ss₁ ++ ss₂⟩⟩
meta instance : has_emptyc refinement := ⟨⟨[],[]⟩⟩
meta def action := (strategy × Z)
meta instance : has_to_tactic_format action := ⟨λ ⟨s,_⟩, tactic.pp s⟩

meta def as_action : Z → option action := λ z, z.item.as_strat >>= λ s, pure (s,z)

end robot