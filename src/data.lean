-- Following S.E.Morrison's conventions set out in `lean-tidy` whenever possible.
import .graph 
open tactic




namespace robot

-- [NOTE] keep everything as concrete as possible for now. 
-- A suitable abstraction will present itself when it is ready.

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
meta constant task.test : task → expr → bool

meta inductive strategy
|Use : rule → strategy
meta def strategy.lt : strategy → strategy → bool
|(strategy.Use r₁) (strategy.Use r₂) := r₁ < r₂
meta instance strategy.has_lt : has_lt strategy := ⟨λ x y, strategy.lt x y⟩
meta instance strategy.decidable_lt : decidable_rel ((<) : strategy → strategy → Prop) := by apply_instance
meta constant strategy.test : strategy → expr → option expr

meta inductive refinement_result
|Subtasks : list task → refinement_result
|Substrategies : list strategy → refinement_result

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

meta instance : edge_col V E := ⟨E.children⟩
meta def G := digraph V E

meta structure state :=
(ce : expr)
(lookahead : list rule) -- all of the expressions that are one rule away from `ce`.
(tasks : G)
(front : list strategy)
(achieved_tasks : list V) 

namespace state 

meta def lookahead_config : simp_config := 
{ fail_if_unchanged := ff
, single_pass := tt
}



/- 
How creating lookaheads works:

 -/


  -- ext_simplify_core [] lookahead_config lem (λ a, failed) (λ a l n o e,
  --   _
  -- ) (λ a l n o e, pure ⟨a,e,none,ff⟩) `eq e
meta def select_strategy : strategy → state → state :=
  -- 1. find the strategy in the list
  -- 2. remove it. remove all of its piers
  -- 3a. if the strategy is diom, do it and go in to diom mode
  -- 3b. otherwise, refine the strategy, start a new cascade to find the next front.
  -- 4.  
  sorry



meta def cascade : (list task) → state → state := sorry

end state

end robot


