/- Author: E.W.Ayers © 2019 -/
import ..equate
import analysis.normed_space.basic tactic

namespace robot

#check has_norm.norm

universes u
variables {α : Type u} [normed_group α] {a : α } {μ : ℝ}

@[equate] lemma norm_def : ∀ x y : α, dist x y = ∥x - y∥ := normed_group.dist_eq
attribute [equate] normed_field.norm_mul
attribute [equate] dist_comm

-- even when `equate` can't get the answer in one go, you can use it to make proofs more readable:
lemma norm_neg_2 (g : α) : ∥-g∥ = ∥g∥ :=
calc ∥-g∥ = dist 0 g : by equate
     ...  = ∥g∥      : by symmetry ; equate

attribute [equate] norm_neg_2

attribute [equate] dist_self
--@[equate] lemma norm_zero: ∥(0 : α)∥ = 0 := by equate

@[equate] lemma power_def_succ {α : Type u} [monoid α] {a : α} {n : ℕ} : a ^ (nat.succ n) = a * (a ^ n) := rfl
@[equate] lemma power_def_zero {α : Type u} [monoid α] {a : α} : a ^ 0 = 1 := rfl

@[simp] lemma normed_field.norm_pow {α : Type*} [normed_field α] (a : α) : ∀ n : ℕ, ∥a^n∥ = ∥a∥^n := 
begin
    intro n,
    induction n,
    simp,
    equate
end


end robot