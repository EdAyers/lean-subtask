import ..equate
import analysis.normed_space.basic 

namespace robot

#check has_norm.norm

universes u
variables {α : Type u} [normed_group α]

@[equate] lemma norm_def : ∀ x y : α, dist x y = ∥x - y∥ := normed_group.dist_eq
attribute [equate] dist_comm

--set_option pp.all true
@[equate] lemma norm_neg_2 (g : α) : ∥g∥ = ∥-g∥ :=
calc ∥g∥ = ∥-g∥      : by equate

attribute [equate] dist_self
@[equate] lemma norm_zero: ∥(0 : α)∥ = 0 := by equate



@[simp] lemma normed_field.norm_pow {α : Type*} [normed_field α] (a : α) :
  ∀ n : ℕ, ∥a^n∥ = ∥a∥^n
  := begin
    intro n,
    induction n,
    equate, 
  end


end robot