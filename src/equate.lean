import .engine2 .policy
import algebra.group_power
import tactic.ring
/- A prototype version of the tactic. -/

namespace robot

meta def equate_user_attr : user_attribute rule_table unit :=
{ name := `equate
, descr := "add the given lemma to equate's rule-table."
, cache_cfg := 
    { mk_cache := rule_table.of_names
    , dependencies := []
    }
}

meta def get_equate_rule_table : tactic rule_table :=
    user_attribute.get_cache equate_user_attr

run_cmd attribute.register `robot.equate_user_attr

meta def equate (names : list name := []) := do
    base ← get_equate_rule_table,
    bonus ← rule_table.of_names names,
    all ← rule_table.join bonus base,
    tactic.timetac "time: " $ robot.run robot.caveman_policy all

/- DEFAULT RULES: -/

attribute [equate] mul_assoc
attribute [equate] mul_comm
attribute [equate] mul_left_inv
attribute [equate] mul_right_inv
attribute [equate] one_mul
attribute [equate] mul_one
attribute [equate] inv_inv
@[equate] lemma mul_inv {G:Type*} [group G] {a b : G} : (a * b) ⁻¹ = b⁻¹ * a⁻¹ := by simp 

attribute [equate] add_assoc
attribute [equate] add_left_neg
attribute [equate] add_right_neg
attribute [equate] zero_add
attribute [equate] add_zero
attribute [equate] add_comm
attribute [equate] neg_add
attribute [equate] neg_neg

attribute [equate] sub_self
attribute [equate] sub_eq_add_neg
attribute [equate] zero_sub
attribute [equate] sub_zero
attribute [equate] sub_neg_eq_add
-- attribute [equate] add_sub_assoc

attribute [equate] left_distrib
attribute [equate] right_distrib
attribute [equate] mul_zero
attribute [equate] zero_mul
attribute [equate] neg_mul_eq_neg_mul
attribute [equate] neg_mul_eq_mul_neg
attribute [equate] neg_mul_neg
attribute [equate] neg_mul_comm
attribute [equate] mul_sub_left_distrib
attribute [equate] mul_sub_right_distrib

@[equate] lemma comp_def {α β γ : Type*} {f : α → β} {g : β → γ} {x : α} : (g ∘ f) x = g (f x) := rfl


namespace ring_theory
    universe u
    variables {R : Type u} [comm_ring R] {x y z a b c : R}
    @[equate] def P1 : x ^ 0 = 1 := rfl
    @[equate] def P2 {n} : x ^ (nat.succ n) = x * x ^ n := rfl
    @[equate] def X2 : 2 * x = x + x  := by ring
end ring_theory

namespace set_rules
    universe u
    variables {α : Type u} {A B C : set α}
    --instance : has_sub (set α) := ⟨λ A B, A ∩ (- B)⟩
    def ext : (∀ a, a ∈ A ↔ a ∈ B) → A = B := begin intro, funext, rw <-iff_eq_eq, apply a x end
    @[equate] def A1 : A \ B = A ∩ (- B) := rfl
    @[equate] def A2 : - ( B ∩ C ) = -B ∪ -C := ext $ λ a, ⟨λ h, classical.by_cases (λ aB, classical.by_cases (λ aC, absurd (and.intro aB aC) h) or.inr ) or.inl,λ h, or.cases_on h (λ h ⟨ab,_⟩, absurd ab h) (λ h ⟨_,ac⟩, absurd ac h)⟩
    @[equate] def A3 :  - ( B ∪ C ) = - B ∩ - C := ext $ λ a, ⟨λ h, ⟨h ∘ or.inl,h ∘ or.inr⟩, λ ⟨x,y⟩ h₂, or.cases_on h₂ x y⟩ 
    @[equate] def A4 : B ∩ C = C ∩ B := ext $ λ a, ⟨and.swap,and.swap⟩
    @[equate] def A5 : B ∪ C = C ∪ B := ext $ λ a, ⟨or.swap, or.swap⟩
    @[equate] def A6 : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := ext $ λ a, ⟨λ h, or.cases_on h (λ h, ⟨or.inl h, or.inl h⟩) (λ ⟨b,c⟩, ⟨or.inr b, or.inr c⟩),λ ⟨ab,ac⟩, or.cases_on ab or.inl $ λ b, or.cases_on ac or.inl $ λ c, or.inr ⟨b,c⟩⟩ -- [NOTE] use mathlib, don't be macochistic.
    @[equate] def A7 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := ext $ λ a, ⟨λ ⟨a,bc⟩,or.cases_on bc (λ b, or.inl ⟨a,b⟩) (λ c, or.inr ⟨a,c⟩), λ h, or.cases_on h (λ ⟨a,b⟩, ⟨a,or.inl b⟩) (λ ⟨a,c⟩, ⟨a,or.inr c⟩)⟩
    @[equate] def A8 : (A ∩ B) ∩ C = A ∩ (B ∩ C)  := ext $ λ a, and.assoc
    @[equate] def A9 : (A ∪ B) ∪ C = A ∪ (B ∪ C)  := ext $ λ a, or.assoc
    @[equate] def A10 : A ∪ ∅ = A := ext $ λ _, or_false _
    @[equate] def A11 : A ∩ ∅ = ∅ := ext $ λ _, and_false _
    @[equate] def A12 : A ∪ set.univ = set.univ := ext $ λ _, or_true _
    @[equate] def A13 : A ∩ set.univ = A := ext $ λ _, and_true _
    @[equate] def A14 : A ∩ A = A := ext $ λ a, ⟨λ ⟨x,y⟩, x, λ x, ⟨x,x⟩⟩
    @[equate] def A15 : A ∪ A = A := ext $ λ a, ⟨λ xy, or.rec_on xy id id, or.inl⟩

end set_rules
namespace list_theory

end list_theory

-- run_cmd (get_equate_rule_table >>= tactic.trace)


end robot