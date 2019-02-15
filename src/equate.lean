import .engine .policy
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
    tactic.timetac "time: " $ robot.run robot.score_policy all

/- DEFAULT RULES: -/

@[equate] lemma comp_def {α β γ : Type*} {f : α → β} {g : β → γ} {x : α} : (g ∘ f) x = g (f x) := rfl

namespace group_theory
    universes u
    attribute [equate] semigroup.mul_assoc
    attribute [equate] group.mul_left_inv
    attribute [equate] mul_right_inv
    attribute [equate] monoid.one_mul
    attribute [equate] monoid.mul_one
    variables {H : Type u} [group H] {x y z : H} 
    @[equate] def II: (x * y)⁻¹ = y⁻¹ * x⁻¹ := by simp
    @[equate] def inv_inv : x ⁻¹ ⁻¹ = x := by simp

    open tactic

end group_theory

namespace add_grp_theory 
    attribute [equate] add_assoc
    attribute [equate] add_left_neg
    attribute [equate] add_right_neg
    attribute [equate] zero_add
    attribute [equate] add_zero
    attribute [equate] add_comm
    universe u
    variables {A : Type u} [add_comm_group A] {x y z : A}
    variables {B : Type u} [add_comm_group B]
    @[equate] def sub_def : x - y = x + - y := by simp
    @[equate] def sub_plus_plus_sub : - (x + y) = (-x + - y) := by simp
    @[equate] def sub_sub_sub_sub : ( - x - - y) = - (x - y) := by simp
    @[equate] def sub_zero : x - 0 = x := by simp
    @[equate] def sub_sub : - - x= x := by simp
end add_grp_theory

namespace ring_theory
    universe u
    variables {R : Type u} [comm_ring R] {x y z a b c : R}
    @[equate] def M1 : (x * y) * z = x * (y * z) := by apply mul_assoc
    @[equate] def M3L : 1 * x = x := by apply one_mul
    @[equate] def M3R : x * 1 = x := by apply mul_one
    @[equate] def M4 : x * y = y * x := by apply mul_comm
    @[equate] def S1 : (- x) * y = - (x * y) := by simp
    @[equate] def S2 : x * -y = - (x * y) := by simp
    @[equate] def D1 : x * (y + z) = (x * y) + (x * z) := by apply left_distrib
    @[equate] def D2 : (y + z) * x = y * x + z * x := by apply right_distrib
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
    universe u
    open list
    variables {α : Type u} {a h : α} {l t : list α}
    @[equate] def nil_append : [] ++ l = l := rfl
    @[equate] def append_cons : (h::t) ++ l = h:: (t ++ l) := rfl
    @[equate] def rev_nil : reverse ([] : list α) = [] := rfl
    @[equate] def append_nil : l ++ [] = l := begin induction l, refl, simp end
    @[equate] theorem rev_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] := 
    begin
            have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]),
            intro l₁, induction l₁, intros, refl,
            intro, 
            equate, 
            symmetry,
            equate
    end
end list_theory

-- run_cmd (get_equate_rule_table >>= tactic.trace)


end robot