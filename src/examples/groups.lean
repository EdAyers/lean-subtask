import ..equate
open robot
universe u

attribute [equate] is_group_hom.mul

section additive_groups 
    variables {α : Type u} [add_comm_group α] {u v w x y z : α}
    example : (x + y) + z = (z + x) + y := 
    by equate
    example : x + (y - z) = -z + y + x := 
    by equate
    example : x - (y + z) = x - y - z := 
    by equate
    example : - (x - y) = y + - x := 
    by equate
    example : - (x - y) = y - x := 
    by equate
    example : (x - y) = -(y - x) := 
    by equate
    example : (x + y) + (z + w) = (x + z) + (y + w) := 
    by equate
    example : v + u + (x + y) + (z + w) = (x + z) + (y + w) + v + u := 
    by equate
    lemma X1 : x + y + z + u + v + w = w + (x + y + z + u + v) := 
    by equate
    #print X1
    lemma X2 : x + y + z + u + v + w = w + (x + y + z + u + v) := 
    by (tactic.timetac "ac_refl" $ tactic.ac_refl)
    #print X2
end additive_groups


-- set_option pp.numerals false
-- [FIXME] The least_absent_subterm module has to be able to count previous times that a given subterm is used.

section group_homs1
    variables {H G : Type u} [group H] [group G] {φ : H → G} {ψ : G → H} {x y z h : G}
    example : (x * z) * (z⁻¹ * y) = x * y
    := by equate
    example : x * y = (x * z) * (z⁻¹ * y)
    := by equate
    def conj (h x : G) := h * x * h ⁻¹ 
    @[equate] lemma conj_def : conj h x = h * x * h ⁻¹ := rfl
    example {h : G} : conj h (x) * conj h (y) = conj h (x * y) := 
    by equate
    example {h : G} : conj h (x * y) = conj h x * conj h y := 
    by equate
    example : x * y⁻¹ = (y * x⁻¹)⁻¹
    := by equate
    example :  (y * x⁻¹)⁻¹ = x * y⁻¹
    := by equate
    example [is_group_hom φ] [is_group_hom ψ] {x y : G} 
        : is_group_hom (φ ∘ ψ) := ⟨λ x y, by equate⟩
    example 
        [is_group_hom φ] 
        (i1 : ∀ x, φ(ψ x) = x) 
        (i2 : ∀ x, ψ(φ x) = x) {x y : G} 
        : is_group_hom ψ :=
    ⟨λ a b, by equate⟩ -- [FIXME] this usually works I promise
end group_homs1

section group_homs3
    lemma is_group_hom_mul_2 {α β} [group α] [comm_group β]
    (f g : α → β) [is_group_hom f] [is_group_hom g] :
    is_group_hom (λa, f a * g a) :=
    ⟨assume a b, by equate⟩ -- [FIXME] when apply_core uses is_group_hom.mul it's using the wrong typeclass instance!!
    #print is_group_hom_mul_2
end group_homs3




