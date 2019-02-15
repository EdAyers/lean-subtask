import ..equate
open robot
universe u

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
    example : x + y + z + u + v + w = w + (x + y + z + u + v) := 
    by equate
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
    example {h : G} : conj h (x) * conj h (y) = conj h (x * y) := by equate
    example {h : G} : conj h (x * y) = conj h x * conj h y := by equate
    example : x * y⁻¹ = (y * x⁻¹)⁻¹
    := by equate
    example :  (y * x⁻¹)⁻¹ = x * y⁻¹
    := by equate
    example 
        (l : ∀ x y, φ (x * y) = φ x * φ y) 
        (l2 : ∀ x y, ψ (x * y) = ψ x * ψ y) {x y : G} 
        : (φ ∘ ψ) (x * y) = (φ ∘ ψ) x * (φ ∘ ψ) y :=
    by equate
    example 
        (l : ∀ x y, φ (x * y) = φ x * φ y) 
        (i1 : ∀ x, φ(ψ x) = x) 
        (i2 : ∀ x, ψ(φ x) = x) {x y : G} 
        : ψ (x * y) = ψ x * ψ y :=
    by equate 
end group_homs1
section group_homs2
    variables {H G : Type u} [group H] [add_comm_group G] {φ ψ: H → G} {x y : H}
    def sum_hom (φ ψ : H → G) : H → G := λ x, φ(x) + ψ(x)
    @[equate] def sum_hom_def : sum_hom φ ψ x = φ(x) + ψ(x) := rfl
    example
        (hφ : ∀ x y, φ (x * y) = φ x + φ y) 
        (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
        : sum_hom φ ψ (x * y) = sum_hom φ ψ x + sum_hom φ ψ y := 
    by equate
end group_homs2

section dist_semigroups
    variables {G : Type u} 
end dist_semigroups


