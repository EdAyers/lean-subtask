import ..equate
open robot
namespace tests
section
universe u
open robot.vector_theory
variables {A B : V → V} {x y z u v w : V} {μ ν: k} {a b c d e : k}

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
-- set_option pp.numerals false
-- [FIXME] The least_absent_subterm module has to be able to count previous times that a given subterm is used.
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by equate
example : (a * -d - b * - c) * e = -((a * d - b * c) * e) := 
by equate
example : (a * d) * b + b * (c * e) = (a * d + c * e) * b := 
by equate 
example : a * b + b * c = (a + c) * b := 
by equate 
example : (a + c) * b = a * b + b * c := 
by equate 
example : (x + y) + (z + w) = (x + z) + (y + w) := 
by equate
example : v + u + (x + y) + (z + w) = (x + z) + (y + w) + v + u := 
by equate
example : x + y + z + u + v + w = w + (x + y + z + u + v) := 
by equate
example (il : is_linear A) :
    μ • A (x) + ν • A (y) = A (μ • x + ν • y)  :=
by equate 

example (il : is_linear A) : 
    ⟪A† (x + y) + w, z⟫ = ⟪A† x + A† y + w ,z⟫ := 
by equate 
example (il : is_linear A) :
    ⟪ A† ( u + v ) + w , x ⟫ = ⟪ A† u + w + A† v , x ⟫
:= by equate

example (il : is_linear A) : 
    ⟪A† x + A† y ,z⟫ = ⟪A† (x + y), z⟫ := 
by equate 

@[equate] lemma adj_linear (il : is_linear A) : 
    ⟪A† (x + y), z⟫ = ⟪A† x + A† y ,z⟫ := 
by equate 
-- try the same two problems again but this time with the adjoint lemma.
example (il : is_linear A) : 
    ⟪A† (x + y) + w, z⟫ = ⟪A† x + A† y + w ,z⟫ := 
by equate 
example (il : is_linear A) :
    ⟪ A† ( u + v ) + w , x ⟫ = ⟪ A† u + w + A† v , x ⟫
:= by equate

@[equate] lemma adj_linear_2 (il : is_linear A) : A†(x + y) = A†x + A†y := sorry

example (il : is_linear A) :
    ⟪ A† ( u + v ) + w , x ⟫ = ⟪ A† u + w + A† v , x ⟫
:= by equate
end
section
    universe u
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
end
section
    universe u
    variables {H G : Type u} [group H] [add_comm_group G] {φ ψ: H → G} {x y : H}
    def sum_hom (φ ψ : H → G) : H → G := λ x, φ(x) + ψ(x)
    @[equate] def sum_hom_def : sum_hom φ ψ x = φ(x) + ψ(x) := rfl
    example
        (hφ : ∀ x y, φ (x * y) = φ x + φ y) 
        (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
        : sum_hom φ ψ (x * y) = sum_hom φ ψ x + sum_hom φ ψ y := 
    by equate
end 
-- -- set_option pp.notation false
section
    universe u
    variables {α : Type u} {X A B C : set α}
    @[equate] example : X \ (B ∩ C) = (X \ B) ∪ (X \ C) := 
    by equate
    example : ( X \ B ) ∪ ( X \ C ) = X \ ( B ∩ C ) := 
    by equate
    example : ( X \ B ) \ C = X \ ( B ∪ C ) := 
    by equate
    example : X \ ( B ∪ C ) = ( X \ B ) \ C := 
    by equate
    example : (A ∪ B) \ A = B 
    := by equate
    @[equate] def A6l : (B ∩ C) ∪ A = (B ∪ A) ∩ (C ∪ A) := by equate
    @[equate] def A7l : (B ∪ C) ∩ A = (B ∩ A) ∪ (C ∩ A) := by equate

    example : (A ∪ B) \ C = A \ C ∪ B \ C
    := by equate
    example : A \ C ∪ B \ C = (A ∪ B) \ C 
    := by equate
end

section
    universe u
    open list
    variables  {α : Type u} {l s t : list α} {a b c : α}
    @[equate] lemma assoc : (l ++ s) ++ t = l ++ (s ++ t) :=
    begin
        induction l with lh lt,
        equate,
        equate
    end -- `induction l; simp *`
    lemma rev_app_rev : reverse (l ++ s) = reverse s ++ reverse l :=
    begin
        induction l,
        equate,
        equate 
    end
end

end tests

