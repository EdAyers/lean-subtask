import .equate
open robot
namespace tests
section
universe u
open robot.vector_theory
variables {A B : V → V} {x y z u v w : V} {μ ν: k} {a b c d e : k}
example : (x + y) + z = (z + x) + y := 
by equate -- [TODO] this should be really fast.
--set_option pp.notation false
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
example (il : is_linear A) :
    μ • A (x) + ν • A (y) = A (μ • x + ν • y)  :=
by equate 
example (il : is_linear A) : 
    ⟪A† (x + y), z⟫ = ⟪A† x + A† y ,z⟫ := 
by equate
end
section
    universe u
    variables {H G : Type u} [group H] [group G] {φ : H → G} {ψ : G → H} {x y : G}
    
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
-- set_option pp.notation false
section
    universe u
    variables {α : Type u} {X B C : set α}
    example : X - (B ∩ C) = (X - B) ∪ (X - C) := 
    by equate
    example : ( X - B ) ∪ ( X - C ) = X - ( B ∩ C ) := 
    by equate
    example : ( X - B ) - C = X - ( B ∪ C ) := 
    by equate
    example : X - ( B ∪ C ) = ( X - B ) - C := 
    by equate
end

section
    universe u
    open list
    variables  {α : Type u} {l s t : list α} {a b c : α}
    lemma assoc : (l ++ s) ++ t = l ++ (s ++ t) :=
    begin
        induction l with lh lt,
        equate, -- irl would just do simp [*] for these.
        equate
    end
    open list_theory
    lemma rev_app_rev : reverse (l ++ s) = reverse s ++ reverse l :=
    begin
        induction l,
        symmetry, equate, -- [HACK] can I get this to work?
        equate [``assoc]  
    end
    /- Compare the above with mathlib version:
        @[simp] theorem reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
        by induction s; [rw [nil_append, reverse_nil, append_nil],
        simp only [*, cons_append, reverse_cons, append_assoc]]
        -/
end



end tests

