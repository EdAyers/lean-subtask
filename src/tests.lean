import .equate
open robot
namespace tests
-- section
-- universe u
-- open robot.vector_theory
-- variables {A B : V → V} {x y z u v w : V} {μ ν: k} {a b c d e : k}
-- example : (x + y) + z = (z + x) + y := 
-- by equate
-- --set_option pp.notation false
-- example : (a * -d - b * - c) * e = -((a * d - b * c) * e) := 
-- by equate
-- example : (a * d) * b + b * (c * e) = (a * d + c * e) * b := 
-- by equate 
-- example : a * b + b * c = (a + c) * b := 
-- by equate 
-- example : (a + c) * b = a * b + b * c := 
-- by equate 
-- example : (x + y) + (z + w) = (x + z) + (y + w) := 
-- by equate
-- lemma X : v + u + (x + y) + (z + w) = (x + z) + (y + w) + u + v := 
-- begin (tactic.timetac "acrefl" tactic.ac_refl) end
-- #print X
-- lemma X1 : v + u + (x + y) + (z + w) = (x + z) + (y + w) + v + u := 
-- by equate
-- #print X1
-- lemma Y : x + y + z + u + v + w = w + (x + y + z + u + v)
-- := by ac_refl
-- #print Y
-- lemma Y1 : x + y + z + u + v + w = w + (x + y + z + u + v)
-- := by equate
-- #print Y1 -- note the length difference with Y
-- example (il : is_linear A) :
--     μ • A (x) + ν • A (y) = A (μ • x + ν • y)  :=
-- by equate 
-- example (il : is_linear A) : 
--     ⟪A† (x + y), z⟫ = ⟪A† x + A† y ,z⟫ := 
-- by equate 
-- end
-- section
--     universe u
--     variables {H G : Type u} [group H] [group G] {φ : H → G} {ψ : G → H} {x y : G}
    
--     example 
--         (l : ∀ x y, φ (x * y) = φ x * φ y) 
--         (l2 : ∀ x y, ψ (x * y) = ψ x * ψ y) {x y : G} 
--         : (φ ∘ ψ) (x * y) = (φ ∘ ψ) x * (φ ∘ ψ) y :=
--     by equate
--     example 
--         (l : ∀ x y, φ (x * y) = φ x * φ y) 
--         (i1 : ∀ x, φ(ψ x) = x) 
--         (i2 : ∀ x, ψ(φ x) = x) {x y : G} 
--         : ψ (x * y) = ψ x * ψ y :=
--     by equate
-- end
section
    universe u
    variables {H G : Type u} [group H] [add_comm_group G] {φ ψ: H → G} {x y : H}
    example
        (hφ : ∀ x y, φ (x * y) = φ x + φ y) 
        (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
        : φ (x * y) + ψ (x * y) = (φ (x) + ψ(x) )+ (φ(y) + ψ(y) ) :=
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
    by symmetry; equate
    example : X \ ( B ∪ C ) = ( X \ B ) \ C := 
    by equate
    -- example : (A ∪ B) \ A = B 
    -- := by equate
    @[equate] def A6l : (B ∩ C) ∪ A = (B ∪ A) ∩ (C ∪ A) := by equate
    @[equate] def A7l : (B ∪ C) ∩ A = (B ∩ A) ∪ (C ∩ A) := by equate

    example : (A ∪ B) \ C = A \ C ∪ B \ C
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
    end
    lemma rev_app_rev : reverse (l ++ s) = reverse s ++ reverse l :=
    begin
        induction l,
        equate,
        equate 
    end
end

end tests

