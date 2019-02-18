import ..equate
open robot
universe u 
section sets 
    variables {α : Type u} {X A B C : set α}
    @[equate] example : X \ (B ∩ C) = (X \ B) ∪ (X \ C) := 
    by equate
    example : ( X \ B ) ∪ ( X \ C ) = X \ ( B ∩ C ) := 
    by equate
    example : ( X \ B ) \ C = X \ ( B ∪ C ) := 
    by equate
    example : X \ ( B ∪ C ) = ( X \ B ) \ C := 
    by equate
    @[equate] def A6l : (B ∩ C) ∪ A = (B ∪ A) ∩ (C ∪ A) :=
    by equate
    @[equate] def A7l : (B ∪ C) ∩ A = (B ∩ A) ∪ (C ∩ A) := 
    by equate
    example : (A ∪ B) \ A = B \ A
    := by equate
    example : (A ∪ B) \ C = A \ C ∪ B \ C
    := by equate
    example : A \ C ∪ B \ C = (A ∪ B) \ C 
    := by equate
end sets
