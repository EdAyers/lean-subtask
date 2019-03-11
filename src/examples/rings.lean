/- Author: E.W.Ayers © 2019 -/
import ..equate tactic
open robot
universe u 
section rings
    -- [TODO] one of the examples in `group` is to show this, so there should be a way of telling `equate` to omit rules.
    attribute [equate] neg_sub 

    variables {α : Type u} [comm_ring α] {a b c d e p x y z : α}


    @[equate] lemma sub_minus : - (a - b) = - a - - b := by equate
    -- comparison with new lemma added
    lemma sumsq_with_equate : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by equate
    lemma sumsq_with_ring : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by ring
    -- compare proof terms:
    #print sumsq_with_equate
    #print sumsq_with_ring
    -- example : (a + b) * (a - b) = a * a - b * b := 
    -- by equate -- [FIXME]
    example : (a * d) * b + b * (c * e) = (a * d + c * e) * b := 
    by equate 
    example : a * b + b * c = (a + c) * b := 
    by equate
    example : (a + c) * b = c * b + b * a := by equate
    example : (a + c) * b = c * b + b * a := by ring

    example : (a * -d - b * - c) * e = -((a * d - b * c) * e) := 
    by equate
    /- [NOTE] the below examples show that our system is not yet able to deal well
    with 'unbalanced' problems where more than one occurrence of a variable is present.
    We aim to fix this with the 'Merge' subtask. -/
    example : (a * b - c * d) = b * a - b * c + (b * c - d * c) :=
    by equate -- [FIXME]
    example : (a + b) * (a - b) = a * a - b * b := 
    by equate -- [FIXME]
    example : (a * b) - c + (b * a) = - c + 2 * (a *  b) := 
    by equate -- [FIXME]
    example : (a * b) - c + (b * a) = - c + (2 * a) *  b := 
    by equate -- [FIXME]
    example : (a * b) - c + (b * a) = - c + a * (b + b) := 
    by equate -- [FIXME]

    /- An extreme comparison of the differences in proof lengths and perils of normal form. -/
    lemma sum_cube_with_equate : (x+y)^3+(x+z)^3 = (z+x)^3+(y+x)^3 := by equate
    lemma sum_cube_with_acrefl : (x+y)^3+(x+z)^3 = (z+x)^3+(y+x)^3 :=
         by ac_refl
    /- `ring` does really badly because it puts the two expressions in to normal form. -/
    lemma sum_cube_with_ring : (x+y)^3+(x+z)^3 = (z+x)^3+(y+x)^3 :=
         by ring
    #print sum_cube_with_equate -- uses eq.trans 3 times
    #print sum_cube_with_acrefl -- uses eq.trans 9 times
    #print sum_cube_with_ring
end rings
