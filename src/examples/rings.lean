import ..equate tactic
open robot
universe u 
section rings
    -- [TODO] one of the examples in `group` is to show this, so there should be a way of telling `equate` to omit rules.
    attribute [equate] neg_sub 

    variables {α : Type u} [comm_ring α] {a b c d e x y z : α}
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by equate
    example : (a * -d - b * - c) * e = -((a * d - b * c) * e) := 
    by equate
    @[equate] lemma sub_minus : - (a - b) = - a - - b := by equate
    -- comparison with new lemma added
    variables {α : Type u} [comm_ring α] {a b c d e : α}
    lemma sumsq_1 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by equate
    lemma sumsq_2 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by ring
    #print sumsq_1
    #print sumsq_2
    -- example : (a + b) * (a - b) = a * a - b * b := 
    -- by equate
    example : (a * -d - b * - c) * e = -((a * d - b * c) * e) := 
    by equate
    example : (a * d) * b + b * (c * e) = (a * d + c * e) * b := 
    by equate 
    example : a * b + b * c = (a + c) * b := 
    by equate
    example : (a + c) * b = a * b + b * c := 
    by equate
    
    /- Failures: -/

    example : (a + b) * (a - b) = a * a - b * b := 
    by equate
    example : (a * b) - c + (b * a) = - c + 2 * (a *  b) := 
    by equate  
    example : (a * b) - c + (b * a) = - c + (2 * a) *  b := 
    by equate  
    example : (a * b) - c + (b * a) = - c + a * (b + b) := 
    by equate  

    /- Comparison of proof lengths. -/
    lemma e1 : (x+y)^2+(x+z)^2 = (z+x)^2+(y+x)^2 := by equate
    #print e1
    lemma e2 : (x+y)^2+(x+z)^2 = (z+x)^2+(y+x)^2 :=
         by ring
    #print e2

end rings
