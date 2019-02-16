import ..equate
open robot
universe u 
section rings
    variables {α : Type u} [comm_ring α] {a b c d e : α}
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by equate
    -- example : (a + b) * (a - b) = a * a - b * b := 
    -- by equate
    example : (a * -d - b * - c) * e = -((a * d - b * c) * e) := 
    by equate
    example : (a * d) * b + b * (c * e) = (a * d + c * e) * b := 
    by equate 
    example : a * b + b * c = (a + c) * b := 
    by equate
    example : (a * b) - c + (b * a) = - c + (a * b + a * b) := 
    by equate  
    example : (a + c) * b = a * b + b * c := 
    by equate
end rings
