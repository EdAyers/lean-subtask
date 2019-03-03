import ..equate tactic
open robot
universe u 
section rings
    -- [TODO] one of the examples in `group` is to show this, so there should be a way of telling `equate` to omit rules.
    attribute [equate] neg_sub 

    variables {α : Type u} [comm_ring α] {a b c d e p x y z : α}
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by equate
    example : (a * -d - b * - c) * e = -((a * d - b * c) * e) := 
    by equate
    @[equate] lemma sub_minus : - (a - b) = - a - - b := by equate
    -- comparison with new lemma added
    lemma sumsq_1 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by equate
    lemma sumsq_2 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := 
    by ring

    meta def trace_proof_size : name → tactic unit := λ n, (do
        env ← tactic.get_env,
        declaration.thm n e y p ← environment.get env n,
        p ← pure $ task.get $ p,
        tactic.trace $ expr.size p
    )
    run_cmd (trace_proof_size `sumsq_1)
    run_cmd (trace_proof_size `sumsq_2)
    
    #print sumsq_1
    #print sumsq_2
    -- example : (a + b) * (a - b) = a * a - b * b := 
    -- by equate
    example : (a * d) * b + b * (c * e) = (a * d + c * e) * b := 
    by equate 
    example : a * b + b * c = (a + c) * b := 
    by equate
    example : (a + c) * b = c * b + b * a := by equate
    example : (a + c) * b = c * b + b * a := by ring

    /- In ideals.lean -- `(I : ideal α) : has_mul I.quotient` -/
    example : (a * b - c * d) = b * a - b * c + (b * c - d * c) :=
    by ring


    /- In multiplicity.lean , `finite_mul_aux`. -/
    -- example {a b p s x : α} {n m : ℕ } 
    --     (h₁ : a = p * x) 
    --     (h₂ : a * b = p ^ (n + m + 1) * s)
    -- :   p * (x * b) = p * (p ^ (n - 1 + m + 1) * s) 
    -- := by equate

    example : (a + b) * (a - b) = a * a - b * b := 
    by equate
    example : (a * b) - c + (b * a) = - c + 2 * (a *  b) := 
    by equate  
    example : (a * b) - c + (b * a) = - c + (2 * a) *  b := 
    by equate  
    example : (a * b) - c + (b * a) = - c + a * (b + b) := 
    by equate  

    /- Comparison of proof lengths. -/
    lemma e1 : (x+y)^3+(x+z)^3 = (z+x)^3+(y+x)^3 := by equate
    #print e1
    run_cmd trace_proof_size `e1
    lemma e2 : (x+y)^3+(x+z)^3 = (z+x)^3+(y+x)^3 :=
         by ring
    #print e2
    run_cmd trace_proof_size `e2

end rings
