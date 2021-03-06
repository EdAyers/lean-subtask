/- Author: E.W.Ayers © 2019 -/
import ..equate
namespace rats
open robot

/- Example within the context of defining the rationals as ordered pairs of integers
quotiented by the relation (⟨a,b⟩ ~ ⟨c,d⟩) ↔ (a * d = c * b).
 -/

meta def blast : tactic unit :=
tactic.timetac "blast" $ (using_smt_with {cc_cfg := {ac:=ff}} $ tactic.intros >> smt_tactic.iterate (smt_tactic.ematch >> smt_tactic.try smt_tactic.close))
attribute [ematch] mul_comm mul_assoc

universes u
structure q (α : Type u) [integral_domain α] := (n : α) (d : α ) (nz : d ≠ 0)
lemma q.ext {α : Type u} [integral_domain α] : Π (q1 q2 : q α), q1.n = q2.n → q1.d = q2.d → q1 = q2
|⟨n,d,nz⟩ ⟨_,_,_⟩ rfl rfl := rfl

instance (α : Type u) [integral_domain α] : setoid (q α) :=
{ r := (λ a b, a.1 * b.2 = b.1 * a.2)
, iseqv :=
  ⟨ λ a, rfl
  , λ a b, eq.symm
  , λ ⟨a,b,_⟩ ⟨c,d,h⟩ ⟨e,f,_⟩
     (p : a * d = c * b)
     (q : c * f = e * d),
    suffices d * (a * f) = d * (e * b), from eq_of_mul_eq_mul_left h this,
    -- by blast -- takes about 2 seconds
    by equate -- also about 2 seconds, but much slower because implemented in Lean VM
  ⟩
}
def free (α : Type u) [integral_domain α] : Type* := @quotient (q α) (by apply_instance)
variables {α : Type u} [integral_domain α]

-- [TODO]
-- namespace free
-- def add : free α → free α → free α
-- := λ x y, quotient.lift_on₂ x y
--   (λ x y, ⟦(⟨x.1 * y.2 + y.1 * x.2, x.2 * y.2, mul_ne_zero x.nz y.nz⟩ : q α)⟧)
--   (λ a1 a2 b1 b2,
--       assume p : a1.n * b1.d = b1.1 * a1.2,
--       assume q : a2.1 * b2.2 = b2.1 * a2.2,
--       suffices (a1.1 * a2.2 + a2.1 * a1.2) * (b1.2 * b2.2)
--                 = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2),
--         from quotient.sound this,
--         calc ((a1.1 * a2.2) + (a2.1 * a1.2)) * (b1.2 * b2.2)
--               = ((b1.1 * a1.2) * (a2.2 * b2.2) + (b1.2 * a1.2) * (b2.1 * a2.2))
--                 : by equate
--          ...  = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2)
--                 : by symmetry; clear p q; equate
--   )
-- end free

end rats