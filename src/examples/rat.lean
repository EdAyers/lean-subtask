import ..tests
namespace rats

meta def equate := tests.equate
universes u
structure q (α : Type u) [integral_domain α] := (n : α) (d : α ) (nz : d ≠ 0)
lemma q.ext {α : Type u} [integral_domain α] : Π (q1 q2 : q α), q1.n = q2.n → q1.d = q2.d → q1 = q2
|⟨n,d,nz⟩ ⟨_,_,_⟩ rfl rfl := rfl

instance (α : Type u) [integral_domain α] : setoid (q α) :=
{ r := (λ a b, a.1 * b.2 = b.1 * a.2)
, iseqv := 
  ⟨ λ a, rfl
  , λ a b, eq.symm
  , λ ⟨n₁,d₁,_⟩ ⟨n₂,d₂,h⟩ ⟨n₃,d₃,_⟩ (p : n₁ * d₂ = n₂ * d₁) (q : n₂ * d₃ = n₃ * d₂),
     suffices d₂ * (n₁ * d₃) = d₂ * (n₃ * d₁), from eq_of_mul_eq_mul_left h this,
     by equate
    -- calc
    --   d₂ * (n₁ * d₃) = (n₁ * d₂) * d₃ : by ac_refl -- 1
    --             ...  = (n₂ * d₁) * d₃ : by rw p    -- 1
    --             ...  = (n₂ * d₃) * d₁ : by ac_refl -- 3
    --             ...  = (n₃ * d₂) * d₁ : by rw q    -- 1
    --             ...  = d₂ * (n₃ * d₁) : by ac_refl -- 2 = 8
  ⟩
}
def free (α : Type u) [integral_domain α] : Type* := @quotient (q α) (by apply_instance)
variables {α : Type u} [integral_domain α]

namespace free
def add : free α → free α → free α 
:= λ x y, quotient.lift_on₂ x y 
  (λ x y, ⟦(⟨x.1 * y.2 + y.1 * x.2, x.2 * y.2, mul_ne_zero x.nz y.nz⟩ : q α)⟧) 
  (λ a1 a2 b1 b2,
      assume p : a1.1 * b1.2 = b1.1 * a1.2,
      assume q : a2.1 * b2.2 = b2.1 * a2.2,
      suffices (a1.1 * a2.2 + a2.1 * a1.2) * (b1.2 * b2.2) = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2), 
        from quotient.sound this,
         sorry
      -- calc ((a1.1 * a2.2) + (a2.1 * a1.2)) * (b1.2 * b2.2) = ((a1.1 * a2.2) * (b1.2 * b2.2) + (a2.1 * a1.2) * (b1.2 * b2.2)) : by equate
      --                                             ...  = ((a1.1 * b1.2) * (a2.2 * b2.2) + (b1.2 * a1.2) * (a2.1 * b2.2)) : begin clear p q, equate end
      --                                             ...  = ((b1.1 * a1.2) * (a2.2 * b2.2) + (b1.2 * a1.2) * (b2.1 * a2.2)) : by equate
      --                                             ...  = (((b1.1 * b2.2)* (a1.2 * a2.2)) + ((b2.1 * b1.2) * (a1.2 * a2.2)))   : by ac_refl
      --                                             ...  = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2)                     : by apply eq.symm; apply integral_domain.right_distrib
  )
end free

end rats