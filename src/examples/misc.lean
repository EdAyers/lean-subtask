import ..equate
open robot

constant p : ℕ → ℕ → ℕ
constant f : ℕ → ℕ
@[equate] axiom pf : ∀ {a}, p (f a) (f a) = p a a
-- [TODO] its revisiting itself for some odd reason.
lemma ex2 (a b : ℕ) (q : a = b) : p (f a) (f b) = p a b := by equate