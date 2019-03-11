/- Author: E.W.Ayers © 2019 -/
namespace parseval
noncomputable theory
constant α : Type
variables {x y z : α} {f g : α → α}
instance : comm_ring α := sorry
constant expectation : (α → α) → α
notation `𝔼` binders `, ` r:(scoped f, expectation f) := r
constant conj : α → α
constant conj_1 : conj (x + y) = conj(x) + conj(y)
constant conj_2 : conj (x * y) = conj(x) * conj(y)
constant conj_3 : conj (conj x) = x
constant conj_4 : conj (expectation f) = expectation (conj ∘ f)
constant conj_5 : conj (-x) = -conj(x)

constant expectation_scalar_lin : x * (𝔼 y, f y) = (𝔼 y, x * f y)
constant expectation_comm {f : α → α → α} : (𝔼 x, 𝔼 y, f x y) = (𝔼 y, 𝔼 x, f x y)
constant expectation_dist : (𝔼 x, f x + g x) = (𝔼 x, f x) + (𝔼 x, g x)

def fourier (f : α → α) (χ : α → α) := 𝔼 x : α, f(x) * χ(-x)  
notation `ℱ` := fourier

def character :=
    {  χ : α → α 
    // (∀ x, conj (χ x) = χ(-x))
    ∧  (∀ x y, χ(x) * χ(y) = χ(x + y))
    }
instance : has_coe_to_fun (character) := ⟨λ _, α → α,λ χ x, χ.val x⟩
variables {χ : character}
lemma char_conj : conj (χ x) = χ (- x) := χ.property.1 _

constant charsum : (((α → α) → α) → α)
notation `∑` binders `, ` r:(scoped f, charsum f) := r

constant dirac_delta : α → α → α
notation `Δ` := dirac_delta
axiom dd_elim {f : α → α → α} : (𝔼 x, 𝔼 y, f x y * Δ x y) = 𝔼 x, f x x
axiom dd_intro : (∑ χ, χ(x - y)) = Δ x y

constant fourier_def (f χ : α → α) : (ℱ f χ) = 𝔼 x, f(x) * (χ(-x))
def i_p_1 (f g : (α → α) → α) := ∑ χ, f χ * conj (g χ)
def i_p_2 (f g : α → α) := 𝔼 x, f(x) * conj(g(x))
example (f g : _) : i_p_1 (fourier f) (fourier g) = i_p_2 f g := sorry

end parseval