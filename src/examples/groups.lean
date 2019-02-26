import ..equate
open robot
universe u

attribute [equate] is_group_hom.mul

section additive_groups 
    variables {α : Type u} [add_comm_group α] {u v w x y z : α}
    example : (x + y) + z = (z + x) + y := 
    by equate
    example : x + y + z = z + x + y := 
    by equate
    example : x + (y - z) = -z + y + x := 
    by equate
    example : x - (y + z) = x - y - z := 
    by equate
    example : - (x - y) = y + - x := 
    by equate
    example : - (x - y) = y - x := 
    by equate
    example : (x - y) = -(y - x) := 
    by equate
    example : (x + y) + (z + w) = (x + z) + (y + w) := 
    by equate
    example : v + u + (x + y) + (z + w) = (x + z) + (y + w) + v + u := 
    by equate
    lemma X1 : x + y + z + u + v + w = w + (x + y + z + u + v) := 
    by equate
    #print X1
    lemma X2 : x + y + z + u + v + w = w + (x + y + z + u + v) := 
    by (tactic.timetac "ac_refl" $ tactic.ac_refl)
    #print X2
end additive_groups

section powers
    variables {M : Type u} [monoid M] {a : M} {n m : ℕ}
    @[equate] lemma my_pow_mul_comm' : a^n * a = a * a^n :=
    begin
        induction n,
        simp,
        equate
    end
    @[equate] lemma my_pow_succ' : a^(n+1) = a^n * a :=
    by equate
    @[equate] lemma my_pow_1 : a^1 = a := by equate
    @[equate] lemma my_pow_2 : a^2 = a * a := by equate
    @[equate] lemma my_pow_add : a^(m + n) = a^m * a^n :=
    begin
        induction m, 
        simp,
        equate
    end
    @[equate] lemma my_one_pow : (1:M)^n = (1:M) :=
    begin
        induction n,
        simp, equate
    end
    @[equate] lemma my_pow_mul : (a^n)^m = a^(n * m) := 
    begin
        induction m, 
        simp,
        equate
    end
    @[equate] lemma my_pow_mul_comm : (a^n) * (a^m) = (a^m) * (a^n)
    := by equate
end powers

section comm_monoid_powers
    variables {M:Type u} [comm_monoid M] {a b c : M} {n m : ℕ}
    @[equate] lemma my_mul_pow : (a * b)^n = a^n * b^n
    := begin
        induction n,
        simp,
        equate
    end
end comm_monoid_powers

section group_powers
    variables {G : Type u} [group G] {a b c : G} {n m : ℕ}
    @[equate] lemma my_inv_pow : (a⁻¹)^n = (a^n)⁻¹ :=
    begin
        induction n,
        simp,
        equate
    end 
end group_powers

section group_homs1
    variables {H G : Type u} [group H] [group G] {φ : H → G} {ψ : G → H} {x y z h : G}
    example : (x * z) * (z⁻¹ * y) = x * y
    := by equate
    example : x * y = (x * z) * (z⁻¹ * y)
    := by equate
    def conj (h x : G) := h * x * h ⁻¹ 
    @[equate] lemma conj_def : conj h x = h * x * h ⁻¹ := rfl
    example {h : G} : conj h (x) * conj h (y) = conj h (x * y) := 
    by equate
    example {h : G} : conj h (x * y) = conj h x * conj h y := 
    by equate
    example : x * y⁻¹ = (y * x⁻¹)⁻¹
    := by equate
    example :  (y * x⁻¹)⁻¹ = x * y⁻¹
    := by equate
    example [is_group_hom φ] [is_group_hom ψ] {x y : G} 
        : is_group_hom (φ ∘ ψ) := ⟨λ x y, by equate⟩
    example 
        [is_group_hom φ] 
        (i1 : ∀ x, φ(ψ x) = x) 
        (i2 : ∀ x, ψ(φ x) = x) {x y : G} 
        : is_group_hom ψ :=
    ⟨λ a b, by equate⟩ -- [FIXME] this usually works I promise
end group_homs1

section group_homs3
    lemma is_group_hom_mul_2 {α β} [group α] [comm_group β]
    (f g : α → β) [is_group_hom f] [is_group_hom g] :
    is_group_hom (λa, f a * g a) :=
    ⟨assume a b, by equate⟩ -- [FIXME] when apply_core uses is_group_hom.mul it's using the wrong typeclass instance!!
    #print is_group_hom_mul_2
end group_homs3




