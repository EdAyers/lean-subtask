import .engine .policy
import algebra.group_power
import tactic.ring
/- A prototype version of the tactic. -/

namespace robot

meta def equate_user_attr : user_attribute rule_table unit :=
{ name := `equate
, descr := "add the given lemma to equate's rule-table."
, cache_cfg := 
    { mk_cache := rule_table.of_names
    , dependencies := []
    }
}

meta def get_equate_rule_table : tactic rule_table :=
    user_attribute.get_cache equate_user_attr

run_cmd attribute.register `robot.equate_user_attr

namespace group_theory
    universes u
    variables {H : Type u} [group H] {x y z : H} 
    @[equate] def A : (x * y) * z = x * (y * z) := by apply mul_assoc
    @[equate] def NL : x ⁻¹ * x = 1 := by apply mul_left_inv
    @[equate] def NR : x * x ⁻¹ = 1 := by apply mul_right_inv
    @[equate] def IR : 1 * x = x := by apply one_mul
    @[equate] def IL : x * 1 = x := by apply mul_one

    --@[equate] def is_hom {G H : Type u} [group G] [group H] (f : G → H) := ∀ x y, f (x * y) = f x * f y
    
    open tactic
    -- set_option pp.all true
    
    -- meta def rules := rule_table.of_names [``A,`NL,`NR,`IR,`IL]
    -- -- test submatches
    -- run_cmd (
    --     do rs ← rules
    --     ,  let e := `(G_theory.a * 1)
    --     ,  subs ← rule_table.submatch e rs
    --     ,  trace subs
    --     ,  test.equal subs.length 3
    -- )
    -- -- test head-match and rewrites.
    -- run_cmd (do
    --     rs ← rules,
    --     il ← rule.of_name `IL,
    --     t ← to_expr ```(Π {G : Type u} [group G] (x:G), true) >>= mk_meta_var,
    --     triv,
    --     set_goals [t],
    --     [G,_,x] ← intros,
    --     -- trace_state,
    --     ls ← rule_table.rewrites x rs {wilds := tt},
    --     test.equal ls.length 2,
    --     e ← to_expr $ ```(%%x * 1),
    --     ls ← rule.head_rewrite il e,
    --     ls ← rs.rewrites e {wilds := tt},
    --     test.equal ls.length 7,
    --     --trace ls,
    --     skip
    -- )

end group_theory

namespace add_grp_theory 
    universe u
    variables {A : Type u} [add_comm_group A] {x y z : A}
    variables {B : Type u} [add_comm_group B]
    @[equate] def A1 : (x + y) + z = x + (y + z) := by apply add_assoc
    @[equate] def A2L : - x + x = 0 := by apply add_left_neg
    @[equate] def A2R : x + - x = 0 := by apply add_right_neg
    @[equate] def A2SS : x - y = x + - y := by simp
    @[equate] def AIM : - (x + y) = (-x + - y) := by simp
    @[equate] def AIM2 : ( - x - - y) = - (x - y) := by simp
    @[equate] def A3L : 0 + x = x := by apply zero_add
    @[equate] def A3R : x + 0 = x := by apply add_zero
    @[equate] def A3Z : x - 0 = x := by simp
    @[equate] def A4 : x + y = y + x := by apply add_comm
    --@[equate] def is_hom (f : A → B) := ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂
end add_grp_theory

namespace ring_theory
    universe u
    variables {R : Type u} [comm_ring R] {x y z a b c : R}
    @[equate] def M1 : (x * y) * z = x * (y * z) := by apply mul_assoc
    @[equate] def M3L : 1 * x = x := by apply one_mul
    @[equate] def M3R : x * 1 = x := by apply mul_one
    @[equate] def M4 : x * y = y * x := by apply mul_comm
    @[equate] def S1 : (- x) * y = - (x * y) := by simp
    @[equate] def S2 : x * -y = - (x * y) := by simp
    @[equate] def D1 : x * (y + z) = (x * y) + (x * z) := by apply left_distrib
    @[equate] def D2 : (y + z) * x = y * x + z * x := by apply right_distrib
    @[equate] def P1 : x ^ 0 = 1 := rfl
    @[equate] def P2 {n} : x ^ (nat.succ n) = x * x ^ n := rfl
    @[equate] def X2 : 2 * x = x + x  := by ring
end ring_theory

namespace set_rules
    universe u
    variables {α : Type u} {A B C : set α}
    --instance : has_sub (set α) := ⟨λ A B, A ∩ (- B)⟩
    def ext : (∀ a, a ∈ A ↔ a ∈ B) → A = B := begin intro, funext, rw <-iff_eq_eq, apply a x end
    @[equate] def A1 : A \ B = A ∩ (- B) := rfl
    @[equate] def A2 : - ( B ∩ C ) = -B ∪ -C := ext $ λ a, ⟨λ h, classical.by_cases (λ aB, classical.by_cases (λ aC, absurd (and.intro aB aC) h) or.inr ) or.inl,λ h, or.cases_on h (λ h ⟨ab,_⟩, absurd ab h) (λ h ⟨_,ac⟩, absurd ac h)⟩
    @[equate] def A3 :  - ( B ∪ C ) = - B ∩ - C := ext $ λ a, ⟨λ h, ⟨h ∘ or.inl,h ∘ or.inr⟩, λ ⟨x,y⟩ h₂, or.cases_on h₂ x y⟩ 
    @[equate] def A4 : B ∩ C = C ∩ B := ext $ λ a, ⟨and.swap,and.swap⟩
    @[equate] def A5 : B ∪ C = C ∪ B := ext $ λ a, ⟨or.swap, or.swap⟩
    @[equate] def A6 : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := ext $ λ a, ⟨λ h, or.cases_on h (λ h, ⟨or.inl h, or.inl h⟩) (λ ⟨b,c⟩, ⟨or.inr b, or.inr c⟩),λ ⟨ab,ac⟩, or.cases_on ab or.inl $ λ b, or.cases_on ac or.inl $ λ c, or.inr ⟨b,c⟩⟩ -- [NOTE] use mathlib, don't be macochistic.
    @[equate] def A7 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := ext $ λ a, ⟨λ ⟨a,bc⟩,or.cases_on bc (λ b, or.inl ⟨a,b⟩) (λ c, or.inr ⟨a,c⟩), λ h, or.cases_on h (λ ⟨a,b⟩, ⟨a,or.inl b⟩) (λ ⟨a,c⟩, ⟨a,or.inr c⟩)⟩
    @[equate] def A8 : (A ∩ B) ∩ C = A ∩ (B ∩ C)  := ext $ λ a, and.assoc
    @[equate] def A9 : (A ∪ B) ∪ C = A ∪ (B ∪ C)  := ext $ λ a, or.assoc
    @[equate] def A10 : A ∪ ∅ = A := ext $ λ _, or_false _
    @[equate] def A11 : A ∩ ∅ = ∅ := ext $ λ _, and_false _
    @[equate] def A12 : A ∪ set.univ = set.univ := ext $ λ _, or_true _
    @[equate] def A13 : A ∩ set.univ = A := ext $ λ _, and_true _
    @[equate] def A14 : A ∩ A = A := ext $ λ a, ⟨λ ⟨x,y⟩, x, λ x, ⟨x,x⟩⟩
    @[equate] def A15 : A ∪ A = A := ext $ λ a, ⟨λ xy, or.rec_on xy id id, or.inl⟩

end set_rules
namespace list_theory
    universe u
    open list
    variables {α : Type u} {a h : α} {l t : list α}
    @[equate] def nil_append : [] ++ l = l := rfl
    @[equate] def append_cons : (h::t) ++ l = h:: (t ++ l) := rfl
    @[equate] def rev_nil : reverse ([] : list α) = [] := rfl
    @[equate] def append_nil : l ++ [] = l := begin induction l, refl, simp end
    -- [HACK] taken from mathlib
    @[equate] theorem rev_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] := 
    begin
            have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]),
            intro l₁, induction l₁, intros, refl,
            intro, 
            simp only [*, reverse_core, cons_append], 
            symmetry, apply aux
    end
end list_theory

namespace vector_theory
    universes u

    -- variables {k : Type u} [field k] {μ ν : k}
    -- variables {V : Type u} [add_comm_group V] {x y z : V}

    -- class has_scalar_prod (k : Type u) (V : Type u) :=
    -- (scalar_prod : k → V → V)
    -- infixr ` • `:100 := has_scalar_prod.scalar_prod
    
    -- class vector_space (k : Type u) [field k] (V : Type u) [add_comm_group V] extends has_scalar_prod k V :=
    -- (scalar_dist {μ : k} {x y : V} : μ • (x + y) = μ • x + μ • y)
    -- (scalar_dist {μ ν: k} {x : V} : μ • (x + y) = μ • x + μ • y)
    -- (scalar_mul {μ ν : k} {x : V} : (μ * ν) • x = μ • ν • x)


    constant k : Type
    constant V : Type
    constant k_f : field k
    noncomputable instance : field k := k_f
    constant V_ac : add_comm_group V
    noncomputable instance : add_comm_group V := V_ac

    constant p : k → V → V
    infixr ` • `: 100 := p
    constant is_linear : (V → V) → Prop
    constant adj : (V → V) → (V → V)
    variables {μ ν : k} {x y z : V} {A : V → V}
    postfix `†`:200 := adj
    @[equate] axiom L1 {A : V → V} : is_linear A → A (x + y) = A x + A y
    @[equate] axiom L2 {A : V → V}: is_linear A → μ • A x = A (μ • x)
    @[equate] axiom SS : μ • ν • x = (μ * ν) • x
    @[equate] axiom LL : μ • (x + y) = μ • x + μ • y
    constant ip : V → V → k
    notation `⟪` x `,` y `⟫`  := ip x y
    @[equate] axiom ipL : ⟪x + y,z⟫ = ⟪x,z⟫ + ⟪y,z⟫
    @[equate] axiom ipR : ⟪x, y + z⟫ = ⟪x,y⟫ + ⟪x,z⟫
    @[equate] axiom ipSL : ⟪μ • x,z⟫ = μ * ⟪x,z⟫
    @[equate] axiom ipSR : ⟪x,μ • z⟫ = μ * ⟪x,z⟫
    @[equate] axiom ADJ : is_linear A → ⟪A† x, y ⟫ = ⟪x, A y⟫
    @[equate] lemma COMP_DEF {α β γ} {f : β → γ} {g : α → β} {x : α} : (f ∘ g) x = f (g x) := rfl

    open tactic
    open ez.zipper
    run_cmd do
        to_expr ```(Π (A : V → V) (u x y : V),_) >>= assert `h,
        swap, triv,
        [A,u,x,y] ← intros,
        lhs ← to_expr ```(⟪%%A†(%%x + %%y),%%u⟫),
        rhs ← to_expr ```(⟪%%A† %%x + %%A† %%y, %%u⟫),
        zs ← lowest_uncommon_subterms lhs (zip rhs),
        test.equal zs.length 2,
        --   trace_state,
        skip


end vector_theory

run_cmd (get_equate_rule_table >>= tactic.trace)

meta def equate (names : list name := []) := do
    base ← get_equate_rule_table,
    bonus ← rule_table.of_names names,
    all ← rule_table.join bonus base,
    tactic.timetac "time: " $ robot.run robot.score_policy all

end robot