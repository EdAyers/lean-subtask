import .engine .policy
/- A prototype version of the tactic. -/

namespace robot


namespace group_theory
    universes u
    variables {H : Type u} [group H] {x y z : H} 
    def A : (x * y) * z = x * (y * z) := by apply mul_assoc
    def NL : x ⁻¹ * x = 1 := by apply mul_left_inv
    def NR : x * x ⁻¹ = 1 := by apply mul_right_inv
    def IR : 1 * x = x := by apply one_mul
    def IL : x * 1 = x := by apply mul_one

    def is_hom {G H : Type u} [group G] [group H] (f : G → H) := ∀ x y, f (x * y) = f x * f y
    
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
    def A1 : (x + y) + z = x + (y + z) := by apply add_assoc
    def A2L : - x + x = 0 := by apply add_left_neg
    def A2R : x + - x = 0 := by apply add_right_neg
    def A2SS : x - y = x + - y := by simp
    def AIM : - (x + y) = (-x + - y) := by simp
    def AIM2 : ( - x - - y) = - (x - y) := by simp
    def A3L : 0 + x = x := by apply zero_add
    def A3R : x + 0 = x := by apply add_zero
    def A4 : x + y = y + x := by apply add_comm
    def is_hom (f : A → B) := ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂
    meta def rules := rule_table.of_names [ 
        ``A1, ``A2L, ``A2R, ``A3L, ``A3R, ``A4, ``A2SS, 
        ``AIM,
        ``AIM2
        ]
end add_grp_theory

namespace ring_theory
    universe u
    variables {R : Type u} [comm_ring R] {x y z a b c : R}
    def M1 : (x * y) * z = x * (y * z) := by apply mul_assoc
    def M3L : 1 * x = x := by apply one_mul
    def M3R : x * 1 = x := by apply mul_one
    def M4 : x * y = y * x := by apply mul_comm
    def S1 : (- x) * y = - (x * y) := by simp
    def S2 : x * -y = - (x * y) := by simp
    def D1 : x * (y + z) = (x * y) + (x * z) := by apply left_distrib
    def D2 : (y + z) * x = y * x + z * x := by apply right_distrib
    meta def rules : tactic rule_table := do r1 ← rule_table.of_names [
        ``M1, ``M3L, ``M3R, ``M4, ``D1, ``D2, ``S1, ``S2
    ], r2 ← add_grp_theory.rules, rule_table.join r1 r2
end ring_theory

namespace set_rules
    universe u
    variables {α : Type u} {A B C : set α}
    instance : has_sub (set α) := ⟨λ A B, A ∩ (- B)⟩
    def ext : (∀ a, a ∈ A ↔ a ∈ B) → A = B := begin intro, funext, rw <-iff_eq_eq, apply a x end
    def A1 : A - B = A ∩ (- B) := rfl
    def A2 : - ( B ∩ C ) = -B ∪ -C := ext $ λ a, ⟨λ h, classical.by_cases (λ aB, classical.by_cases (λ aC, absurd (and.intro aB aC) h) or.inr ) or.inl,λ h, or.cases_on h (λ h ⟨ab,_⟩, absurd ab h) (λ h ⟨_,ac⟩, absurd ac h)⟩
    def A3 :  - ( B ∪ C ) = - B ∩ - C := ext $ λ a, ⟨λ h, ⟨h ∘ or.inl,h ∘ or.inr⟩, λ ⟨x,y⟩ h₂, or.cases_on h₂ x y⟩ 
    def A4 : B ∩ C = C ∩ B := ext $ λ a, ⟨and.swap,and.swap⟩
    def A5 : B ∪ C = C ∪ B := ext $ λ a, ⟨or.swap, or.swap⟩
    def A6 : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := ext $ λ a, ⟨λ h, or.cases_on h (λ h, ⟨or.inl h, or.inl h⟩) (λ ⟨b,c⟩, ⟨or.inr b, or.inr c⟩),λ ⟨ab,ac⟩, or.cases_on ab or.inl $ λ b, or.cases_on ac or.inl $ λ c, or.inr ⟨b,c⟩⟩ -- [NOTE] use mathlib, don't be macochistic.
    def A7 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := ext $ λ a, ⟨λ ⟨a,bc⟩,or.cases_on bc (λ b, or.inl ⟨a,b⟩) (λ c, or.inr ⟨a,c⟩), λ h, or.cases_on h (λ ⟨a,b⟩, ⟨a,or.inl b⟩) (λ ⟨a,c⟩, ⟨a,or.inr c⟩)⟩
    def A8 : (A ∩ B) ∩ C = A ∩ (B ∩ C)  := ext $ λ a, and.assoc
    def A9 : (A ∪ B) ∪ C = A ∪ (B ∪ C)  := ext $ λ a, or.assoc
    def A10 : A ∪ ∅ = A := ext $ λ _, or_false _
    def A11 : A ∩ ∅ = ∅ := ext $ λ _, and_false _
    def A12 : A ∪ set.univ = set.univ := ext $ λ _, or_true _
    def A13 : A ∩ set.univ = A := ext $ λ _, and_true _
    def A14 : A ∩ A = A := ext $ λ a, ⟨λ ⟨x,y⟩, x, λ x, ⟨x,x⟩⟩
    def A15 : A ∪ A = A := ext $ λ a, ⟨λ xy, or.rec_on xy id id, or.inl⟩
    meta def rules := rule_table.of_names [
        ``A1, ``A2, ``A3, ``A4, ``A5, ``A6, ``A7, ``A8, ``A9
        , ``A10, ``A11, ``A12, ``A13, ``A14, ``A15
    ]
end set_rules
namespace list_theory
    universe u
    open list
    variables {α : Type u} {a h : α} {l t : list α}
    def nil_append : [] ++ l = l := rfl
    def append_cons : (h::t) ++ l = h:: (t ++ l) := rfl
    def rev_nil : reverse ([] : list α) = [] := rfl
    def append_nil : l ++ [] = l := begin induction l, refl, simp end
    -- [HACK] taken from mathlib
    theorem rev_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] := 
    begin
            have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]),
            intro l₁, induction l₁, intros, refl,
            intro, 
            simp only [*, reverse_core, cons_append], 
            symmetry, apply aux
    end

    meta def rules := rule_table.of_names [``append_nil, ``append_cons, ``rev_nil, ``rev_cons, ``nil_append]

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
    axiom L1 {A : V → V} : is_linear A → A (x + y) = A x + A y
    axiom L2 {A : V → V}: is_linear A → μ • A x = A (μ • x)
    axiom SS : μ • ν • x = (μ * ν) • x
    axiom LL : μ • (x + y) = μ • x + μ • y
    constant ip : V → V → k
    notation `⟪` x `,` y `⟫`  := ip x y
    axiom ipL : ⟪x + y,z⟫ = ⟪x,z⟫ + ⟪y,z⟫
    axiom ipR : ⟪x, y + z⟫ = ⟪x,y⟫ + ⟪x,z⟫
    axiom ipSL : ⟪μ • x,z⟫ = μ * ⟪x,z⟫
    axiom ipSR : ⟪x,μ • z⟫ = μ * ⟪x,z⟫
    axiom ADJ : is_linear A → ⟪A† x, y ⟫ = ⟪x, A y⟫
    axiom COMP_DEF {α β γ} {f : β → γ} {g : α → β} {x : α} : (f ∘ g) x = f (g x)
    meta def rulenames := [
        ``L1, ``L2,``SS, ``LL, ``ipL, ``ipR,``ipSL,``ipSR,``ADJ,
        ``COMP_DEF
        ]
    /-- [TODO] is there a way to cache this? -/
    meta def rules : tactic rule_table :=
        [rule_table.of_names rulenames, 
            ring_theory.rules, 
            set_rules.rules, 
            list_theory.rules
        ].mfoldl (λ acc rt, rt >>= λ rt, rule_table.join rt acc) (rule_table.empty)

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

    run_cmd rules >>= trace

end vector_theory

run_cmd (vector_theory.rules >>= tactic.trace)


meta def equate (names : list name := []) := do
    base ← vector_theory.rules,
    bonus ← rule_table.of_names names,
    all ← rule_table.join bonus base,
    tactic.timetac "equate" $ robot.run robot.score_policy all


end robot