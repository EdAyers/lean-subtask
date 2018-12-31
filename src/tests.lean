import .data
open robot
namespace tests

    /- Simple group theory axiomatisation for testing. -/
    namespace G_theory
        constant G : Type
        constant p : G → G → G
        local infixl ` ∙ `:70 := p
        constant e : G
        constant i : G → G
        constant a : G -- just an element.
        variables {x y z : G}
        axiom A : (x ∙ y) ∙ z = x ∙ (y ∙ z)
        axiom IL : x ∙ e = x
        axiom IR : e ∙ x = x
        axiom NL : e = i(x) ∙ x 
        noncomputable instance : group G := {mul := p, one := e, inv := i, mul_assoc := λ _ _ _ ,A, one_mul:= λ _,IR, mul_one:=λ _,IL, mul_left_inv:=λ _,eq.symm NL}
        -- axiom A_rev :  x ∙ (y ∙ z) = (x ∙ y) ∙ z
        -- axiom IL_rev : x  = x ∙ e
        -- axiom IR_rev : x = e ∙ x
        -- axiom NL_rev : i(x) ∙ x = e
        -- axiom NR_rev : e = x ∙ i(x)
        open tactic
        meta def rules : tactic rule_table := rule_table.of_names [``A,``IL,``IR,``NL]

        -- test the rule table is created correctly. [TODO] add assertions.
        run_cmd (do rs ← rules, trace rs, skip)

        -- test rule_table.rewrites
        run_cmd (do
            rs ← rules,
            t ← to_expr ```(Π x:G, true) >>= mk_meta_var,
            triv,
            set_goals [t],
            x ← intro `a,
            ls ← rule_table.rewrites `((e ∙ %%x) ∙ %%x) rs,
            test.equal ls.length 12,
            -- trace ls,
            skip
        )




    end G_theory

    namespace group_theory
        universes u
        variables {H : Type u} [group H] {x y z : H} 
        def A : (x * y) * z = x * (y * z) := by apply mul_assoc
        def NL : x ⁻¹ * x = 1 := by apply mul_left_inv
        def NR : x * x ⁻¹ = 1 := by apply mul_right_inv
        def IR : 1 * x = x := by apply one_mul
        def IL : x * 1 = x := by apply mul_one
        open tactic
-- set_option pp.all true
        
        meta def rules := rule_table.of_names [``A,`NL,`NR,`IR,`IL]
        -- test submatches
        run_cmd (
            do rs ← rules
            ,  let e := `(G_theory.a * 1)
            ,  subs ← rule_table.submatch e rs
            ,  trace subs
            ,  test.equal subs.length 3

        )
        -- test head-match and rewrites.
        run_cmd (do
            rs ← rules,
            il ← rule.of_name `IL,
            t ← to_expr ```(Π {G : Type u} [group G] (x:G), true) >>= mk_meta_var,
            triv,
            set_goals [t],
            [G,_,x] ← intros,
            -- trace_state,
            ls ← rule_table.rewrites x rs,
            test.equal ls.length 2,
            e ← to_expr $ ```(%%x * 1),
            ls ← rule.head_rewrite il e,
            ls ← rs.rewrites e,
            test.equal ls.length 7,
            --trace ls,
            skip
        )

    end group_theory


    namespace vector_theory
        universes u
        constant k : Type
        constant is_field : field k
        noncomputable instance : field k := is_field
        constant V : Type
        constant is_ab : add_comm_group V
        noncomputable instance : add_comm_group V := is_ab
        constant p : k → V → V
        infixr `•`: 100 := p
        constant is_linear : (V → V) → Prop
        constant adj : (V → V) → (V → V)
        variables {μ ν : k} {x y z : V} {A : V → V}
        postfix `†`:200 := adj
        axiom L1 : is_linear A → A (x + y) = A x + A y
        axiom L2 : is_linear A → μ • A x = A (μ • x)
        axiom SS : μ • ν • x = (μ * ν) • x
        axiom LL : μ • (x + y) = μ • x + μ • y
        constant ip : V → V → k
        notation `⟪` x `,` y `⟫`  := ip x y
        axiom ipL : ⟪x + y,z⟫ = ⟪x,z⟫ + ⟪y,z⟫
        axiom ipR : ⟪x, y + z⟫ = ⟪x,y⟫ + ⟪x,z⟫
        axiom ipSL : ⟪μ • x,z⟫ = μ * ⟪x,z⟫
        axiom ipSR : ⟪x,μ • z⟫ = μ * ⟪x,z⟫

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
          skip
    end vector_theory

end tests

    