import .rule .zipper .rule_table
/- Investigating how simp_lemmas works -/

namespace scratch1

constant G : Type
constant p : G → G → G
local infixl ` ∙ `:70 := p
constant e : G
constant i : G → G
variables {x y z : G}
axiom A : (x ∙ y) ∙ z = x ∙ (y ∙ z)
axiom A_rev :  x ∙ (y ∙ z) = (x ∙ y) ∙ z
#check A
axiom IL : x ∙ e = x
axiom IR : e ∙ x = x
axiom NL : e = i(x) ∙ x 
axiom NR : x ∙ i(x) = e
axiom IL_rev : x  = x ∙ e
axiom IR_rev : x = e ∙ x
axiom NL_rev : i(x) ∙ x = e
axiom NR_rev : e = x ∙ i(x)
axiom WTF : x = e → x ∙ x = x
noncomputable instance G_has_mul : has_mul G := ⟨p⟩
constants (a b c : G)
open tactic
open ez ez.zipper

run_cmd (do
    n ← mk_fresh_name,
    let e := `(a * b),
    --get_fun_info (expr.get_app_fn e) >>= trace,
    let x := ez.zipper.zip e,
    ⟨f,zs⟩ ← x.down_proper,
    trace f,
    trace zs,
    -- x ← x.app_left,
    x ← x.app_right,
    zipper.infer_type x >>= trace,
    e ← zipper.with_tactic (do target >>= trace, exact `(b ∙ b)) x,
    trace e,
    --trace (x.unzip_with soz),
    -- trace x.current,
    -- C ← ez.zipper.mk_congr x,
    -- trace C,
    -- infer_type C >>= trace,
    pure ()
)

/- The holdup:
`to_expr` is applying the implicit variables.
Solutions:
- Remake `rule` to be a conversion `F(LHS) = ?X`.
- Keep it as a simp_lemma.
-/

constant α : Type
axiom P : ∀ {a:α}, a = a
run_cmd do
    p ← tactic.resolve_name `P,
    e ← tactic.to_expr p tt ff,
    t ← tactic.infer_type e,
    trace t,
    pure ()


meta def rules := do
    num_goals >>= trace,
    target >>= trace,
    let axs := [``A,``IL,``IR,``NL,``NR, ``WTF],
    axs ← axs.mmap resolve_name,
    axs ← axs.mmap (λ p, to_expr p.mk_explicit tt ff), -- The rule is that if the variables are implicit then `to_expr` of the proof will automatically unfold the telescope.
    axs.mmap infer_type >>= trace,
    axs ← axs.mmap rule.of_prf,
    --revs ← axs.mmap (λ r, rule.flip r),
    pure $ axs --+ revs

run_cmd  rules >>= trace

meta def SLs := 
    pure [``A,``IL,``IR,``NL,``NR, ``A_rev,``IL_rev,``IR_rev,``NL_rev,``NR_rev] 
    >>= list.mmap (λ x, 
            resolve_name x
            >>= (pure ∘ pexpr.mk_explicit)
            >>= to_expr
            >>= rule.of_prf
        )
    >>= (pure ∘ rule_table.of_rules)

-- meta def traverse_congruence :=
-- do
--     let fn := get_app_fn e,
--     let args := get_app_args e,
--     cgr_lemma ← mk_congr_lemma_simp fn (some args.length),
--     -- for each proper argument. (that is, not a type and not a member of a subsingleton and explicit)
universes u v


set_option trace.simp_lemmas true

run_cmd do
    let sl := simp_lemmas.mk,
    sl ←  sl.add_simp ``NL,
    sl ←  sl.add_simp ``IL,
    sl ←  sl.add_simp ``IL_rev,
    sl ←  sl.add_simp ``NL_rev,
    trace sl,
    pure ()

run_cmd do
    sl ← SLs,
    trace sl,
    t ← to_expr ```(Π x :G, true) >>= mk_meta_var,
    exact `(trivial),
    set_goals [t],
    x ← intro `a,
    --trace_state,
    ls ← rule_table.rewrites `(e ∙ %%x) sl,
    trace ls,
    exact `(trivial),
    pure ()
    
run_cmd do sls ← SLs, trace sls

end scratch1