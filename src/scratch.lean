import .rule
/- Investigating how simp_lemmas works -/

namespace scratch1

constant G : Type
constant p : G → G → G
local infixl ` ∙ `:70 := p
constant e : G
constant i : G → G
variables {x y z : G}
axiom A : (x ∙ y) ∙ z = x ∙ (y ∙ z)
#check A
axiom IL : x ∙ e = x
axiom IR : e ∙ x = x
axiom NL : e = i(x) ∙ x 
axiom NR : x ∙ i(x) = e
axiom WTF : x = e → x ∙ x = x
open tactic

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
    axs ← axs.mmap (λ p, to_expr p tt ff), -- The rule is that if the variables are implicit then `to_expr` of the proof will automatically unfold the telescope.
    axs.mmap infer_type >>= trace,
    axs ← axs.mmap rule.of_prf,
    --revs ← axs.mmap (λ r, rule.flip r),
    pure $ axs --+ revs

run_cmd  rules >>= trace

meta def SLs := pure [``A,``IL,``IR,``NL,``NR] >>= list.mfoldl simp_lemmas.add_simp simp_lemmas.mk

-- meta def traverse_congruence :=
-- do
--     let fn := get_app_fn e,
--     let args := get_app_args e,
--     cgr_lemma ← mk_congr_lemma_simp fn (some args.length),
--     -- for each proper argument. (that is, not a type and not a member of a subsingleton and explicit)


meta def create_lookahead (lem : simp_lemmas) (e : expr) :=
  simp_lemmas.rewrites lem e >>= trace

run_cmd do
    sl ← SLs,
    trace sl,
    create_lookahead sl `((e ∙ e) ∙ (e ∙ e))
    
run_cmd do sls ← SLs, trace sls

end scratch1