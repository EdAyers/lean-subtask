open tactic

universes u v
section
variables {α : Type u} {β : Type v}

meta def notimpl : α := undefined_core "not implemented"

meta def new_goal : option expr → tactic expr
|none := mk_mvar
|(some e) := mk_meta_var e

/-- `fabricate type s` uses tactic `s` to make an instance of `type`. It saves and restores the goals of the tactic. -/
meta def tactic.fabricate (type : option expr) (strat : tactic unit) : tactic expr := do
    new_g ← new_goal type,
    gs ← get_goals,
    set_goals [new_g],
    strat,
    n ← num_goals,
    when (n≠0) (fail "fabrication failed: there are unsolved goals."),
    set_goals gs,
    instantiate_mvars new_g

/--Throw away the main goal. -/
meta def tactic.ignore : tactic unit := do
    g::gs ← get_goals | pure (),
    set_goals gs

meta def tactic.trace_fail {α} (t : tactic α) : (tactic α) | s :=
    match t s with
    |(interaction_monad.result.exception msg pos _) :=
        let tr : tactic unit := tactic.trace $ ("Exception: ":format) ++ (option.rec_on msg (to_fmt "silent") (λ f, f())) in
        (tr >> t) s
    |r := r
    end


open interaction_monad.result

/--Perform `tac`, but throw away the state afterwards. -/
meta def tactic.hypothetically {α} (tac : tactic α) : tactic (option α) :=
λ s, match tac s with
|(success a s') := (success (some a) s)
|(exception ms pos s') := (success none s) 
end

meta def tactic.hypothetically' {α} (tac : tactic α) : tactic α :=
λ s, match tac s with
|(success a _) := success a s
|(exception ms pos _) := exception ms pos s
end
    -- tactic α = interaction_monad state α = state → result state α

meta def tactic.trace_m {α} [has_to_tactic_format α]: string → α → tactic unit |s a := do ppa ← tactic.pp a, trace $ (to_fmt s) ++ ppa

meta def tactic.try_first {α} : list (tactic α) → tactic α
| []            := failed
| (tac :: tacs) := λ s,
  match tac s with
  | result.success a s' := result.success a s'
  | result.exception e p _ := tactic.try_first tacs s
  end

meta def expr.binding_body_all : expr → option expr
|(expr.pi _ _ _ b) :=  some b
|(expr.lam _ _ _ b) := some b
|(expr.elet _ _ _ b) :=some b
|_ := none

meta def expr.is_mvar : expr → bool
|(expr.mvar _ _ _) := tt
|_ := ff



def list.mcollect {T} [alternative T] (f : α → T β) : list α → T (list β)
|[] := pure []
|(h::t) := pure (λ fh rest, option.cases_on fh rest (λ fh,fh::rest)) 
            <*> (some <$> f h <|> pure none) 
            <*> list.mcollect t

private def map_with_rest_aux (m : α → list α → β) : list α → list α → list β → list β
| left [] acc := acc.reverse
| left (a::right) acc := map_with_rest_aux (a::left) right (m a (left.foldl (λ l x, x :: l) right) :: acc)

def list.map_with_rest (m : α → list α → β) : list α → list β := λ right, map_with_rest_aux m [] right []
end
structure writer_t (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : m (α × σ))
attribute [pp_using_anonymous_constructor] writer_t
namespace writer_t
        variables {σ : Type u} [monoid σ] {m : Type u → Type v} [monad m] 
        variables {α β : Type u}
        @[inline] protected def pure (a : α) : writer_t σ m α := ⟨pure ⟨a,1⟩⟩
        @[inline] protected def bind (x : writer_t σ m α) (f : α → writer_t σ m β) : writer_t σ m β := 
        ⟨do ⟨a,s₁⟩ ← x.run, ⟨b,s₂⟩ ← (f a).run, pure ⟨b, s₁ * s₂⟩ ⟩
        instance : monad (writer_t σ m) := {pure:=λ α, writer_t.pure, bind := λ α β, writer_t.bind}
        protected def orelse [alternative m] {α : Type u} (x₁ x₂ : writer_t σ m α) : writer_t σ m α :=
        ⟨run x₁ <|> run x₂⟩
        protected def failure [alternative m] : writer_t σ m α := ⟨failure⟩
        instance [alternative m] : alternative (writer_t σ m) := {failure := λ α, writer_t.failure, orelse := λ α, writer_t.orelse}
        def log (msg : σ) : writer_t σ m punit := ⟨pure ⟨⟨⟩,msg⟩⟩
        @[inline] protected def lift (t : m α) : writer_t σ m α := ⟨(λ a, ⟨a,1⟩) <$> t⟩
        instance : has_monad_lift m (writer_t σ m) := ⟨λ α, writer_t.lift⟩
end writer_t

section
    variables {T : Type u → Type u} [monad T] {α β γ : Type u} (p : α → T (β ⊕ γ))
    def list.mpartition : list α → T (list β × list γ):= λ l, do 
        ⟨xs,ys⟩ ← l.mfoldl (λ (xsys : list β × list γ) a, do 
            ⟨xs,ys⟩ ← pure xsys,
            r ← p a, 
            pure $ sum.rec_on r (λ x, ⟨x::xs,ys⟩) (λ y, ⟨xs,y::ys⟩)
        ) (⟨[],[]⟩), 
        pure ⟨xs.reverse,ys.reverse⟩
end

namespace test
    meta def assert (test : bool) (msg : option string := none) : tactic unit := when (¬test) $ fail $ option.get_or_else msg "Assertion failed"
    meta def equal {α} [decidable_eq α] [has_to_tactic_format α] (expected actual : α) (msg : format := "") : tactic unit := when (expected ≠ actual) $ do
        epp ← pp expected,
        app ← pp actual,
        fail $ (to_fmt "Assertion failed: \nexpected: ") ++ format.nest 10 epp ++ "\n  actual: " ++ format.nest 10 app ++ "\n" ++ msg
    -- [TODO] `meta def snapshot` would be the dream. You could do this by dumping the to_tactic_format code to a text file and then reading it back using io. I guess you would also need a monad called test.
end test

