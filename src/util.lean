/- Author: E.W.Ayers © 2019 -/
import data.list writer_t
open tactic

/-- Demarcate code as yet to be implemented. -/
meta def notimpl {α} : α := undefined_core "not implemented"

namespace list
    universes u v
    variables {α : Type u} {β : Type v}
    def qsortby {α} (f : α → int) (l : list α) : list α := qsort (λ a b, f a < f b) l
    def mfind {T} [alternative T] {α β} (f : α → T β) : list α → T β
    |[] := failure |(h::t) := f h <|> mfind t
    def bind' : (α → list β) → list α → list β := function.swap list.bind
    /-- Run `f` on each element in the list, return a new list with the values which didn't fail. -/
    def mchoose {T} [alternative T] (f : α → T β) : list α → T (list β)
    |[] := pure []
    |(h::t) := pure (λ fh rest, option.cases_on fh rest (λ fh, fh::rest)) 
                <*> (some <$> f h <|> pure none) 
                <*> mchoose t
    def mcollect {T} [monad T] (f : α → T (list β)) : list α → T (list β)
    |l := mfoldl (λ acc x, (++ acc) <$> f x) [] l
    /-- `skip n l` returns `l` with the first `n` elements removed. If `n > l.length` it returns the empty list. -/
    def skip {α} : ℕ → list α → list α
    |0 l := l
    |(n+1) [] := []
    |(n+1) (h::t) := skip n t
    def maxidx {α} (f : α → int) (l : list α) : option nat :=
        let o := foldl (λ (a : ℕ × option (ℕ×ℤ)) x, 
            let m := f x in 
            prod.mk (a.1 + 1) $ ((a.2 <|> some ⟨a.1,m⟩) 
            >>= (λ p, if m < p.2 then a.2 else some ⟨a.1,m⟩ ))
        ) (0,none) l
        in prod.fst <$> prod.snd o
    /-- Find the maximum according to the given function. -/
    def maxby {α} (f : α → int) (l : list α) : option α := 
    prod.fst <$> foldl (λ (acc : option(α×ℤ)) x, let m := f x in option.cases_on acc (some ⟨x,m⟩) (λ ⟨_,m'⟩, if m < m' then acc else some ⟨x,m⟩)) none l
    def minby {α} (f : α → int) (l : list α) : option α :=
        maxby (has_neg.neg ∘ f) l
    def singleton : α → list α := ( :: [])
    -- def first {α} (f : α → bool) : list α → option α
    -- |[] := none
    -- |(h::t) := if f h then some h else first t 

    def msome {T} [monad T] {α} (f : α → T bool) : list α → T bool
    |[] := pure ff
    |(h::t) := f h >>= λ x, if x then pure tt else msome t
    def collect {β} (f : α → list β) : list α → list β := λ l, bind l f
    def eq_by {α β} (f : α → β → bool) : list α → list β → bool
    |[] [] := tt
    |(h₁::t₁) (h₂::t₂) := f h₁ h₂ && eq_by t₁ t₂
    | _ _ := ff
    /-- Given a relation `f`, check that the two given lists are elementwise true according to `f`.   -/
    def meq_by {T} [monad T] {α β} (f : α → β → T bool) : list α → list β → T bool
    |[] [] := pure tt
    |(h₁::t₁) (h₂::t₂) := do r ← f h₁ h₂, if r then meq_by t₁ t₂ else pure ff
    |_ _ := pure ff
    private def mapi_aux {α β} (f : ℕ → α → β) : ℕ →  list α → list β
    |_ [] := []
    |i (h::t) := (f i h) :: mapi_aux (i+1) t
    /-- Map with the current index. -/
    def mapi {α β} (f : ℕ → α → β) : list α → list β := mapi_aux f 0
    def with_indices {α} : list α → list (ℕ × α) := mapi prod.mk

    private meta def partition_many_aux {α} (equ : α → α → bool) : list α → list (list α) → list (list α) 
    |(h::t) acc := let ⟨eqs,non_eqs⟩ := partition (λ x, equ h x) t in partition_many_aux non_eqs (eqs :: acc)
    |[] acc := acc

    meta def partition_many {α} (equ : α → α → bool) : list α → list (list α)
    | l := partition_many_aux equ l []

    def ohead {α} : list α → option α |(h::t) := some h | [] := none
    def take1 {α} : list α → list α |(h::_) := [h] | [] := []
    private def map_with_rest_aux (m : α → list α → β) : list α → list α → list β → list β
    | left [] acc := acc.reverse
    | left (a::right) acc := map_with_rest_aux (a::left) right (m a (left.foldl (λ l x, x :: l) right) :: acc)
    def map_with_rest (m : α → list α → β) : list α → list β := λ right, map_with_rest_aux m [] right []
    def msplit {T : Type u → Type u} [monad T] {α β γ : Type u} (p : α → T (β ⊕ γ)) 
      : list α → T (list β × list γ)
      | l := do 
        ⟨xs,ys⟩ ← l.mfoldl (λ (xsys : list β × list γ) a, do 
            ⟨xs,ys⟩ ← pure xsys,
            r ← p a, 
            pure $ sum.rec_on r (λ x, ⟨x::xs,ys⟩) (λ y, ⟨xs,y::ys⟩)
        ) (⟨[],[]⟩), 
        pure ⟨xs.reverse,ys.reverse⟩
end list

namespace tactic
    open interaction_monad.result

    private meta def new_goal : option expr → tactic expr
    |none := mk_mvar
    |(some e) := mk_meta_var e

    /-- `fabricate type s` uses tactic `s` to make an instance of `type`. It saves and restores the goals of the tactic. -/
    meta def fabricate (type : option expr) (strat : tactic unit) : tactic expr := do
        new_g ← new_goal type,
        gs ← get_goals,
        set_goals [new_g],
        strat,
        n ← num_goals,
        when (n≠0) (do
            st ← read,
            ppst ← pp st,
            fail $ (to_fmt "fabrication failed, there are unsolved goals:\n") ++ ppst),
        set_goals gs,
        instantiate_mvars new_g
    meta def is_success {α} (t : tactic α) : tactic bool := (t *> pure tt) <|> pure ff
    /-- Throw away the main goal. -/
    meta def ignore : tactic unit := do
        g::gs ← get_goals | pure (),
        set_goals gs

    /-- If the given tactic fails, trace the failure message. -/
    meta def trace_fail {α} (t : tactic α) : (tactic α) | s :=
        match t s with
        |(interaction_monad.result.exception msg pos _) :=
            let tr : tactic unit := 
                tactic.trace $ ("Exception: ":format) 
                ++ (option.rec_on msg (to_fmt "silent") ($ ())) in
            (tr >> t) s
        |r := r
        end
    /-- Attempt to solve the main goal with assumption. Will fail if the main goal is not a prop. -/
    meta def prop_assumption : tactic unit := do
        isp ← target >>= is_prop,
        if isp then assumption else fail "target not a Prop"

    meta def hypothetically' {α} (tac : tactic α) : tactic α :=
    λ s, match tac s with
    |(success a _) := success a s
    |(exception ms pos _) := exception ms pos s
    end
    /-- `trace_m x y` is an alias for `(format.join x <$> pp y) >>= trace`. -/
    meta def trace_m {α} [has_to_tactic_format α]: string → α → tactic unit 
    |s a := do ppa ← pp a, trace $ (to_fmt s) ++ ppa

    /-- Try all of the tactics in the given list and return the result from 
    the first one that doesn't fail. Don't do later tactics. -/
    meta def try_first {α} : list (tactic α) → tactic α
    | []            := failed
    | (tac :: tacs) := λ s,
        match tac s with
        | result.success a s' := result.success a s'
        | result.exception e p _ := try_first tacs s
        end
end tactic

namespace expr  
    /-- If it's a pi, lam or elet, get the body. -/
    meta def binding_body_all : expr → option expr
    |(pi _ _ _ b) :=  some b
    |(lam _ _ _ b) := some b
    |(elet _ _ _ b) :=some b
    |_ := none

    /-- Is it a pi, lambda, app or elet? -/
    meta def is_composite : expr → bool
    := λ e, e.is_pi ∨ e.is_lambda ∨ e.is_app ∨ e.is_let

    -- /-- Fold `f` on all subexpressions. If `f` doesn't fail then all child subexpressions are skipped.-/
    -- meta def mfold2  {T} [monad T] [alternative T]  {α} (f : expr → expr → α → T α) : expr → expr → α → T α :=
    -- λ e₁ e₂ a, f e₁ e₂ a <|> match e₁, e₂ with
    -- |(app f₁ a₁), (app f₂ a₂) := mfold2 f₁ f₂ a >>= mfold2 a₁ a₂
    -- |_,_ := if e₁ = e₂ then pure a else failure -- [TODO] not implemented. 
    -- end
    -- #check const_name

    /-- Get the pretty name if the expression is a const, local_const or mvar. -/
    meta def as_name : expr → option name
    |(local_const unique pretty _ _) := some unique
    |(const n _) := some n
    |(mvar unique pretty _) := some unique
    |_ := none

    meta def as_mvar : expr → option (name × name × expr)
    |(mvar u p y) := some (u,p,y)
    |_ := none

    /-- Count the number of subexpressions in the given expression. -/
    meta def size : expr → nat := λ e, fold e 0 (λ e bd n, n+1)
    -- meta def trans_count : expr → nat := λ e, fold e 0 (λ e bd n, n+1 <| is_app_of e `eq.trans |> n) 

    /-- A __term__ here means an expression that is not a Sort and which is not a typeclass instance.  -/
    meta def is_term (e : expr) : tactic bool := do
        T ← infer_type e,
        iscl ← tactic.is_class T,
        pure $ (¬ is_sort T) && ¬ iscl

    meta def list_local_const_terms (e : expr) : tactic (list expr) 
    := mfilter expr.is_term $ list_local_consts e
end expr

meta def option.repeat {α} (f : α → option α) : α → α
|a := option.get_or_else (option.repeat <$> f a) a

/- One can write unit tests by doing `run_cmd do  ... test.assert my_bool "my bool should be true"`.
    You will get an error with a helpful message when the unit test fails.
-/
namespace test
    meta def assert (test : bool) (msg : option string := none) : tactic unit := when (¬test) $ fail $ option.get_or_else msg "Assertion failed"
    meta def equal {α} [decidable_eq α] [has_to_tactic_format α] (expected actual : α) (msg : format := "") : tactic unit := when (expected ≠ actual) $ do
        epp ← pp expected,
        app ← pp actual,
        fail $ (to_fmt "Assertion failed: \nexpected: ") ++ format.nest 10 epp ++ "\n  actual: " ++ format.nest 10 app ++ "\n" ++ msg
    -- [TODO] `meta def snapshot` would be the dream. You could do this by dumping the to_tactic_format code to a text file and then reading it back using io. I guess you would also need a monad called test.
end test
