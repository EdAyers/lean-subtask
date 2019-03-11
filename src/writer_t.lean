/- Author: E.W.Ayers © 2019 -/
universes u v
/-- Writer monad transformer. -/
structure writer_t (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : m (α × σ))
attribute [pp_using_anonymous_constructor] writer_t
namespace writer_t
        variables {σ : Type u} [monoid σ] {m : Type u → Type v} [monad m] 
        variables {α β : Type u}
        instance : monad (writer_t σ m) := 
        { pure := λ α a, ⟨pure ⟨a,1⟩⟩ 
        , bind := λ α β x f, ⟨do 
            ⟨a,s₁⟩ ← x.run, 
            ⟨b,s₂⟩ ← (f a).run, 
            pure ⟨b,s₁ * s₂⟩
        ⟩}
        instance [alternative m] : alternative (writer_t σ m) := 
        { failure := λ α, ⟨failure⟩
        , orelse := λ α x₁ x₂, ⟨run x₁ <|> run x₂⟩
        }
        def log (msg : σ) : writer_t σ m punit := ⟨pure ⟨⟨⟩,msg⟩⟩
        instance : has_monad_lift m (writer_t σ m) := 
        ⟨λ α t, ⟨(λ a, ⟨a,1⟩) <$> t⟩⟩
end writer_t
