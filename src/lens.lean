import category.traversable
namespace lens
/- 

lens : (s → a) → (s → b → t) → Lens s t a b

set : Setter s t a b → b → s → t
over : Setter 

 -/
universes u

variables {s t a b e r : Type u} 
variables {F M : Type u → Type u} [functor F] [monad M]

inductive Equality : Type u → Type u → Type u → Type u → Type (u+1)
|id {a b} : Equality a b a b

inductive Iso :  Type u → Type u → Type u → Type u → Type (u+1)
|iso {s t a b} : (s → a) → (b → t) → Iso s t a b
def Iso.id : Iso a b a b := Iso.iso id id
def Iso.of_eq : Π {s t a b}, Equality s t a b  → Iso s t a b |_ _ _ _ (Equality.id) := Iso.id
instance Iso.from_eq : has_coe (Equality s t a b) (Iso s t a b) := ⟨Iso.of_eq⟩

inductive Lens : Type u → Type u → Type u → Type u → Type (u+1)
|lens {s t a b} : (s → a) → (s → b → t) → Lens s t a b
open Lens
def Lens.id : Lens a b a b := lens id (λ _, id)
def Lens.iso : (s → a) → (b → t) → Lens s t a b := λ f g, lens f (λ _, g)
def Lens.of_Iso : Iso s t a b → Lens s t a b | (Iso.iso f g) := Lens.iso f g
def inside : Lens s t a b → Lens (e -> s) (e -> t) (e -> a) (e -> b)
|(lens f g) := lens (λ x y, f $ x $ y) (λ x y z, g (x z) (y z))

inductive Prism : Type u → Type u → Type u → Type u → Type (u+1)
|prism {s t a b} : (b → t) → (s → t ⊕ a) → Prism s t a b
def Prism.of_Iso : Iso s t a b → Prism s t a b
|(Iso.iso f g) := Prism.prism g (sum.inr ∘ f)
instance Prism.has_coe_iso : has_coe (Iso s t a b) (Prism s t a b) := ⟨Prism.of_Iso⟩
def outside : Prism s t a b → Lens (t → r) (s → r) (b → r) (a → r)
|(Prism.prism f g) := lens (λ x y, x $ f $ y) (λ x y z, sum.rec_on (g z) x y)
inductive Review : Type u → Type u → Type u → Type u → Type (u+1)
|unto {s t a b} : (b → t) → Review s t a b
def Review.of_Prism : Prism s t a b → Review s t a b
|(Prism.prism f g) := Review.unto f

inductive Getter : Type u → Type u → Type (u+1)
|to {s a} : (s → a) → Getter s a
def Getter.of_Lens : Lens s t a b → Getter s a
|(Lens.lens f g) := Getter.to f
def Getter.fold_map_of : Getter s a → (a → r) → s → r
|(Getter.to f) g x := g $ f $ x
def Getter.app : s → Getter s a → a | x (Getter.to f) := f x
infixl ` ^. `:30 := Getter.app
def view [monad_reader s M] : Getter s a → M a := λ g, do x ← read, pure (x ^. g)
def use [monad_state s M] : Getter s a → M a := λ g, do x ← get, pure (x ^. g)

inductive Traversal (F : Type u → Type u) [applicative F] : Type u → Type u → Type u → Type u → Type (u+1)
|traverse {s t a b : Type u} : ((a → F b) → (s → F t)) → Traversal s t a b 
def Traversal.of_Lens (F : Type u → Type u) [applicative F] : Lens s t a b → Traversal F s t a b 
|(lens f g) := Traversal.traverse (λ h x, pure (g x) <*> (h $ f $ x))
inductive Setter : Type u → Type u → Type u → Type u → Type (u+1)
|sets {a b s t} : ((a → b) → (s → t)) → Setter s t a b
open Setter
--def sets (f : (a → b) → (s → t)) := Setter.sets f
def over :Setter s t a b → (a → b) → (s → t)
|(sets g) f x := g f x 
def Setter.of_Traversal {F : Type u → Type u} [applicative F] : Traversal F s t a b → Setter (s) (F t) a b
|(Traversal.traverse f) := Setter.sets (λ g y, f (pure ∘ g) y) -- [HACK] is this right?
def set : Setter s t a b → b → s → t := λ setter b, over setter (λ _, b) 
def mapped {a b : Type u} {F : Type u → Type u} [functor F] : Setter (F a) (F b) a b := sets (λ f a, f <$> a)
def prod_fst_setter {α β : Type u} : Setter (α × β) (α × β) α α := sets (λ f ⟨a,b⟩, ⟨f a, b⟩)
def Setter.id : Setter a b a b := sets id
-- idea: generate the setters automatically using a tactic.
