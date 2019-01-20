import .util
namespace robot
universes u
inductive tree (α : Type u)
|branch (a : α) (children : list tree) : tree
|leaf (a : α) : tree
inductive tree.path (α : Type u)
|top : tree.path
|down : α → ℕ → list (tree α) → tree.path → tree.path

structure tree.zipper (α : Type u) :=
(path : tree.path α)
(current : tree α)

namespace tree
variables {α β : Type u}

def item : tree α → α
|(branch a _) := a
|(leaf a) := a

namespace zipper

def zip : tree α → zipper α
|t := ⟨path.top _, t⟩

def up : zipper α → option (zipper α)
|⟨path.top _, c⟩ := none
|⟨path.down a n l p,c⟩ := some $ zipper.mk p $ tree.branch a $ list.update_nth l n c

meta def unzip : zipper α → tree α := current ∘ option.repeat up

def down : ℕ → zipper α → option (zipper α)
|n ⟨p,tree.branch a l⟩ := zipper.mk (path.down a n l p) <$> list.nth l n
|n ⟨p,tree.leaf a⟩ := none

def children : zipper α → list (zipper α)
|⟨p,tree.branch a l⟩ := l.mapi (λ i c, zipper.mk (path.down a i l p) $ c)
|_ := []

def item : zipper α → α := item ∘ current

meta def fold (f : β → zipper α → β) : β → zipper α → β
|b z := list.foldl fold (f b z) (children z)

meta def mfold {M} [monad M] (f : β → zipper α → M β) : β → zipper α → M β
|b z := do
    b ← f b z,
    list.mfoldl mfold b (children z)

end zipper
end tree
end robot