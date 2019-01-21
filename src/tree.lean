import .util
namespace robot
universes u
inductive tree (α : Type u)
|branch (a : α) (children : list tree) : tree
|leaf (a : α) : tree

namespace tree
variables {α β : Type u}

def head_item : tree α → α
|(branch a _) := a
|(leaf a) := a

def map_head_item (f : α → α) : tree α → tree α
|(leaf a) := leaf $ f $ a
|(branch a c) := branch (f a) c
def set_head_item (a : α) : tree α → tree α := map_head_item (λ _, a)

meta def map (f : α → β) : tree α → tree β
|(leaf a) := leaf $ f $ a
|(branch a c) := branch (f a) $ list.map map c

instance : has_pure tree := ⟨λ α a, leaf a⟩

meta instance : functor tree := {map := λ α β f t, map f t}
def set_children : list (tree α) → tree α → tree α |c t := branch (head_item t) c

inductive zipper.path (α : Type u)
|top : zipper.path
|down : α → ℕ → list (tree α) → zipper.path → zipper.path

structure zipper (α : Type u) :=
(p : zipper.path α)
(current : tree α)

namespace zipper

def path.fold (f : β → α → ℕ → list (tree α) → β) : β → path α → β
|b (path.top _) := b
|b (path.down a n l p) := path.fold (f b a n l) p

def path.items : path α → list α
|(path.top _) := []
|(path.down a _ _ p) := a :: path.items p

def zip : tree α → zipper α | t := ⟨path.top _, t⟩

def up : zipper α → option (zipper α)
|⟨path.top _, c⟩ := none
|⟨path.down a n l p,c⟩ := some $ zipper.mk p $ tree.branch a $ list.update_nth l n c

/--Go up and remove the current branch from the resulting tree. -/
def up_drop : zipper α → option (zipper α) 
|⟨path.top _, c⟩ := none
|⟨path.down a n l p, c⟩ := 
    some $ zipper.mk p $ tree.branch a $ list.remove_nth l n

meta def unzip : zipper α → tree α := current ∘ option.repeat up

def down : ℕ → zipper α → option (zipper α)
|n ⟨p,tree.branch a l⟩ := zipper.mk (path.down a n l p) <$> list.nth l n
|n ⟨p,tree.leaf a⟩ := none

def is_leaf : zipper α → bool |⟨p,leaf _⟩ := tt | _ := ff

def children : zipper α → list (zipper α)
|⟨p,tree.branch a l⟩ := l.mapi (λ i c, zipper.mk (path.down a i l p) $ c)
|_ := []
def set_current : tree α → zipper α → zipper α | t ⟨p,_⟩ := ⟨p,t⟩
def map_current : (tree α → tree α) → zipper α → zipper α | f z := set_current (f $ current z) z
def set_children : list (tree α) → zipper α → zipper α := λ c z, map_current (set_children c) z
/--Replace the children of current to be leaves of the given list instead.-/
def grow : list α → zipper α → zipper α |c z := z.map_current $ tree.set_children $ leaf <$> c

def item : zipper α → α := head_item ∘ current
def map_item (f : α → α) : zipper α → zipper α := map_current (map_head_item f)
def set_item : α → zipper α → zipper α |a := map_current (set_head_item a)  

meta def fold (f : β → zipper α → β) : β → zipper α → β
|b z := list.foldl fold (f b z) (children z)

meta def mfold {M} [monad M] (f : β → zipper α → M β) : β → zipper α → M β
|b z := do b ← f b z, list.mfoldl mfold b (children z)

meta def fold_up {α β} (f : β → zipper α → β) : β → zipper α → β
|b z := let b := f b z in option.rec_on (up z) b $ fold_up b

/--Get all of the items in the tree that are _strictly above_ the current position. -/
meta def above : zipper α → list α := path.items ∘ zipper.p
meta def depth : zipper α → ℕ := list.length ∘ above

meta def any_above {α} (f : α → bool) : zipper α → bool := λ z, z.above.any f

meta def pp_item_with_indent [has_to_tactic_format α] : zipper α → tactic format := λ z, do
  pa ← tactic.pp z.item,
  n ← pure $ z.depth,
  pure $ (format.join $ list.repeat " " n) ++ pa

end zipper
end tree
end robot