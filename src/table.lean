open expr
open native

section foldable
    universes u v
    class foldable (F : Type u → Type u) :=
    (fold : ∀ {α σ : Type u}, (α → σ → σ) → σ → F α → σ)
end foldable

-- [TODO] make sure the argument order conventions in this file are not pointlessly different to commonly used ones.
/-- Lightweight wrapper around `rbtree` because I keep swapping out which dictionary implementation I am using -/
meta def table (α : Type) : Type := rb_set α
namespace table
    variables {α : Type} [has_lt α] [decidable_rel ((<) : α → α → Prop)]
    meta def empty : table α := rb_map.mk α unit
    meta def is_empty : table α → bool := λ t, rb_map.size t = 0
    meta instance has_emptyc : has_emptyc (table α) := ⟨empty⟩
    meta def from_list (l : list α) : table α  := rb_map.set_of_list l
    meta def to_list (d : table α) : list α := rb_set.to_list d
    meta def union  (l : table α ) (r : table α) := rb_set.fold r l (λ x s, rb_set.insert s x)
    meta instance has_union : has_union (table α) := ⟨union⟩
    /-- `subtract l r = {x ∈ l | x ∉ r}`-/
    meta def subtract (l : table α) (r : table α) := rb_set.fold r l (λ x s, rb_set.erase s x)
    meta instance has_sub : has_sub (table α) := ⟨subtract⟩
    meta def contains : α → table α → bool := λ a t, rb_set.contains t a
    meta instance has_mem : has_mem α (table α) := ⟨λ x T, contains x T⟩
    meta instance {x : α} {T : table α} : decidable (x ∈ T) := dite (contains x T) is_true is_false
    meta def insert : α → table α → table α := λ a t, rb_set.insert t a
    meta def insert_many : list α → table α → table α := λ xs t, xs.foldl (λ t x, insert x t) t
    meta instance has_insert : has_insert α (table α) := ⟨insert⟩
    meta def erase : α → table α → table α := λ x t, rb_set.erase t x
    meta def fold {β} : (β → α → β) → β → table α → β  := λ r z t, rb_set.fold t z (function.swap r)
    meta instance : foldable (table) := ⟨λ α σ f i t, rb_set.fold t i f⟩
    meta def mfold {T} [monad T] {β} (f : β → α → T β) (init : β) (t : table α) : T β := rb_set.mfold t init (function.swap f)
    meta def inter (l : table α) (r : table α) : table α := fold (λ acc a, if a ∈ r then insert a acc else acc) ∅ l
    meta instance has_inter : has_inter (table α) := ⟨λ l r, inter l r⟩
    /-- Return `tt` if all of the items in the table satisfy the predicate. -/
    meta def all (p : α → bool) : table α → bool := option.is_some ∘ mfold (λ _ a, if p a then some () else none) ()
    /-- Return `tt` if at least one of the elements satisfies the predicate-/
    meta def any (p : α → bool) : table α → bool := option.is_none ∘ mfold (λ (x : unit) a, if p a then none else some ()) ()
    meta def filter (p : α → bool) : table α → table α := fold (λ t k, if p k then insert k t else t) empty
    meta def first : table α → option α := fold (λ o a, option.rec_on o (some a) some) none -- [HACK] highly inefficient but I can't see a better way given the interface.
    meta instance [has_to_string α] : has_to_string (table α) := ⟨λ t, (λ s, "{|" ++ s ++ "|}") $ list.to_string $ to_list $ t⟩
    meta instance has_to_tactic_format [has_to_tactic_format α] : has_to_tactic_format (table α) := 
        ⟨λ t, do
            items ← t.to_list.mmap (tactic.pp),
            pure $ to_fmt "{" ++ (format.group $ format.nest 1 $ format.join $ list.intersperse ("," ++ format.line) $ items ) ++ "}"⟩
    meta def are_equal [decidable_eq α] : table α → table α → bool := (λ l₁ l₂, l₁ = l₂) on (to_list)
    -- meta instance [decidable_eq α] {t₁ t₂ : table α} : decidable (t₁ = t₂) := dite (are_equal t₁ t₂) (is_true) (is_false)
    /-- A total ordering on tables. -/
    meta def compare : table α → table α → Prop := λ t₁ t₂, to_list t₁ < to_list t₂
    meta instance : has_lt (table α) := ⟨compare⟩
    meta instance : decidable_rel ((<) : table α → table α → Prop) := λ t₁ t₂, list.has_decidable_lt (to_list t₁) (to_list t₂)
end table

meta def dict (k : Type) (α : Type) : Type := rb_map k α
namespace dict
    variables {k : Type} [has_lt k] [decidable_rel ((<) : k → k → Prop)]
    variable {α : Type}
    meta instance : has_sizeof (dict k α) := ⟨λ d, rb_map.size d⟩ 
    meta def empty : dict k α := rb_map.mk k α
    meta instance : has_emptyc (dict k α) := ⟨empty⟩
    meta def insert : k → α → dict k α → dict k α := λ k a d, rb_map.insert d k a
    meta def get : k → dict k α → option α := λ k d, rb_map.find d k
    meta def contains : k → dict k α → bool := λ k d, rb_map.contains d k
    meta instance : has_mem k (dict k α) := ⟨λ k d, contains k d⟩
    meta instance (key : k) (d : dict k α) : decidable (key ∈ d) := by apply_instance
    meta def modify (f : option α → α) (key : k) (d : dict k α) : dict k α := insert key (f $ get key d) d
    meta def modify_default (default : α) (f : α → α) : k → dict k α → dict k α := modify (λ o, f $ option.get_or_else o default)
    meta def modify_when_present (f : α → α) : k → dict k α → dict k α := λ key d, option.rec_on (get key d) d (λ a, insert key a d)
    meta def get_default (default : α)  (key : k) (d: dict k α) : α := option.get_or_else (get key d) default
    meta def erase : k → dict k α → dict k α := λ k d, rb_map.erase d k
    meta def merge (l r : dict k α) := rb_map.fold r l insert
    meta instance : has_append (dict k α) := ⟨merge⟩
    meta def fold {β} (r : β → k → α → β) (z : β) (d : dict k α) : β := rb_map.fold d z (λ k a b, r b k a)
    meta def mfold {T} [monad T] {β} (f : β → k → α → T β) (z : β) (d : dict k α) : T β := rb_map.mfold d z (λ k a b, f b k a)
    meta def map {β} (f : α → β) (d : dict k α) : dict k β := rb_map.map f d
    meta def filter (p : k → α → bool) (d : dict k α) := fold (λ d k a, if p k a then insert k a d else d) empty d
    meta def collect {β} (f : k → α → dict k β) := fold (λ d k a, d ++ f k a) empty
    meta def choose {β} (f : k → α → option β) := fold (λ d k a, match f k a with (some b) := insert k b d | none := d end) empty
    meta def keys : dict k α → table k := fold (λ acc k v, table.insert k acc) ∅
    meta def to_list : dict k α → list (k×α) := rb_map.to_list
    /--[HACK] not efficient, don't use in perf critical code. -/
    meta def first : dict k α → option (k×α) := fold (λ o k a, option.rec_on o (some (k,a)) some) none
    section formatting
        open format
        meta instance [has_to_string α] [has_to_string k] : has_to_string (dict k α) := ⟨λ d,  (λ s, "{" ++ s ++ "}") $ list.to_string $ dict.to_list $ d⟩
        -- meta instance has_to_format [has_to_format α] [has_to_format k] : has_to_format (dict k α) := ⟨λ d, 
        --     to_fmt "{" ++ group (nest 1 $ join $ list.intersperse ("," ++ line) $ list.map (λ (p:k×α), to_fmt p.1 ++ " ↦ " ++ to_fmt p.2) $ dict.to_list d) ++ to_fmt "}"
        -- ⟩
        meta instance has_to_tactic_format [has_to_tactic_format α] [has_to_tactic_format k] : has_to_tactic_format (dict k α) := ⟨λ d, do
            items ← list.mmap (λ (p:k×α), do f1 ← tactic.pp p.1, f2 ← tactic.pp p.2, pure $ f1 ++ line ++ "↦ " ++ nest 3 (f2)) (to_list d),
            pure $ "{" ++ group (nest 1 $ join $ list.intersperse ("," ++ line) $ items) ++ "}"
         ⟩
    end formatting
end dict

/--dictionary with a default if it doesn't exist. You define the default when you make the dictionary. -/
meta structure dictd (k : Type) (α : Type) : Type :=
(dict : dict k α)
(default : k → α)
namespace dictd
  variables {k : Type} [has_lt k] [decidable_rel ((<) : k → k → Prop)] {α : Type}
  private meta def empty (default : k → α) : dictd k α := ⟨dict.empty, default⟩
  meta def get (key : k) (dd : dictd k α) : α := dict.get_default (dd.2 key) key dd.1
  meta def insert (key : k) (a : α) (dd : dictd k α) : dictd k α := ⟨dict.insert key a dd.1, dd.2⟩
  meta def modify (f : α → α) (key : k) (dd : dictd k α) : dictd k α := ⟨dict.modify (λ o, f $ option.get_or_else o (dd.2 key)) key dd.1, dd.2⟩
end dictd

meta def tabledict (κ : Type) (α : Type) 
    [has_lt κ] [decidable_rel ((<) : κ → κ → Prop)] 
    [has_lt α] [decidable_rel ((<) : α → α → Prop)] : Type := dict κ (table α)

namespace tabledict 
    variables {κ α : Type} [has_lt κ] [decidable_rel ((<) : κ → κ → Prop)] [has_lt α] [decidable_rel ((<) : α → α → Prop)]
    meta def empty : tabledict κ α := dict.empty
    meta instance : has_emptyc (tabledict κ α) := ⟨empty⟩
    meta def insert : κ → α → tabledict κ α → tabledict κ α := λ k a d, dict.modify_default ∅ (λ t, t.insert a) k d
    meta def erase : κ → α → tabledict κ α → tabledict κ α := λ k a d, dict.modify_when_present (λ t, t.erase a) k d
    meta def get : κ → tabledict κ α → table α := λ k t, dict.get_default ∅ k t
    meta def contains : κ → α → tabledict κ α → bool := λ k a d,  match dict.get k d with |(some t) := t.contains a | none := ff end
    meta instance [has_to_tactic_format κ] [has_to_tactic_format α] : has_to_tactic_format (tabledict κ α) := ⟨λ (d : dict κ (table α)), tactic.pp d⟩
    meta def fold {β} (f : β → κ → α → β) : β → tabledict κ α → β := dict.fold (λ b k, table.fold (λ b, f b k) b)
    meta def mfold {T} [monad T] {β} (f : β → κ → α → T β) : β → tabledict κ α → T β := dict.mfold (λ b k, table.mfold (λ b, f b k) b)
end tabledict

meta def listdict (κ : Type) (α : Type) [has_lt κ] [decidable_rel ((<) : κ → κ → Prop)] : Type := dict κ (list α)

namespace listdict
    variables {κ α : Type} [has_lt κ] [decidable_rel ((<) : κ → κ → Prop)]
    meta def empty : listdict κ α := dict.empty
    meta instance : has_emptyc (listdict κ α) := ⟨empty⟩
    meta def insert : κ → α → listdict κ α → listdict κ α | k a d := dict.modify_default [] (λ t, a :: t) k d
    meta def pop : κ → listdict κ α → option (α × listdict κ α) | k d := match dict.get_default [] k d with |[] := none |(h::t) := some (h, dict.insert k t d)  end
    meta def get : κ → listdict κ α → list α | k d := dict.get_default [] k d
    meta def fold {β} (f : β → κ → α → β) : β → listdict κ α → β := dict.fold (λ b k, list.foldl (λ b, f b k) b)
    meta def mfold {T} [monad T] {β} (f:β → κ → α → T β) : β → listdict κ α → T β := dict.mfold (λ b k, list.mfoldl (λ b, f b k) b)
    meta def first : listdict κ α → option (κ × α) := fold (λ o k a, option.rec_on o (some (k,a)) some) none
    -- meta instance [has_to_format κ] [has_to_format α] : has_to_format (listdict κ α) := ⟨λ (d : dict κ (list α)), to_fmt d⟩
    meta instance [has_to_tactic_format κ] [has_to_tactic_format α] : has_to_tactic_format (listdict κ α) := ⟨λ (d : dict κ (list α)), tactic.pp d⟩
end listdict