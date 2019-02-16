import ..equate
open robot
section
    universe u
    open list
    variables {α : Type u} {a h : α} {l t s : list α}
    @[equate] def nil_append : [] ++ l = l := rfl
    @[equate] def append_cons : (h::t) ++ l = h:: (t ++ l) := rfl
    @[equate] def rev_nil : reverse ([] : list α) = [] := rfl
    @[equate] def append_nil : l ++ [] = l := begin induction l, refl, simp end
    @[equate] theorem rev_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] := 
    begin
            have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]),
            intro l₁, induction l₁, intros, refl,
            intro, 
            equate, 
            symmetry, equate
    end
    open list
    @[equate] lemma assoc : (l ++ s) ++ t = l ++ (s ++ t) :=
    begin
        induction l with lh lt,
        equate,
        equate
    end -- `induction l; simp *`
    lemma rev_app_rev : reverse (l ++ s) = reverse s ++ reverse l :=
    begin
        induction l,
        equate,
        equate 
    end
end