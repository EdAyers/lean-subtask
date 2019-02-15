import ..equate
open robot
section
    universe u
    open list
    variables  {α : Type u} {l s t : list α} {a b c : α}
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