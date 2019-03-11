/- Author: E.W.Ayers © 2019 -/
import ..equate
open robot
section
    universe u
    open list
    variables {α : Type u} {a h : α} {l t s : list α}
    @[equate] def nil_append : [] ++ l = l := rfl
    @[equate] def append_cons : (h::t) ++ l = h:: (t ++ l) := rfl
    @[equate] def reverse_def : reverse l = reverse_core l [] := rfl
    @[equate] def rev_nil : reverse ([] : list α) = [] := rfl
    @[equate] def reverse_core_def : reverse_core (h :: t) l = reverse_core t (h :: l) := rfl
    @[equate] def append_nil : l ++ [] = l := begin induction l, refl, simp end
    @[equate] theorem rev_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] := 
    begin
            have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]),
            intro l₁, induction l₁, intros, refl,
            intro, 
            equate, 
            equate
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

namespace my_nat
    inductive my_nat : Type
    |zero : my_nat
    |succ : my_nat → my_nat
    open my_nat
    instance : has_zero my_nat := ⟨my_nat.zero⟩
    variables {x y z : my_nat}
    def add : my_nat → my_nat → my_nat
    |(my_nat.zero) x := x
    |(my_nat.succ x) y := my_nat.succ (add x y)
    instance : has_add my_nat := ⟨add⟩
    local notation `s(` x `)` := my_nat.succ x
    @[equate] lemma add_zero : 0 + x = x := rfl
    @[equate] lemma add_succ : (s(x)) + y = s(x + y) := rfl
    @[equate] lemma nat_assoc {x y z : my_nat} :  x + ( y + z ) = (x + y) + z :=
    begin
        induction x,
        equate,
        equate
    end
    @[equate] lemma succ_add : y + (s(x)) = s(y + x) := begin
        induction y, equate, equate
    end
    @[equate] lemma zero_add : x + my_nat.zero = x := begin 
        induction x, equate, symmetry, equate -- [FIXME] remove symmetry
    end
    @[equate] lemma add_comm : x + y = y + x := begin
        induction x, 
        rw zero_add, refl, 
        equate
    end
end my_nat