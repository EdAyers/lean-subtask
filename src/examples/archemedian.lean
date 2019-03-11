/- Author: E.W.Ayers © 2019 -/
import ..equate
import algebra.archimedean
open robot
universe u

variables {R : Type u} [linear_ordered_ring R] [floor_ring R] {x : R}

attribute [equate] int.cast_neg
attribute [equate] floor_coe
attribute [equate] floor_add_int
attribute [equate] floor_sub_int

@[equate] lemma ciel_def : ⌈x⌉ = -⌊-x⌋ := rfl
-- attribute [equate] neg_neg

@[equate] lemma my_ciel_coe (z : ℤ) : z = ⌈(z:R)⌉ :=
by equate

@[equate] theorem my_ceil_add_int (x : R) (z : ℤ) : ⌈x + z⌉ = ⌈x⌉ + z :=
by equate
-- [FIXME] bug where it thinks `0 = x * 0` is a good idea. Should be forbidden.