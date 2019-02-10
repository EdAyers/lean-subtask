import ..bigram ..equate

open robot tactic
constant α : Type
constants A B C : set α
run_cmd (do 
    rt ← robot.get_equate_rule_table,
    bgc ← bigram.of_rule_table rt,
    tactic.trace $ bigram.bigram_cache.occs bgc,
    tactic.trace $ bigram.bigram_cache.trigs bgc,
    b1 ← tactic.to_expr ```(A ∩ (B ∪ C)),
    b2 ← tactic.to_expr ```(A ∪ (B ∩ C)),
    -- -- b2 ← bigram.of_names `has_inter.inter `has_union.union,
    -- -- let b1 : bigram := bigram.mk `(has_union.union) `(has_union.union),
    d1 ← bigram.distance bgc b1 b2,
    tactic.trace d1, 
    pure ()
)



