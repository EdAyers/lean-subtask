import .rule .zipper .rule_table

namespace robot
--open ez ez.zipper
/-[IDEA] tag bigrams with the direction between the upper and lower symbol. 
`U` means that the bigram is unitary. 
The `Comm` mode can be used to indicate that the direction doesn't matter. -/
--inductive dir | L | R | U | Comm
/--A bigram is a pair of symbols (constants or local constants) appearing in a term. -/
@[derive decidable_eq]
meta structure bigram :=
(t : name)
(b : name)
-- (dir : dir)

meta def bigram.lt : bigram → bigram → bool := λ ⟨t₁,b₁⟩ ⟨t₂,b₂⟩, (t₁,b₁) < (t₂,b₂)
meta instance bigram.has_lt : has_lt bigram := ⟨λ x y , bigram.lt x y⟩
meta instance bigram.dec_lt : decidable_rel ((<) : bigram → bigram → Prop) := by apply_instance
meta instance bigram.has_to_string : has_to_string bigram := 
⟨λ ⟨t,b⟩, "⟮" ++ to_string t ++ ", " ++ to_string b ++ "⟯"⟩
meta instance bigram.has_to_tactic_format : has_to_tactic_format bigram := 
⟨λ ⟨t,b⟩, do ppt ← tactic.pp t, ppb ← tactic.pp b, 
pure $ "⟮" ++ ppt ++ ", " ++ ppb ++ "⟯"⟩
-- follows along with the SInE algorithm but on bigrams instead of individual symbols.

namespace bigram

-- meta def of_names : name → name → tactic bigram := λ n₁ n₂, do
--     r₁ ← tactic.resolve_name n₁ >>= tactic.to_expr,
--     r₂ ← tactic.resolve_name n₂ >>= tactic.to_expr,
--     pure $ bigram.mk r₁ r₂

def tolerance := 2
def generality := 5
def max_trigger_depth := 10
open ez ez.zipper

private meta def get_bigrams_aux : name → mtable bigram → zipper → tactic (mtable bigram)
|t acc z := do
    (b,children) ← down_proper z,
    match expr.const_name b with
    |(some n) :=
        let acc := acc.insert ⟨t,n⟩ in
        children.mfoldl (get_bigrams_aux n) acc
    |none := pure acc
    end

meta def get_bigrams : expr → tactic (mtable bigram) := λ e, do
    (t,children) ← down_proper $ zip $ e,
    match expr.const_name t with
    |(some t) := children.mfoldl (get_bigrams_aux t) ∅
    |none := pure ∅
    end

-- a bigram table; 


meta structure bigram_cache :=
(trigs : tabledict bigram rule)
(occs : mtable bigram)

meta instance bigram_cache.has_to_tactic_format : has_to_tactic_format bigram_cache :=
⟨λ x, do ppo ← tactic.pp x.occs, pure ppo⟩

private meta def rare_test : mtable bigram → mtable bigram → bigram → bool
|occs bs b := (occs(b) ≤ generality) ∨ bs.all (λ b' _, occs(b) ≤ tolerance * occs(b'))

meta def bigram_cache.get_rares (bc : bigram_cache) : expr → tactic ( mtable bigram )
|e := do bs ← get_bigrams e, pure $ bs.filter $ rare_test bc.occs bs

meta def compute_bigram_cache : list rule → tactic bigram_cache := λ rs, do
    bigs ← rs.mmap (λ r, prod.mk r <$> get_bigrams r.lhs),
    occs ← pure $ list.foldl mtable.join ∅ $ list.map prod.snd $ bigs,
    trigs ← pure $ bigs.foldl (λ acc ⟨r,bs⟩,
        dict.fold (λ acc bg a, tabledict.insert bg r acc) acc 
        $ bs.filter $ rare_test occs bs 
    ) ∅,
    pure $ {trigs := trigs, occs := occs}

meta def distance_aux (bgc : bigram_cache) : table bigram → table bigram → table expr → ℕ → tactic ℕ
|visited targets front n := do
    tactic.trace_m "front: " $ front, 
    tactic.trace_m "targets: " $ targets, 
    rares ← mtable.to_table <$> front.mfold (λ acc e, mtable.join acc <$> bgc.get_rares e) ∅,
    let rares := rares \ visited,
    let visited := visited ∪ rares,
    if targets.any (λ z, rares.contains z) then pure n else do -- [HACK] remove this line to make algorithm clear ALL targets.
    let targets := targets \ rares,
    if targets.is_empty then pure n else
    if front.is_empty then failure else
    if n > max_trigger_depth then failure else do
    front ← rares.mfold (λ front rare, do
        triggers ← pure $ bgc.trigs.get rare,
        tactic.trace_m "fold: " $ (rare,triggers),
        table.mfold (λ front r, do
            pure $ table.insert (rule.rhs r) $ front
        ) front triggers
    ) ∅,
    let front : table expr := rares.fold (λ front rare, 
            table.fold (λ front r, front.insert $ rule.rhs r) front 
            $ bgc.trigs.get rare
        ) ∅,
    distance_aux visited targets front (n+1) 

meta def distance (bgc : bigram_cache) : expr → expr → tactic ℕ
|e₁ e₂ := do 
    targets ← mtable.to_table <$> bgc.get_rares e₂,
    distance_aux bgc ∅ targets (table.singleton e₁) 0

meta def of_rule_table : rule_table → tactic bigram_cache := compute_bigram_cache ∘ rule_table.rules 




/- 
Now that we have the zero trigger table we can get
the n-trigger table by recursively looking up zero_trigger, then looking at the rare symbols in rhs.

The question that I want to be able to answer is:
Given a pair of expressions `e`, find a trigger-distance between them.
To do this, we look at all of the rare symbols in `e`, find rules which work with these,
then look at the next generation of symbols.

In addition, you might find rare digrams that are a 'logjam' in the sense that there are no rules which deal with them.
An example of a logjam is `log(a + b)`, since there is no way of moving these two past each other, we have to find a way
of rewriting either above or below. So we begin the search again but looking at the neighbours of the logjammed bigram.

In general, I think there will be some techniques for looking at subterm-locally-rare bigrams.

So eg, if we are trying to create `a + c` and we have eg `1 ∙ (b ∙ a + (1 ∙ b) ∙ c)`,
then it will be a good idea to look for bigram triggers under the `+`.

But anyway, what is something we can do with this right away?
I want a digram distance table but I don't want it to take ages to compute.
Idea 1: compute a `(dict (bigram × bigram) ℕ)` This will be too big.
Idea 2: use the table `bigram ⇀ table rule` 


 -/

end bigram

end robot