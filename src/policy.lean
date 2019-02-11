import .M .zipper .refine
open ez tactic
namespace robot
meta def first_policy : policy
|[] := failure
|l := pure l

meta def is_term : expr → tactic bool := λ e, do
    T ← infer_type e >>= instantiate_mvars,
    pure $ expr.is_sort T
open ez.zipper

def weak : ℕ := 1
def medium : ℕ := 2
def strong : ℕ := 3

meta def requires_nonmeta_variable_that_is_already_present (r : rule) : M nat := do
    ce ← get_ce,
    lhs_locals ← list_local_const_terms $ r.lhs,
    rhs_locals ← list_local_const_terms $ r.rhs,
    lhs_reqs ← pure $ list.filter (∉ rhs_locals) lhs_locals,
    ce_locals ← list_local_const_terms $ ce,
    let result := list.any ce_locals (∈ lhs_reqs),
    pure $ if result then weak else 0
meta def requires_complex_term_that_is_already_present (r : rule) : M nat := do
    ce ← get_ce,
    subterms ← list.map zipper.current <$> (get_smallest_complex_subterms $ r.lhs),
    subterms ← pure $ subterms.filter $ λ t, ¬ expr.occurs t r.rhs,
    unify_present ← subterms.mfilter $ λ t, zipper.has_occurences t ce,
    directly_present ← pure $ unify_present.filter $ λ t, expr.occurs t ce,
    pure $ if unify_present.empty then 0 else if directly_present.empty then medium else strong
meta def requires_nonmeta_variable_present_in_rule (r : rule) : M nat := do
    -- that is, look through local constants and find hypotheses which would introduce these.
    lcs ← list_local_const_terms r.lhs,
    rs ← list.msome (λ lc, bnot <$> list.empty <$> M.submatch lc) lcs,
    pure $ if rs then weak else 0
-- meta def requires_complex_term_that_is_present_in_rule (r : rule) : M nat := do
     /- I feel like this one will just always be true. 
     A better refinement would be:  
     -/
     
meta def score_rule (r : rule) : M int := do
    is_local ← r.is_local_hypothesis,
    meta_count ← r.count_metas, 
    ce ← get_ce,
    lookahead ← get_lookahead,
    /- [IDEA]: add a point for every large common subterm between ce and lhs  -/
    lcsts ← zipper.largest_common_subterms (zipper.zip ce) (zipper.zip r.lhs),
    let lcsts :=  lcsts.foldl (λ acc z, if z.is_terminal then acc else acc + 1 ) 0 ,
    --trace_m "score_rule: " $ lcsts,
    -- [IDEA]: score by symbol overlap
    ce_symbs ← zipper.count_symbols $ ce,
    lhs_symbs ← zipper.count_symbols $ r.lhs,
    let overlap := table.size $ ce_symbs ∩ lhs_symbs,
    let symm_diff := table.size (ce_symbs ∪ lhs_symbs) - overlap,
    -- [TODO] if the LHS is in the lookahead table then use that
    has_diom ← 
        if ¬ expr.is_composite r.lhs then pure ff else
            bnot 
            <$> list.empty 
            <$> list.mchoose (λ x, 
                state_t.lift 
                $ tactic.hypothetically' 
                $ (do 
                    zipper.find_subterm r.lhs (zipper.zip $ rule.rhs x), 
                    pure x)
            ) lookahead
        ,

    is_comm ← rule.is_commuter r,
    pure $ (if is_comm then -5 else 0) + (if is_local then 10 else 0) + (if has_diom then 10 else 0) - meta_count + /- lcsts -/ - symm_diff

meta def score_strategy : strategy → M int
|(strategy.ReduceDistance a b) := pure 0
|(strategy.Use r) := score_rule r

meta def score_policy : policy
|[] := failure
|l  := do
    -- when (l.length ≥ 10) (failure), -- [IDEA] too many _bad_ choices means we are better off backtracking.
    scores ← list.mmap (score_strategy ∘ prod.fst) l,
    scoreboard ← pure $ list.zip l scores,
    let scoreboard := scoreboard.qsort (λ x y, x.2 > y.2),
    ppsb ← scoreboard.mmap (λ ⟨s,b⟩, do pps ← tactic.pp s, pure $ (to_fmt $ to_string b) ++ format.space ++ pps),
    tactic.trace_m "\nscore: \n" $ ppsb,
    tactic.trace " ",
    let scoreboard := scoreboard.map prod.fst,
    -- ⟨a,_⟩ ← list.maxby (prod.snd) $ list.zip l scores,
    pure scoreboard

    /- [TODO] give a human-tuned, ad-hoc score based on:
        - [ ] what previous strategies were chosen from? That is, suppose a strategy came up earlier, then it would be good to detect that it should be a good idea now.
        - [x] Is the strategy a diom? If yes then it should be preferred, but only if it doesn't introduce too many more metas.
        - [ ] How many siblings does the strategy have? If this number is low we should prefer it.
        - [x] Is the rule an assumption, or a library rule?
        - [ ] Does the rule have high definitional depth?
        - [x] How many metas are introduced?
        - [ ] Some type-theoretical information??? eg, if the rule is for a specific type or for any type.
        - [x] on a `Use`, if there are large subterms already present then that's good.

    [TODO] backtrack when there are lots of possible actions all with bad scores.
     -/ 


end robot