import .M .zipper .refine
open ez tactic
namespace robot

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

meta def get_candidate_actions : Z → M (list action)
:= tree.zipper.get_non_failures (λ z, as_action z) 

meta def get_sister_candidate_actions_aux : Z → list action → M (list action)
|z acc := do
    some (z,i) ← pure $ tree.zipper.up_with_index z | pure acc,
    cs ← list.mcollect get_candidate_actions $ list.take i $ z.down_all,
    acc ← pure $ cs ++ acc,
    if z.item.is_strat then pure acc else do
    get_sister_candidate_actions_aux z acc
     
meta def get_merger_actions : list action → list action → M ( list action)
|l₁ l₂ := list.mcollect (λ a₁ : action, list.mchoose (λ a₂ : action, strategy.merge a₁.1 a₂.1 >>= λ s, pure (s,a₂.2)) l₂) l₁


meta def score_rule (r : rule_app) : M int := do
    is_local ← r.is_local_hypothesis,
    meta_count ← r.count_metas, 
    if (meta_count > 1) then pure (-10) else do
    ce ← get_ce,
    lookahead ← get_lookahead,
    -- [IDEA]: score by symbol overlap
    ce_symbs ← zipper.count_symbols $ ce,
    lhs_symbs ← zipper.count_symbols $ r.lhs,
    let overlap := table.size $ ce_symbs ∩ lhs_symbs,
    let symm_diff := table.size (ce_symbs ∪ lhs_symbs) - overlap,
    -- [TODO] if the LHS is in the lookahead table then use that
    has_diom ← 
        (if ¬ expr.is_composite r.r.lhs then pure ff else (do
            let pts := ce :: lookahead.map rule_app.rhs,
            matches ← state_t.lift $ list.mchoose (λ x, do
                zipper.find_subterm r.lhs (zipper.zip x),
                pure x
            ) pts,
            pure $ bnot $ list.empty $ matches
        )),
    is_comm ← rule_app.is_commuter r,
    pure 
        $ (if is_comm then -5 else 0) 
        + (if is_local then 10 else 0) 
        + (if has_diom then 10 else 0) 
        - meta_count 
        - symm_diff

meta def score_strategy : strategy → M int
|(strategy.ReduceDistance a b) := do
     ce ← get_ce,
     d ← get_distance ce a b,
     pure $ max (10 - d) 0
|(strategy.Use r) := score_rule r

meta def caveman_evaluate :  list action → M evaluation
|[] := pure []
|l@(⟨s,sz⟩::t)  := do
    -- sisters ← get_sister_candidate_actions_aux sz [],
    -- mergers ← get_merger_actions sisters l,
    -- trace mergers,

    scores ← list.mmap (score_strategy ∘ prod.fst) l,
    scoreboard ← pure $ list.zip l scores,
    let scoreboard := scoreboard.qsort (λ x y, x.2 > y.2),
    scoreboard_pretty ← scoreboard.mmap (λ ⟨s,b⟩, do pps ← tactic.pp s, pure $ (to_fmt $ to_string b) ++ format.space ++ pps),
    tactic.trace_m "\nscore: \n" $ scoreboard_pretty,
    tactic.trace " ",
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

     -/ 


/-- A simple scoring heuristic for lists of terms.
    [TODO] For now this is just whatever works but there is some theory that can go in here.
-/
meta def caveman_overall_score : list (action × score) → M score
|[x] := pure $ 10
|l  := do
    let l := l.filter (λ x, x.2 ≥ -5),
    match list.partition (λ x : _ × score, x.2 ≥ 0) l with
    |⟨[],[]⟩ := pure $ -100 -- [TODO], special case: it's impossible?
    |⟨[],negs⟩ := do
        pure $ 5 - negs.length
    |⟨xs,_⟩ := pure $ 5 - xs.length
    end

meta def caveman_policy : policy := 
    { evaluate := caveman_evaluate
    , get_overall_score := caveman_overall_score
    }

end robot