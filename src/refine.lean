import .M .zipper
namespace robot
open strategy task tactic robot.tactic ez
-- meta def strategy.merge : strategy → strategy → M strategy 
-- |(Use r₁) (Use r₂) := do
--     r ← hypothetically' (do 
--         unify r₁.lhs r₂.lhs,
--         unify r₁.rhs r₂.rhs, 
--         rule.instantiate_mvars r₁
--     ),
--     pure $ Use r
-- |_ _ := failure

meta def destroy_test : zipper → expr → M bool
|e c := 
    (do 
        cez ← zipper.down_address e.address c,
        eq_above ← zipper.above_equal cez e,
        if eq_above then pure ff else failure
    )
    <|>
    (hypothetically' (ez.zipper.find_subterm e.current c *> pure ff)) <|> pure tt

meta def task.test : expr → task → M bool
|ce (task.Create n e) := do
    e ← instantiate_mvars e,
    pp_ce ← pp ce, pp_e ← pp e,
    --trace_m "task.test: " $ (to_fmt "testing that " ++ pp_ce ++ " satisfies Create " ++ pp_e),
    matches : list ez.zipper ← ez.zipper.find_occurences (ez.zipper.zip ce) e,
    pure $ matches.length ≥ n
    --trace_m "task.test: " $ matches,
    -- pure $ bnot matches.empty
|ce t@(task.CreateAll e) :=
    -- trace_m "task.test: " $ t,
    (hypothetically' (unify e ce *> pure tt)) <|> pure ff
|ce t@(task.Annihilate x) :=
    (ez.zipper.find_subterm x ce *> pure ff) <|> pure tt
|ce t@(task.Destroy e) := do
    destroy_test e ce
|ce t := notimpl
meta def hoist : task → strategy → M strategy
|t s@(Use r₁) := do
    passes ← task.test r₁.rhs t,
    if passes then pure s else failure
|_  _ := failure

-- -- automatically do moves which are 'cowild', that is, they just reduce to a variable.
-- meta def simplify : M (list strategy) := λ t, do
--     ce ← get_ce,
--     lookahead ← get_lookahead,
--     list.mchoose (λ r, 
--         rule.lhs_wildcard
--     ) lookahead

/-- Do In One Move. Check the lookahead table and see if any of 
the entries in there cause the task to be achieved. -/
meta def task.diom : task → M (list strategy) := λ t, do
    ce ← get_ce,
    lookahead ← get_lookahead,
    -- trace_m "diom: " $ lookahead,
    list.mchoose (λ r, do 
        let rhs := rule_app.rhs r,
        M.hypothetically' (do
                -- trace_m "task.diom: " $ (r, t),
                result ← task.test rhs t,
                if result then pure () else failure
        ),
        pure $ strategy.Use $ r
    ) lookahead

meta def try_dioms : task → M refinement | t := do 
    -- trace "trying dioms",
    dioms ← task.diom t, 
    -- trace dioms,
    if ¬ dioms.empty then pure ([],dioms) else failure

open ez tactic
meta def get_distance_reducer : expr → expr → M (rule_app)
| a b := do
    a ← instantiate_mvars a, 
    ce ← get_ce,
    current_dist ← zipper.get_distance ce a b,
    -- trace_m "\ngdr: " $ (ce, a, b,  current_dist),
    rs ← get_lookahead,
    drs ← list.mchoose (λ r, (do
        -- trace_m "gdr: " $ (rule_app.rhs r),
        new_dist ← zipper.get_distance (rule_app.rhs $ r) a b,
        -- trace_m "gdr: " $ (rule_app.rhs r, new_dist),
        pure (new_dist,r)
        --pure $ new_dist < current_dist) <|> pure ff
    )) rs,
    let drs := drs.filter (λ p : ℕ × rule_app, p.1 < current_dist),
    drs ← list.minby (int.of_nat ∘ prod.fst) drs,
    pure drs.2
    



meta def has_single_subterm : expr → M unit := λ a, do
    lhs ← get_ce,
    rhs ← get_rhs,
    zipper.has_single_subterm a $ zipper.zip lhs,
    -- [HACK] if the given symbol occurs twice in the RHS then we shouldn't consider it as a strategy
    -- this is a hack because really the refinement process shouldn't look at higher tasks.
    c ← zipper.count_subterms a $ zipper.zip rhs,
    when (c > 1) failure,
    pure ⟨⟩


meta def can_use_ReduceDistance : expr → M strategy := λ e, (do
    [a,b] ← zipper.get_proper_children e | failure,
    ce ← get_ce,
    zce ← pure $ zipper.zip ce, 
    rhs ← get_rhs,
    -- trace_m "can_use_ReduceDistance" $ (a,b),
    has_single_subterm a,
    has_single_subterm b, 
    dist ← zipper.get_distance ce a b,
    -- trace_m "can_use_ReduceDistance" $ (a,b,dist),
    r ← get_distance_reducer a b,
    pure $ ReduceDistance a b
    )

meta def can_use_commutativity : expr → M bool := λ e, (do 
    [a,b] ← zipper.get_proper_children e | failure,
    ce ← get_ce,
    zipper.has_single_subterm a $ zipper.zip ce,
    zipper.has_single_subterm b $ zipper.zip ce,
    zipper.get_distance ce b a,
    pure tt
) <|> pure ff

meta def task.refine (t : task) : M refinement :=
try_dioms t <|>
match t with
|(task.Create n e) := do
    rss ← (list.singleton <$> can_use_ReduceDistance e) <|> pure [],
    -- trace_m "task.refine: " $ rss,
    ce ← get_ce,
    rt ← get_rule_table,
    submatches ← rt.submatch e,
    -- trace_m "task.refine: " $ (e,submatches),
    use_comm ← can_use_commutativity e,
    -- trace_m "task.refine: " $ use_comm,
    submatches ← pure submatches, -- if use_comm then pure submatches else submatches.mfilter (λ z, bnot <$> rule.is_commuter z),
    -- [TODO] need a way of ignoring commutativity here. 
    -- trace_m "task.refine: " $ submatches,
    strats ← pure $ list.map strategy.Use $ list.filter (λ r, ¬ rule_app.lhsz_is_meta r) $ submatches,
    pure $ ([],rss ++ strats)
|(task.CreateAll a) := do
    ce ← get_ce >>= lift instantiate_mvars,
    -- trace_m "refine CreateAll: " $ ce,
    --scs ← zipper.lowest_uncommon_subterms ce a,
    scs ← zipper.smallest_absent_subterms ce a,
    -- trace_m "refine CreateAll: " $ scs,
    --if scs.length = 0 then pure $ ([],[]) else do
    -- if list.any scs (zipper.is_top)  then do 
    --     rt ← get_rule_table,
    --     hrws ← rule_table.head_rewrites_rhs a rt,
    --     pure $ ([], strategy.Use <$> hrws)
    -- else do
    let primaries := (λ p : ℕ × zipper, task.Create p.1 p.2.current) <$> scs,
    secondaries ← list.mchoose (λ p : _ × _, do
        z ← zipper.up p.2,
        pure $ task.Create p.1 z.current
     ) scs,

    -- find the smallest absent subterms on the LHS bit not RHS
    rscs ← zipper.smallest_absent_composite_subterms a ce,

    to_destroy ← pure 
        $ list.map (task.Destroy) 
        $ list.map (prod.snd)
        $ rscs,

    lhs_lcs ← list_local_const_terms ce,
    -- trace_m "lhs_lcs: " $ lhs_lcs,
    rhs_lcs ← list_local_const_terms a,
    to_annihilate ← pure $ list.map task.Annihilate $ lhs_lcs.filter (∉ rhs_lcs),
    let scs := primaries ++ to_annihilate ++ secondaries ++ to_destroy,
    pure $ (scs, [])
|(task.Annihilate x) := do
    ce ← get_ce, rt ← get_rule_table,
    rss ← (list.singleton <$> get_distance_reducer x x) <|> pure [],
    -- find all rules which will remove `x` from the face of the earth?
    -- trace_m "refine annihilate: " $ rss,
    if ¬ rss.empty then
        pure $ ([],[strategy.ReduceDistance x x])
    else pure ([],[])
|(task.Destroy x) := do
    rt ← get_rule_table,
    some xu ← pure $ zipper.up x | pure ([],[]),
    submatches ← rt.submatch_lhs x.current,
    submatches ← list.mmap (λ r, rule_app.flip r) submatches,
    ⟨breakups,rewrites⟩ ← list.mpartition (λ r, 
        (do z ← zipper.find_non_unify_subterm x.current (rule_app.lhs r),
            guard (¬ z.is_top),
            pure $ sum.inl r
        ) <|> (pure $ sum.inr r)
    ) submatches,
    trace (breakups,rewrites),
    if breakups.empty then pure $ ([], list.map Use rewrites) else
    pure $ ([], list.map Use breakups)

|_ := do -- MERGE
    /- Find rules which will:
        a. perform a factorisation such that `x` is factorised.
        b. perform a straight merge such as `F(x) ∩ F(x) = F(x)` or `x + x = 2 * x`
        c. annihilate one instance of `x`. For example `x * 0 = 0`. 

        In general, this will produce too many bad candidates. 
        You don't want `x ∩ x = x` to be seen as a good idea for a number problem, how to refine?
        1. use n-gram triggers to suggest rules.
        2. Use this subtask to refine sets of rules produced by other subtasks.
    -/
    notimpl
end

meta def strategy.execute : strategy → M unit
|(strategy.ReduceDistance a b) := do
    repeat (do 
        h ← get_distance_reducer a b,
        run_conv $ rule_app.rewrite_conv h
    )
|s@(strategy.Use r)            := 
    run_conv $ rule_app.rewrite_conv r

meta def strategy.refine : strategy → M refinement
|(strategy.ReduceDistance a b) := pure $ ([],[])
|(strategy.Use r)              := do
    ce ← get_ce,
    scs ← zipper.smallest_absent_subterms ce r.lhs,

    -- subs : list zipper ← zipper.minimal_monotone (λ lz,
    --     if lz.is_mvar || lz.is_constant then failure else do
    --     --⟨r,ms⟩ ← rule.to_mvars r,
    --     l : list unit ← zipper.maximal_monotone (λ rz, (hypothetically' $ unify lz.current rz.current)) $ zipper.zip $ ce,
    --     if l.empty then pure lz else failure
    -- ) $ zipper.zip $ r.lhs,
    subs ← scs.mmap (λ z, task.Create z.1 <$> instantiate_mvars z.2.current),
    pure ⟨subs, []⟩


end robot