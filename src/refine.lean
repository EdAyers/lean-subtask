import .M .zipper
namespace robot
open strategy task tactic
meta def strategy.merge : strategy → strategy → M strategy 
|(Use r₁) (Use r₂) := do
    unify r₁.lhs r₂.lhs,
    unify r₁.rhs r₂.rhs, 
    r ← rule.instantiate_mvars r₁,
    pure $ Use r
|_ _ := failure

meta def task.test : expr → task → M bool
|ce (task.Create e) := do
    e ← instantiate_mvars e,
    pp_ce ← pp ce, pp_e ← pp e,
    --trace_m "task.test: " $ (to_fmt "testing that " ++ pp_ce ++ " satisfies Create " ++ pp_e),
    matches : list ez.zipper ← ez.zipper.find_occurences (ez.zipper.zip ce) e ,
    --trace_m "task.test: " $ matches,
    pure $ bnot matches.empty
|ce t@(task.CreateAll e) := do
    -- trace_m "task.test: " $ t,
    o ← hypothetically (unify e ce), 
    pure o.is_some

/-- Do In One Move. Check the lookahead table and see if any of the entries in there cause the task to be achieved. -/
meta def task.diom : task → M (list strategy) := λ t, do
    ce ← get_ce,
    lookahead ← get_lookahead,
    list.mcollect (λ r, do 
        let rhs := rule.rhs r,
        let pf := rule.pf r,
        x : option rule ← M.hypothetically (do
                result ← task.test rhs t,
                if result then pure r else failure
        ),
        match x with
        |(some r) := pure $ strategy.Use $ r
        |none := failure
        end
    ) lookahead

meta def try_dioms : task → M refinement | t := do 
    -- trace "trying dioms",
    dioms ← task.diom t, 
    -- trace dioms,
    if ¬ dioms.empty then pure ([],dioms) else failure

open ez tactic
meta def get_distance_reducers : expr → expr → M (list rule)
| a b := do
    ce ← get_ce,
    current_dist ← zipper.get_distance ce a b,
    -- trace_m "\ngdr: " $ (ce, current_dist),
    rs ← get_lookahead,
    rs.mfilter (λ r, (do
        new_dist ← zipper.get_distance r.rhs a b,
        -- trace_m "gdr: " $ (r.rhs, new_dist),
        pure $ new_dist < current_dist) <|> pure ff
    )

meta def can_use_ReduceDistance : expr → M strategy := λ e, (do
    [a,b] ← zipper.get_proper_children e | failure,
    ce ← get_ce,
    [za] ← zipper.find_subterms a $ zipper.zip ce | failure,
    [zb] ← zipper.find_subterms b $ zipper.zip ce | failure,
    zipper.get_distance ce a b,
    _::_ ← get_distance_reducers a b | failure,
    -- trace_m "can_use_ReduceDistance" $ (a,b),
    pure $ ReduceDistance a b
    )

meta def task.refine (t : task) : M refinement :=
try_dioms t <|>
match t with
|(task.Create e) := do
    rss ← (list.singleton <$> can_use_ReduceDistance e) <|> pure [],
    -- trace_m "task.refine: " $ rss,
    ce ← get_ce,
    rt ← get_rule_table,
    submatches ← rt.submatch e,
    -- trace_m "task.refine: " $ submatches,
    strats ← pure $ list.map strategy.Use $ list.filter (λ r, ¬ rule.is_wildcard r) $ submatches,
    pure $ ([],rss ++ strats)
|(task.CreateAll a) := do
    ce ← get_ce >>= lift instantiate_mvars,
    -- trace_m "refine CreateAll: " $ ce,
    scs ← zipper.lowest_uncommon_subterms ce $ zipper.zip a,
    -- trace_m "refine CreateAll: " $ scs,
    if scs.length = 0 then notimpl else do
    let scs := task.Create <$> zipper.current <$> scs,
    pure $ (scs, [])
end

meta def strategy.execute : strategy → M unit
|(strategy.ReduceDistance a b) := do
    repeat (do 
        h::_ ← get_distance_reducers a b | failure,
        run_conv $ zipper.rewrite_conv h
    )
|s@(strategy.Use r)              := run_conv $ zipper.rewrite_conv r

meta def strategy.refine : strategy → M refinement
|(strategy.ReduceDistance a b) := pure $ ([],[])
|(strategy.Use r)              := do
    ce ← get_ce,
    ⟨r,ms⟩ ← rule.to_mvars r,
    subs : list zipper ← zipper.minimal_monotone (λ lz,
        if lz.is_mvar || lz.is_constant then failure else do
        ⟨r,ms⟩ ← rule.to_mvars r,
        l : list unit ← zipper.maximal_monotone (λ rz, (hypothetically' $ unify lz.current rz.current)) $ zipper.zip $ ce,
        if l.empty then pure lz else failure
    ) $ zipper.zip $ r.lhs,
    let subs := subs.map (λ z, task.Create $ z.current),
    pure ⟨subs, []⟩


end robot