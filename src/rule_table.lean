/- Author: E.W.Ayers © 2019 -/
import .table .rule_app .expr_zipper
open tactic expr
namespace robot

/-- A __submatch__ is a rule `r` and a zipper on `r.lhs`. 
They represent fragments of the LHS to match against some given term. -/
@[derive decidable_eq]
meta structure submatch :=
(r : rule) -- the original rule
(z : expr.zipper) -- a zipper on `r.rhs`

namespace submatch
    open tactic

    /-- [HACK] run_app does the same thing as `run` except that sometimes the unifier doesn't try to unify the function and argument separately. -/
    meta def run_app : expr → submatch → tactic rule_app
    | e ⟨r,z⟩ := do
        (expr.app f a) ← pure e,
        (mrule, ms) ← rule_app.of_rule r,
        if ¬z.ctxt.empty then fail "not implemented when z contains bound variables" else do
        current@(expr.app f₂ a₂) ← pure $ expr.instantiate_vars z.current $ ms.reverse,
        -- current ← instantiate_mvars current,
        -- tactic.trace_m "submatch.run_app: " $ (e, z),
        -- wrap in a 'hypothetically'' to keep the old assignment table.
        -- this means that any mvars in `e` are never assigned. 
        tactic.hypothetically' (do 
            unify f₂ f,
            unify a₂ a,
            -- not allowed any typeclass instances or
            problems ← ms.mfilter (λ m, do
                 y ← infer_type m,
                 iscl ← is_class y,
                 isprop ← is_prop y,
                 pure $ if iscl || isprop then tt else ff
            ),
            tactic.set_goals problems,
            -- trace_state,
            all_goals (apply_instance <|> assumption),

            n ← num_goals,
            guard (n = 0),

            
            mrule.instantiate_mvars
        ) 
        --trace_state,

    /--`run e s` attempts to unify `e` with the subterm of `s` and then returns a rule depending on fresh metavariables.-/
    meta def run : expr → submatch → tactic rule_app | e ⟨r,z⟩ := do
        --e ← instantiate_mvars e,
        (ra, ms) ← rule_app.of_rule r,
        if ¬z.ctxt.empty then fail "not implemented when z contains bound variables" else do
        let current := expr.instantiate_vars z.current $ ms.reverse,
        current ← instantiate_mvars current,
        -- tactic.trace_m "submatch.run: " $ current,
        -- [FIXME] duplicate code with `run_app`. 
        tactic.hypothetically' (do 
            unify current e, -- [HACK] for some reason this can't unify `A ?m_1` and `?m_2 ?m_3`? Current fix is `run_app`.
            --trace_state,
            ra.instantiate_mvars
        )

    meta def to_rule_app : submatch → tactic rule_app
    |⟨r,z⟩ := do
        ⟨ra,_⟩ ← rule_app.of_rule r,
        rule_app.head_rewrite ra z
        
    meta instance : has_to_tactic_format (submatch) := ⟨λ ⟨r,z⟩, pure (λ pr pz, "{" ++ pr ++ "," ++ format.line ++ pz ++ " }") <*> tactic.pp r <*> tactic.pp z⟩
end submatch

meta structure rule_table := 
(head_table : tabledict name rule)
(submatch_table : listdict name submatch)

namespace rule_table 

    meta def empty : rule_table := {head_table := ∅, submatch_table := ∅}

    meta def get_key : expr → name
    |(expr.app f a) := if f.is_var || expr.is_mvar f || f.is_local_constant then `rule_table.app else get_key f
    |(expr.const n _) := n
    |(expr.var n) := `rule_table.wildcard
    |e := `rule_table.default
    meta def map_head_table (f : tabledict name rule → tabledict name rule) : rule_table → rule_table |rt := {rt with head_table := f rt.head_table}
    meta def insert : rule → rule_table → tactic rule_table
    | r {head_table:=ht, submatch_table := st} := do
        ppr ← pp r,
        st ← zipper.traverse_proper (λ st z, pure $ listdict.insert (get_key z.current) (submatch.mk r z) st) st $ zipper.zip r.rhs,
        pure { head_table := tabledict.insert (get_key r.lhs) r ht
             , submatch_table :=  st
             }
    /-- Take each rule in r₁ and insert to r₂. -/
    meta def join (r₁ r₂ : rule_table) : tactic rule_table := tabledict.mfold (λ rt _ r, insert r rt) r₂ $ head_table $ r₁
    meta def joins (l : list rule_table) :tactic rule_table := list.mfoldl (λ acc rt, join rt acc) (rule_table.empty) l
    meta def of_rules : list rule → tactic rule_table := list.mfoldl (function.swap insert) empty
    meta def rules : rule_table → list rule := tabledict.to_list ∘ rule_table.head_table
    meta def of_names (ns : list name) : tactic rule_table := do
        rs ← ns.mmap rule.of_name,
        revs ← list.mchoose (λ r, do ic ← rule.is_commuter r, if ic then failure else rule.flip r) rs,
        of_rules $ rs ++ revs
    private meta def get_head_rewrites : name → rule_table → table rule | k {head_table := ht, ..} := ht.get k
    meta structure rewrites_config :=
    (wilds := ff) 
    -- setting wilds causes inclusion of rules such as `?x = ?x * 1` where the lhs can be anything. 
    -- This slows things down substantially 
    -- [TODO] these 'wild' rules are handled by their own system.
    -- [TODO] optimise so that there are some type/typeclass checks on it.
    -- (annihilators := ff) [TODO]
    
    meta def head_rewrites (lhs : expr) (rt : rule_table)  (cfg : rewrites_config := {}) : (tactic $ list rule_app) := do
        let k := get_key lhs,
        let wilds := if cfg.wilds then get_head_rewrites `rule_table.wildcard rt else ∅,
        let keyed := get_head_rewrites k rt,
        let t := wilds ∪ keyed,
        --  kpp ← pp k, tpp ← pp t,
        --  trace $ ("getting key ":format) ++ kpp ++ " with rules " ++ tpp,
        t.mfold (λ acc r, (do 
            ppr ← to_string <$> pp r,
            -- tactic.trace_m "hr: " $ ppr,
            ra ← rule_app.rule_rewrite r lhs,
            pure $ ra :: acc
            ) <|> pure acc
        ) []

    -- meta def head_rewrites_rhs (rhs : expr) (rt : rule_table) (cfg : rewrites_config := {}) : (tactic $ list rule) := do
    --     head_rewrites rhs rt >>= list.mmap rule.flip

    private meta def rewrites_aux (rt : rule_table) (cfg : rewrites_config) 
    : zipper → list rule_app → tactic (list rule_app)
    |z acc := do
        ppz ← to_string <$> pp z,
        hrs ← 
            -- timetac ("head_rewrites: " ++ ppz) $ 
            head_rewrites z.current rt cfg,
        -- tactic.trace_m "rewrites_aux: " $ hrs,
        hrs ← list.mchoose (λ rw, rule_app.head_rewrite rw z) hrs,
        acc ← pure $ hrs ++ acc,
        ⟨f,children⟩ ← z.down_proper,
        acc ← children.mfoldl (λ acc z, rewrites_aux z acc) acc,
        pure acc

    -- [TODO] wildcard moves should have their own section, since one is constructed for each node in the tree.
    -- [TODO] similarly, anti-annihilator moves (moves which have metas after matching) should be put in their own section.

    meta def rewrites (lhs : expr) (rt : rule_table) (cfg : rewrites_config := {}) : (tactic $ list rule_app) := 
    rewrites_aux rt cfg (zipper.zip lhs) []

    meta instance : has_to_tactic_format rule_table := ⟨tactic.pp ∘ head_table⟩

    /--`submatch e rt` finds rules such that the rhs of the rule contains `e`-/
    meta def submatch : expr → rule_table → tactic (list rule_app) | e rt := do
        let key := get_key e,
        let submatches := rt.submatch_table.get key,
        -- tactic.trace_m "submatch: " $ submatches,
        if (key = `rule_table.app) 
        then list.mchoose (robot.submatch.run_app e) submatches
        else list.mchoose (robot.submatch.run e) submatches
    meta def submatch_lhs : expr → rule_table → tactic(list rule_app) | lhs rt := do
        rs ← submatch lhs rt,
        pure rs
        -- rs.mmap rule_app.flip


end rule_table


end robot