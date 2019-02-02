
import .table .rule .zipper
open tactic ez
namespace robot

@[derive decidable_eq]
meta structure submatch :=
(r : rule) -- the original rule
(z : zipper) -- a zipper on `r.rhs`

namespace submatch
    open tactic
    -- meta def intro_metas : list expr → list hyp → tactic (list expr)
    -- |acc (⟨n,b,y⟩::rest) := do 
    --     let y := expr.instantiate_vars y acc,
    --     mv ← tactic.mk_meta_var y,
    --     intro_metas (mv::acc) rest
    -- |acc [] := pure acc
    /--`run e s` attempts to unify `e` with the subterm of `s` and then returns a rule depending on fresh metavariables.-/
    -- meta def run : expr → submatch → tactic rule | e ⟨r,z⟩ := do -- [TODO] return a `submatch_result` which also scores the match.
    --     gs ← get_goals,
    --     e_type ← infer_type e,
    --     ms ← intro_metas [] $ r.ctxt.reverse,
    --     set_goals ms,
    --     let current := expr.instantiate_vars z.current ms,
    --     current_type ← infer_type current,
    --     unify current_type e_type,
    --     all_goals $ try $ apply_instance,
    --     current ← instantiate_mvars current,
    --     unify e current,
    --     --ctxt : list $ hyp × expr × option expr ← list.zip r.ctxt <$> list.mmap (λ h, (some <$> get_assignment h) <|> pure none) ms,
    --     ms ← ms.mmap instantiate_mvars,
    --     set_goals gs,
    --     rule.of_prf $ expr.mk_app r.pf ms.reverse

    -- [BUG] run and run_app are setting metavariables in the global tactic state.
    -- This is a common problem that I have; I want to be able to take 
    meta def run_app : expr → submatch → tactic rule
    | e ⟨r,z⟩ := do

        (expr.app f a) ← pure e,
        (mrule, ms) ← rule.to_mvars r,
        if ¬z.ctxt.empty then fail "not implemented when z contains bound variables" else do
        current@(expr.app f₂ a₂) ← pure $ expr.instantiate_vars z.current $ ms.reverse,
        -- current ← instantiate_mvars current,
        -- trace_m "submatch.run_app: " $ (e, z),
        unify f₂ f,
        unify a₂ a,
        --trace_state,
        mrule.instantiate_mvars

    
    meta def run : expr → submatch → tactic rule | e ⟨r,z⟩ := do
        --e ← instantiate_mvars e,
        (mrule, ms) ← rule.to_mvars r,
        if ¬z.ctxt.empty then fail "not implemented when z contains bound variables" else do
        let current := expr.instantiate_vars z.current $ ms.reverse,
        current ← instantiate_mvars current,
        --trace_m "submatch.run: " $ current,
        unify current e, -- [TODO] for some reason this can't unify `A ?m_1` and `?m_2 ?m_3`?
        --trace_state,
        mrule.instantiate_mvars
        
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

    meta def of_names (ns : list name) : tactic rule_table := do
        rs ← ns.mmap rule.of_name,
        revs ← rs.mmap rule.flip,
        of_rules $ rs ++ revs
    private meta def get_head_rewrites : name → rule_table → table rule | k {head_table := ht, ..} := ht.get k
    meta structure rewrites_config :=
    (wilds := ff) -- include rules such as `?x = ?x * 1` where the lhs can be anything. This slows things down substantially. [TODO] optimise so that there are some type/typeclass checks on it.
    -- (annihilators := ff) [TODO]
    
    meta def head_rewrites (lhs : expr) (rt : rule_table)  (cfg : rewrites_config := {}) : (tactic $ list rule) := do
        let k := get_key lhs,
        kpp ← pp k,
        let wilds := if cfg.wilds then get_head_rewrites `rule_table.wildcard rt else ∅,
        let keyed := get_head_rewrites k rt,
        let t := wilds ∪ keyed,
        tpp ← pp t,
        --trace $ ("getting key ":format) ++ kpp ++ " with rules " ++ tpp,
        t.mfold (λ acc r, (do r ← rule.head_rewrite r lhs, pure $ r :: acc) <|> pure acc) []

    private meta def rewrites_aux (rt : rule_table) (cfg : rewrites_config) : zipper → list rule → tactic (list rule)
    |z acc := do
        -- trace z,
        hrs ← head_rewrites z.current rt cfg,
        -- trace head_rewrites,
        hrs ← list.mcollect (λ rw, ez.zipper.apply_rule rw z) hrs,
        --trace head_rewrites,
        acc ← pure $ hrs ++ acc,
        ⟨f,children⟩ ← z.down_proper,
        --trace children,
        acc ← children.mfoldl (λ acc z, rewrites_aux z acc) acc,
        pure acc

    -- [TODO] add a 'specificity score'. How likely is it that the given rule would match?
    -- [TODO] wildcard moves should have their own section, since one is constructed for each node in the tree.
    -- [TODO] similarly, anti-annihilator moves (moves which have metas after matching) should be put in their own section. If my understanding of Lean is correct, it should be possible to simply add these as metavariables to the tactic state.

    meta def rewrites (lhs : expr) (rt : rule_table) (cfg : rewrites_config := {}) : (tactic $ list rule) := rewrites_aux rt cfg (zipper.zip lhs) []

    meta instance : has_to_tactic_format rule_table := ⟨tactic.pp ∘ head_table⟩

    /--`submatch e rt` finds rules such that the rhs of the rule contains `e`-/
    meta def submatch : expr → rule_table → (tactic (list rule)) | e rt :=
        let key := get_key e in
        let submatches := rt.submatch_table.get key in
        if (key = `rule_table.app ) then list.mcollect (robot.submatch.run_app e) submatches
        else 
        -- trace_m "submatch: " $ submatches,
        list.mcollect (robot.submatch.run e) submatches

end rule_table


end robot