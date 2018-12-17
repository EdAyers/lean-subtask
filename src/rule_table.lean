import .table .rule .zipper
open tactic ez

#check simp_lemmas



meta def rule_table := tabledict name rule


namespace rule_table 

    meta def empty : rule_table := tabledict.empty
    meta def get_key : expr → name
    |(expr.app f a) := get_key f
    |(expr.const n _) := n
    |(expr.var n) := `rule_table.wildcard
    |e := `rule_table.default
    meta def insert : rule → rule_table → rule_table := λ r rt,
        tabledict.insert (get_key r.lhs) r rt
    meta def of_rules : list rule → rule_table
    := list.foldl (function.swap insert) empty


    meta def head_rewrites : expr → rule_table → (tactic $ list rule) := λ lhs rt, do
        let k := get_key lhs,
        kpp ← pp k,
        let t := rt.get `rule_table.wildcard ∪ rt.get k,
        tpp ← pp t,
        --trace $ ("getting key ":format) ++ kpp ++ " with rules " ++ tpp,
        t.mfold (λ r acc, (do r ← rule.head_rewrite r lhs, pure $ r :: acc) <|> pure acc) []

    private meta def rewrites_aux (rt : rule_table) : zipper → list rule → tactic (list rule)
    |z acc := do
        -- trace z,
        head_rewrites ← rt.head_rewrites z.current,
        --trace head_rewrites,
        head_rewrites ← head_rewrites.mcollect (λ rw, ez.zipper.apply_rule rw z),
        --trace head_rewrites,
        acc ← pure $ head_rewrites ++ acc,
        ⟨f,children⟩ ← z.down_proper,
        acc ← children.mfoldl (λ acc z, rewrites_aux z acc) acc,
        pure acc


    -- [TODO] add a 'specificity score'. How likely is it that the given rule would match?
    -- [TODO] wildcard moves should have their own section, since one is constructed for each node in the tree.
    -- [TODO] similarly, anti-annihilator moves (moves which have metas after matching) should be put in their own section. If my understanding of Lean is correct, it should be possible to simply add these as metavariables to the tactic state.


    meta def rewrites : expr → rule_table → (tactic $ list rule) := λ lhs rt, rewrites_aux rt (zipper.zip lhs) []

    meta instance : has_to_tactic_format rule_table := ⟨λ rt, do
        rt.mfold (λ k t acc, do
            head ← pp k,
            body ← t.mfold (λ r acc, do
                e ← pp r,
                pure $ acc ++ e ++ format.line
            ) format.nil,
            pure $ acc ++ format.nest 4 (head ++ format.line ++ body) ++ format.line
        ) format.nil
    ⟩

end rule_table


