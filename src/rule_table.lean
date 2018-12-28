import .table .rule .zipper
open tactic ez
namespace robot
#check simp_lemmas

meta structure submatch :=
(r : rule) -- the original rule
(z : zipper) -- a zipper on `r.rhs` 

namespace submatch
    meta def run : expr → submatch → tactic rule | e ⟨r,z⟩ := do
        ⟨result,hs⟩ ← src.introduce_context z.ctxt,
        let current := expr.instantiate_vars z.current hs,
        refine ```(%%e = %%current),
        n ← num_goals,
        when (n≠0) (fail "not all metavariables were accounted for."),
        set_goals [result],
        tactic.reflexivity,
        result ← instantiate_mvars result,
        r₁ ← rule.of_prf result,
        zipper.apply_rule r₁ z
        
end submatch

meta structure rule_table := 
(head_table : tabledict name rule)
(submatch_table : listdict name submatch)


namespace rule_table 

    meta def empty : rule_table := {head_table := ∅, submatch_table := ∅}

    meta def get_key : expr → name
    |(expr.app f a) := get_key f
    |(expr.const n _) := n
    |(expr.var n) := `rule_table.wildcard
    |e := `rule_table.default
    meta def map_head_table (f : tabledict name rule → tabledict name rule) : rule_table → rule_table |rt := {rt with head_table := f rt.head_table}
    meta def insert : rule → rule_table → tactic rule_table
    | r {head_table:=ht, submatch_table := st} := do
        ppr ← pp r,
        st ← zipper.traverse_proper (λ st z, pure $ listdict.insert (get_key z.current) (submatch.mk r z) st) st $ zipper.zip_with_metas r.ctxt r.rhs,
        pure { head_table := tabledict.insert (get_key r.lhs) r ht
             , submatch_table :=  st
             }
    
    meta def of_rules : list rule → tactic rule_table := list.mfoldl (function.swap insert) empty
    private meta def get_head_rewrites : name → rule_table → table rule | k {head_table := ht, ..} := ht.get k
    meta def head_rewrites : expr → rule_table → (tactic $ list rule) := λ lhs rt, do
        let k := get_key lhs,
        kpp ← pp k,
        let t := get_head_rewrites `rule_table.wildcard rt ∪ get_head_rewrites k rt,
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

    meta instance : has_to_tactic_format rule_table := ⟨tactic.pp ∘ head_table⟩

    /--`submatch e rt` finds rules such that the rhs of the rule contains `e`-/
    meta def submatch : expr → rule_table → tactic (list rule) | e rt := do
        let k := get_key e, -- [TODO] need to guard against wildcards.
        let items := rt.submatch_table.get k,
        rules ← items.mmap (robot.submatch.run e),
        pure rules

end rule_table


end robot