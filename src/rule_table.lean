import .table .rule
open tactic

#check simp_lemmas

meta def rule_table := tabledict name rule


namespace rule_table 

    meta def empty : rule_table := tabledict.empty
    meta def get_key : expr → name
    |(expr.app f a) := get_key f
    |(expr.const n _) := n
    |e := `rule_table.default
    meta def insert : rule → rule_table → rule_table := λ r rt,
        tabledict.insert (get_key r.lhs) r rt
    meta def rewrites : expr → rule_table → list (tactic rule) := λ e rt,
        let k := get_key e in
        let t := rt.get k,


end rule_table


