import .rule .zipper .rule_table
/- Investigating how simp_lemmas works -/
open robot
namespace scratch1
open tactic

    run_cmd do
        mv ← mk_mvar,
        E ← to_expr ```(%%mv + %%mv),
        trace E,
        let E₂ := expr.abstract E mv,
        trace E₂,
        skip

end scratch1