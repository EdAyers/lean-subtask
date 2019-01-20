import .data

namespace robot


constants (T : Type) [has_lt T] [decidable_rel ((<) : T → T → Prop)]
constants (S : Type) [has_lt S] [decidable_rel ((<) : S → S → Prop)]
constants (M : Type → Type) [monad M] [alternative M]
meta class system :=
(strat_test : S → M bool)
(strat_merge : S → S → M S)
(strat_refine : S → M (list S × list T))
(strat_execute : S → M unit)
(task_test : T → M bool)
(task_refine : T → M (list S × list T))

end data

namespace system

variables {T : Type} [has_lt T] [decidable_rel ((<) : T → T → Prop)]
variables {S : Type} [has_lt S] [decidable_rel ((<) : S → S → Prop)]
variables {M : Type → Type} [monad M] [alternative M]
variables [system T S M]
def refinement := list S × list T

inductive tree_entry 
|task (t : T) (achieved : list T) : tree_entry
|strat (s : S) : tree_entry

namespace tree_entry
    def test : tree_entry  → M bool
    |(task t acs) := system.task_test t
    |(strat s) := system.strat_test s
end tree_entry

end system

end robot
