# Human-oriented Term Rewriting.

A prototype implementation of the subtasks algorithm in Lean for solving simple equalities.

## Build & Run

This code uses Lean 3.4.2 but should still work on newer versions of Lean 3.

1. Install [Lean](https://github.com/leanprover/lean). This best way is probably to install [elan](https://github.com/khoek/elan/) by running the script
    ``` sh
    curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh
    ```
2. It is recommended that you view the examples files within the supported editors:
      + [VSCode](https://code.visualstudio.com/)
            with the [Lean extension](https://marketplace.visualstudio.com/items?itemName=jroesch.lean).
      + [Emacs](https://www.gnu.org/software/emacs/) with [lean-mode](https://github.com/leanprover/lean-mode).
3. In the terminal, `cd` to the root directory for `lean-subtask` and run `leanpkg build`. This will pull and verify mathlib and will take about 20 mins on the first run, but after that the proofs for mathlib are saved.
4. Open any file from the examples folder and inspect Lean Messages to see the `equate` tactic in action

