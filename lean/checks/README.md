# Checks of the Lean development

These are the logs of the checks run on the formalization, with a script that reproduces them.
Lean 4.35.0 and Mathlib commit `6015dbbfc399f4548bafd46f9560ff61595fd328` were used.

| File | Content |
| --- | --- |
| `lake-build.log` | Output of a clean `lake build` (build directory deleted first). All 18 `RegSub` targets build. The only messages are 26 style warnings suggesting the `module` keyword for files importing Mathlib. |
| `run_checks.log` | Output of `run_checks.sh` (described below). |
| `run_checks.sh` | Reproduces the checks: run it from `lean/` after `lake build`. |
| `nanoda.json` | Configuration for `nanoda`. Only `propext`, `Classical.choice` and `Quot.sound` are permitted, and any other axiom is a hard error. |

`run_checks.sh` runs four checks.

1. `CheckAxioms.lean`. All 33 listed results depend only on `propext`, `Classical.choice` and
   `Quot.sound`. Among them are `RegSub.theoremA_l2`, the Alexandrov–Urysohn theorem,
   `ℕ^ℕ ≅ 𝕀` and Theorem 4.6.
2. `SanityChecks.lean` compiles.
3. `leanchecker` replays every one of the 17 modules through the Lean kernel.
4. `lean4export` exports `RegSub.theoremA_l2` and `RegSub.theoremA_unconditional` together with
   all their dependencies, including the Mathlib ones. The independent type checker `nanoda`
   then checks the export: **"Checked 23932 declarations with no errors"**. Before that line,
   nanoda prints the statement of `RegSub.theoremA_l2` and the three axioms used.

Compiled directly with `lean`, all modules build with no errors and no warnings. The source
contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern`.
