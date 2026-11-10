# Checks of the Lean development

These are the logs of the checks run on the formalization, together with a script that reproduces
them. They used Lean 4.35.0 and Mathlib commit `6015dbbfc399f4548bafd46f9560ff61595fd328`.

| File | Content |
| --- | --- |
| `lake-build.log` | Output of a clean `lake build` (build directory deleted first). Every target builds. The only warning is the deliberate `sorry` in `Challenge.lean`. |
| `comparator.log` | Output of `lake comparator`, which compares `Solution` with `Challenge`. The Lean kernel, nanoda and con-ron accept the solution. This local run used `--inadvisably-no-sandbox`, because `bwrap` was not available; `scripts/verify-comparator.sh` runs the sandboxed version. |
| `run_checks.log` | Output of `run_checks.sh`: the axiom check, the sanity checks, `leanchecker` on all 17 modules, and `lean4export` + `nanoda` on Theorem A with all its dependencies ("Checked 23933 declarations with no errors"). |
| `run_checks.sh` | Reproduces `run_checks.log`. Run it from the project root after `lake build`. |
| `nanoda.json` | Configuration for `nanoda`. It permits only `propext`, `Classical.choice` and `Quot.sound`, and any other axiom is a hard error. |
