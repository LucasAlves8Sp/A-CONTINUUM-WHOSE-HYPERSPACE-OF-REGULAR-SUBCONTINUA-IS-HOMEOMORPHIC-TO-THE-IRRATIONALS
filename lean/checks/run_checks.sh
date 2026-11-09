#!/usr/bin/env bash
# Reproduce the checks recorded in this folder. Run from `lean/` after `lake build`.
#
# Tools: `leanchecker` ships with Lean; `lean4export` (https://github.com/leanprover/lean4export)
# and `nanoda_bin` (https://github.com/ammkrn/nanoda_lib) are external. Override the binary
# names with LEANCHECKER, LEAN4EXPORT and NANODA if needed.
set -euo pipefail
LEANCHECKER=${LEANCHECKER:-leanchecker}
LEAN4EXPORT=${LEAN4EXPORT:-lean4export}
NANODA=${NANODA:-nanoda_bin}
MODULES="Tree CodeSpace Topology GdeltaPolish TheoremA Knaster Composant AlexandrovUrysohn
  Irrational Hilbert Construction Geometry Interiors Description Theorem46 Identification Main"

echo "== axioms"
lake env lean CheckAxioms.lean

echo "== sanity checks"
lake env lean SanityChecks.lean > /dev/null && echo "SanityChecks.lean: ok"

echo "== kernel replay (leanchecker)"
for m in $MODULES; do
  lake env "$LEANCHECKER" "RegSub.$m"
  echo "RegSub.$m: ok"
done

echo "== external type checker (nanoda)"
lake env "$LEAN4EXPORT" RegSub.Main -- RegSub.theoremA_l2 RegSub.theoremA_unconditional \
  > checks/export.ndjson
"$NANODA" checks/nanoda.json
rm -f checks/export.ndjson
