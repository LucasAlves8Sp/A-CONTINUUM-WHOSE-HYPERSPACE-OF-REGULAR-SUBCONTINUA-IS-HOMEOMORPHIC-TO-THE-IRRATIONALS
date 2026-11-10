module

public import RegSub.Main

@[expose] public section

/-!
# Proved solution

`RegSub.regularSubcontinua` is defined in `RegSub/TheoremA.lean`, with the same definition as in
`Challenge.lean`, and `RegSub.theoremA_l2` is proved in `RegSub/Main.lean` from the whole
development in `RegSub/`. This module re-exports both. Comparator checks that they have exactly the
statements of their counterparts in `Challenge.lean` and that the proof uses only the permitted
axioms `propext`, `Classical.choice` and `Quot.sound`.
-/
