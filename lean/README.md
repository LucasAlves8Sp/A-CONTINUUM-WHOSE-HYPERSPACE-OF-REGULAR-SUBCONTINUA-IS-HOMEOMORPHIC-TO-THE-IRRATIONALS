# RegSub — Lean 4 formalization of Theorem A

Lean 4 / Mathlib formalization accompanying the paper
*A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals*
(supplementary material).

The whole proof of Theorem A is formalized, including the classical results it uses
(the Alexandrov–Urysohn theorem and `ℕ^ℕ ≅ ℝ \ ℚ`). There is no `sorry`, no added `axiom` and no
hypothesis: `#print axioms` reports only Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## The main theorem

```lean
theorem RegSub.theoremA_l2 :
    ∃ X : Set (lp (fun _ : ℕ => ℝ) 2), IsCompact X ∧ IsConnected X ∧ X.Nontrivial ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) ∧
      Nonempty (regularSubcontinua X ≃ₜ {x : ℝ // Irrational x})
```

(`RegSub/Main.lean`). Here `lp (fun _ : ℕ => ℝ) 2` is the Hilbert space `ℓ²`, and

```lean
def regularSubcontinua (X : Type) [MetricSpace X] : Set (NonemptyCompacts X) :=
  {A | IsConnected (A : Set X) ∧ closure (interior (A : Set X)) = A}
```

is `𝒟(X)`, the set of regular subcontinua, with the topology of `NonemptyCompacts X`.
`SanityChecks.lean` confirms by `rfl` that this topology is the topology of the Hausdorff metric.
The abstract form `RegSub.theoremA_unconditional` states the same for a compact connected metric
space `X`.

## Files and the paper

The files are listed in dependency order (4618 lines in all). Paper numbers refer to the paper (v15).

| File | Lines | Content | Paper |
| --- | ---: | --- | --- |
| `RegSub/Tree.lean` | 220 | the index tree `Piece`, descendants `IsDesc`, tree paths `OnPath`, convexity | §3.2 |
| `RegSub/CodeSpace.lean` | 198 | admissible sets `Admissible` (conditions (a)–(c)), the code modifications of both cases of Prop. 5.4 | Thm 4.6, Prop. 5.4 |
| `RegSub/Topology.lean` | 276 | the code space `codeSet` is nonempty, `G_δ` and zero-dimensional, and its compact subsets have empty interior | Prop. 5.3, Prop. 5.4 (code form) |
| `RegSub/GdeltaPolish.lean` | 52 | a `G_δ` subset of a Polish space is Polish | Fact 2.5(a) |
| `RegSub/TheoremA.lean` | 79 | Theorem A from two intermediate statements (both proved later) | §5 |
| `RegSub/Knaster.lean` | 477 | the template `K`: inverse limit of the tent map; compact, connected, nondegenerate; Fact 2.4(a) | §3.1, Fact 2.4(a) |
| `RegSub/Composant.lean` | 259 | composants (`Joinable`), Baire category, Fact 2.4(d), the template points | Fact 2.4, Lemma 3.1 |
| `RegSub/AlexandrovUrysohn.lean` | 312 | the Alexandrov–Urysohn theorem, by a Lusin scheme | Fact 2.5(b) |
| `RegSub/Irrational.lean` | 85 | `ℕ^ℕ ≅ ℝ \ ℚ`, from Alexandrov–Urysohn | Fact 2.5(c) |
| `RegSub/Hilbert.lean` | 345 | `ℓ²`, coordinate blocks `J P`, `C P`, the embedding `ι : K → ℓ²` | §3.3 |
| `RegSub/Construction.lean` | 500 | scales, attaching points, the maps `φ_P`, coordinates, finiteness of `𝒫_N` | §3.2–3.3, Lemma 3.2, Lemma 3.3(a) |
| `RegSub/Geometry.lean` | 415 | the sets `Y_P`, `Z_P`, `X`; Lemma 3.3(b)–(h) | Lemma 3.3 |
| `RegSub/Interiors.lean` | 266 | relative interiors; Lemma 3.5(a),(c) | Lemma 3.5 |
| `RegSub/Description.lean` | 359 | retractions, branches, crossing, atoms, Lemma 4.5 | Lemmas 4.2–4.5 |
| `RegSub/Theorem46.lean` | 443 | Theorem 4.6 (both directions) and Lemma 5.1 | Thm 4.6, Lemma 5.1 |
| `RegSub/Identification.lean` | 273 | `Φ : 𝒟(X) ≃ₜ 𝔇` | Prop. 5.2 |
| `RegSub/Main.lean` | 59 | Theorem A | Theorem A |

Main declarations:

| Lean declaration | Paper |
| --- | --- |
| `Knaster`, `isCompact_knaster`, `isConnected_knaster`, `knaster_nontrivial` | the template continuum `K` |
| `eq_univ_of_interior_nonempty` | Fact 2.4(a): a closed connected subset of `K` with nonempty interior is `K` |
| `Joinable`, `eq_univ_of_not_joinable`, `isMeagre_joinable` | composants; Fact 2.4(c); composants are meagre |
| `dense_compl_of_countable`, `dense_diff_finite` | Fact 2.4(d) |
| `Template`, `exists_template`, `tmpl` | Lemma 3.1 |
| `alexandrovUrysohn` | Fact 2.5(b), Kechris Theorem 7.7 |
| `baire_homeomorph_irr` | Fact 2.5(c) |
| `isGδ_polishSpace` | Fact 2.5(a), direction used |
| `lam`, `lam_childOf`, `tpt`, `opt`, `pt`, `phi` | scales `λ_P`, attaching points `t_P`, `o_P`, `p_P`, maps `φ_P` |
| `C_phi_self`, `C_phi_of_not_isDesc`, `C_phi_of_isDesc_child` | Lemma 3.2 |
| `finite_lam_ge`, `Y_subset_closedBall`, `Y_eq`, `C_of_mem_Y_child`, `C_of_mem_Z`, `C_eq_zero_iff_of_mem_Y`, `disjoint_Y_child`, `Y_child_inter_piece`, `X_eq_Y_union_Z`, `Y_inter_Z`, `isCompact_X`, `isConnected_X` | Lemma 3.3(a)–(h) |
| `piece_subset_closure_relInt_block`, `relInt_piece_disjoint`, `X_subset_closure_Ublk` | Lemma 3.5(a),(c) |
| `X_eq_brY_union_brZ`, `brY_inter_brZ`, `not_joinable_brT` | Lemma 4.2 (closed sides of the branches) |
| `ret`, `mem_of_cut`, `piece_subset_of_crossing` | Lemma 4.3 |
| `piece_subset_of_relInt` | Lemma 4.4 |
| `eq_closure_blocks`, `blocksU_subset_closure_relInt` | Lemma 4.5 |
| `pcs_admissible`, `reg_Psi`, `pcs_Psi`, `Psi_pcs` | Theorem 4.6 |
| `dense_iff_infinite` | the encoded condition (c) is the density condition (c) |
| `hausdorffDist_Psi_le` | Lemma 5.1 |
| `PhiHomeo`, `geometricIdentification` | Proposition 5.2 |
| `isGδ_codeSet`, `instZeroDimensionalSpaceCodeSet`, `codeSet_nonempty` | Proposition 5.3 |
| `isCompact_interior_eq_empty` | Proposition 5.4, code form |
| `theoremA_l2`, `theoremA_unconditional`, `DX_homeomorph_baire` | Theorem A |

## Translation notes

The formalization follows the proof in the paper. It differs in presentation in the following
points, none of which changes the mathematics.

* **The template.** `K` is the inverse limit of the tent map `t ↦ min(2t, 2 − 2t)` on `[0,1]`,
  as a subset of `ℕ → ℝ` with the product topology (`Knaster`). This is a standard model of the
  Knaster continuum. The paper only uses that `K` is a nondegenerate indecomposable continuum, and
  the Lean proof uses exactly Fact 2.4(a) for it (`eq_univ_of_interior_nonempty`). As a check,
  `SanityChecks.lean` derives from it that `K` is indecomposable (`knaster_indecomposable`).
* **Composants.** "In distinct composants" is formalized as `¬ Joinable x y`: no proper closed
  connected subset contains both points. This is the property used in the paper (Fact 2.4(c)).
  Lemma 3.1 is proved with the Baire category theorem: the composant of a point is meagre
  (`isMeagre_joinable`), so every nonempty open set has points outside any countably many
  composants.
* **The realization.** Each piece `P` gets its own infinite block of coordinates
  `blk P n` of `ℓ²` (instead of a plane). `J P` puts a vector into that block and `C P` reads it
  back, so `C P` plays the role of the orthogonal projection `π_P`. The template is embedded by
  `ι z = (2^{-(n+1)} z_n)ₙ`, so `‖ι z − ι z'‖ ≤ 1`.
  The pieces are `φ_P(z) = p_P + λ_P · J_P(ι z − ι o_P)`.
* **The root.** The root offset `o_{B_∅}` is `ρ` (the paper uses `(0,0)`); then
  `p_{B_∅} = 0` lies in the root piece. Lemma 3.3(e) is used only for non-root pieces, as in the
  paper.
* **Indexing.** The paper uses `ℕ = {1,2,…}`; Lean starts at `0`. With this shift the scales are
  the paper's: `lam (childOf P n) = lam P / 2^(n+2)`. `block β` stores the most recent pair first,
  so `B_{β⌢(m,k)}` is `block ((m,k) :: β)`.
* **Interiors.** `relInt A` is the interior of `A ∩ X` relative to `X`; `reg_iff` shows that the
  Lean notion of a regular subcontinuum of the subspace `X` agrees with `Reg`.
* **Condition (c).** With a countable base `(V_j)` of `K`, `Nset j = {k | a_k ∈ V_j}`; an included
  spine must have, for every `j`, infinitely many included children with index in `Nset j`.
  `dense_iff_infinite` proves this equivalent to density of the included attaching points.
* **Tree paths.** `OnPath P R Q` says that `Q` is an ancestor of `P` or `R` and that `P`, `R` do not
  both lie below a single child of `Q`; this is `Q ∈ [P, R]`. Most proofs use the equivalent
  parent-closed form of convexity (`pathConvex_iff_parentClosed`).
* **Proposition 5.4.** It is proved in the code space (`isCompact_interior_eq_empty`) and
  transferred to `𝒟(X)` through `PhiHomeo`. Lemma 3.5(b) and the limit continua `A*` of the paper
  are not needed. In Case 2, `cutHead` deletes the subtrees below all children `j < k`; on the
  convex sets to which it is applied this agrees with the paper.
* **Lemma 3.5(c).** The proof shows that every piece lies in the closure of `U` and uses that `X`
  is the closure of the union of the pieces; the branch limits of Lemma 3.3(h) are not needed.
  The paper (v15) now gives this proof.

## Checks

The logs are in [`checks/`](checks/), and `checks/run_checks.sh` reproduces them.

* `lake build` builds every module with no errors. Its only messages are style warnings suggesting
  the `module` keyword for files importing Mathlib; they do not affect the results. Compiled
  directly with `lean`, the modules give no warnings at all.
* `CheckAxioms.lean` prints the axioms of the main results (expected output below).
* `SanityChecks.lean` prints the elaborated statements and checks examples: tree paths, small
  admissible and non-admissible sets, values of the tent map, the parent map of `childOf`, the scale
  recursion, `φ_P(o_P) = p_P`, nondegeneracy of `X`, indecomposability of `K`, and that the
  Vietoris topology on `NonemptyCompacts` is the Hausdorff-metric topology.
* Every module was replayed through the kernel with `leanchecker` (exit code 0).
* `RegSub.theoremA_l2`, `RegSub.theoremA_unconditional` and all their dependencies (23,932
  declarations, including the Mathlib ones) were exported with `lean4export` and checked by the
  independent type checker `nanoda`: no errors, and the only axioms are `propext`,
  `Classical.choice` and `Quot.sound`.

## Building

The project needs Lean `v4.35.0` (see `lean-toolchain`) and Mathlib at commit
`6015dbbfc399f4548bafd46f9560ff61595fd328`, pinned in `lakefile.toml`.

```
lake update        # fetch Mathlib at the pinned commit
lake exe cache get # download prebuilt Mathlib
lake build
lake env lean CheckAxioms.lean
lake env lean SanityChecks.lean
```

Expected output of `CheckAxioms.lean`:

```
'RegSub.theoremA_l2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.theoremA_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.DX_homeomorph_baire' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.alexandrovUrysohnStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.geometricIdentification' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.alexandrovUrysohn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.baire_homeomorph_irr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isGδ_polishSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.eq_univ_of_interior_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isConnected_knaster' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.exists_template' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.Y_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.Y_inter_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isCompact_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isConnected_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.nontrivial_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.piece_subset_closure_relInt_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.X_subset_closure_Ublk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.piece_subset_of_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.piece_subset_of_relInt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.eq_closure_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.pcs_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.reg_Psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.pcs_Psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.hausdorffDist_Psi_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.PhiHomeo' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.pathConvex_iff_parentClosed' depends on axioms: [propext, Quot.sound]
'RegSub.codeSet_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isGδ_codeSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.instZeroDimensionalSpaceCodeSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isCompact_interior_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.codeSet_homeomorph_baire' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.theoremA' depends on axioms: [propext, Classical.choice, Quot.sound]
```
