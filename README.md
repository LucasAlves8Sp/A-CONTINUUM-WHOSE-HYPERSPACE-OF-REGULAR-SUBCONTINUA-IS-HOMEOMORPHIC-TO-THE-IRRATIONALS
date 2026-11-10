# RegSub: a continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals

A Lean 4 / Mathlib formalization of the complete proof of Theorem A of the paper

> Lucas Alves de Almeida, *A continuum whose hyperspace of regular subcontinua is homeomorphic to
> the irrationals*, preprint, Zenodo, [doi:10.5281/zenodo.23528477](https://doi.org/10.5281/zenodo.23528477);
> also [hexagon:2610.00570](https://hexagonmath.org/pdf/2610.00570v1).

The paper, its LaTeX source and the AI disclosure are on the `main` branch of
[the repository](https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS).
This project is laid out for submission to the [Palomar registry](https://palomar-registry.org/):
`Challenge.lean` states the theorem, `Solution.lean` proves it, and `comparator.json` tells
`lake comparator` how to compare them. The provenance and the other metadata are in `formalization.yaml`.

## The theorem

For a metric continuum `X` (a nonempty compact connected metric space), a subcontinuum is
*regular* if it equals the closure of its interior in `X`. `𝒟(X)` is the hyperspace of regular
subcontinua with the Hausdorff metric. Camargo, Ordoñez and Ramírez (Appl. Gen. Topol. 25 (2024),
Question 3.26; earlier in Ramírez's 2023 thesis, Pregunta 3.2.14) asked whether `𝒟(X)` can be
homeomorphic to the rationals or to the irrationals. Theorem A answers the irrational case.

**Theorem A.** There is a nondegenerate continuum `X` in the Hilbert space `ℓ²` such that `𝒟(X)` is
homeomorphic to the Baire space `ℕ^ℕ`, and hence to the space of irrational numbers.

The compared statement (`Challenge.lean`; proved as `RegSub.theoremA_l2` in `RegSub/Main.lean`) is

```lean
def regularSubcontinua (X : Type) [MetricSpace X] : Set (TopologicalSpace.NonemptyCompacts X) :=
  {A | IsConnected (A : Set X) ∧ closure (interior (A : Set X)) = (A : Set X)}

theorem theoremA_l2 :
    ∃ X : Set (lp (fun _ : ℕ => ℝ) 2), IsCompact X ∧ IsConnected X ∧ X.Nontrivial ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) ∧
      Nonempty (regularSubcontinua X ≃ₜ {x : ℝ // Irrational x})
```

In plain language: some compact, connected subset `X` of `ℓ²` with more than one point has a
hyperspace of regular subcontinua that is homeomorphic both to `ℕ → ℕ` with the product topology
and to the irrationals with the topology of `ℝ`.

* `lp (fun _ : ℕ => ℝ) 2` is `ℓ²`, and `X` enters as a subtype, so closure and interior are taken
  in `X`.
* `TopologicalSpace.NonemptyCompacts X` carries Mathlib's Vietoris topology. `SanityChecks.lean`
  proves by `rfl` that this is the topology of the Hausdorff metric.
* `X.Nontrivial` is not in the paper's statement. A continuum is usually required to be
  nondegenerate, and the conclusion forces it anyway.

There is no `sorry` outside `Challenge.lean`, no added axiom and no hypothesis. The proof uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## How the proof goes

1. **The template.** `K` is a model of the Knaster continuum: the inverse limit of the tent map,
   in `RegSub/Knaster.lean`. Lean proves that it is compact, connected and nondegenerate, and that
   every closed connected subset with nonempty interior is all of `K`. `RegSub/Composant.lean`
   chooses the template points of Lemma 3.1: points in distinct composants, with dense tails. They
   are found with the Baire category theorem, since a composant is meagre.
2. **The construction.** The continuum `X` is the closure of a countable tree of scaled copies of
   `K`, each in its own block of coordinates of `ℓ²` (`RegSub/Hilbert.lean`,
   `RegSub/Construction.lean`). Pieces alternate between blocks (dense interior) and spines (empty
   interior); each spine carries densely attached child blocks. `RegSub/Geometry.lean` proves the
   geometry of Lemma 3.3: the subtrees, their diameters, the coordinates of points, and that `X`
   is compact and connected.
3. **Regular subcontinua.** `RegSub/Interiors.lean`, `RegSub/Description.lean` and
   `RegSub/Theorem46.lean` prove Theorem 4.6: a regular subcontinuum is determined by the set of
   pieces it contains. The sets of pieces that occur are exactly the nonempty sets that are convex
   in the tree and satisfy a density condition at every included spine.
4. **Topology.** `RegSub/Identification.lean` proves Proposition 5.2: this coding is a homeomorphism
   `𝒟(X) ≃ₜ 𝔇` onto a code space `𝔇 ⊆ 2^𝒫`. `RegSub/Topology.lean` shows that `𝔇` is nonempty,
   `G_δ` and zero-dimensional, hence Polish, and that every compact subset of `𝔇` has empty
   interior.
5. **Conclusion.** `RegSub/AlexandrovUrysohn.lean` proves the Alexandrov–Urysohn theorem (Kechris,
   Theorem 7.7) with a Lusin scheme, so `𝔇 ≅ ℕ^ℕ`. `RegSub/Irrational.lean` derives
   `ℕ^ℕ ≅ ℝ \ ℚ` from it, and `RegSub/Main.lean` combines everything.

## Sources, what is new, and what is not formalized

* **Sources.** The result and its proof are those of the paper above, which is the first
  presentation of Theorem A. The paper presents Theorem A as an answer to the irrational case of
  the question of Camargo, Ordoñez and Ramírez. A literature comparison made while the paper was
  prepared found no earlier answer, but novelty has not been independently established. The
  classical results used are the Alexandrov–Urysohn characterization of the Baire space (Kechris,
  *Classical Descriptive Set Theory*, Theorem 7.7) and basic facts on indecomposable continua
  (Nadler, *Continuum Theory*, Chapter XI). The project proves the instances it needs.
* **What is proved.** Everything needed for Theorem A, including the classical results.
* **Not formalized**, because Theorem A does not use them:
  * Example 2.6;
  * Lemma 3.5(b);
  * the branch-limit sentence of Lemma 3.3(h);
  * the geometric form of Proposition 5.4 (the non-regular limit continua `A*`);
  * Remarks 4.7 and 5.5–5.7;
  * Section 6 on the rational case, which remains open.
* **Divergences from the paper.** These are listed under *Translation notes* below. All of them
  concern presentation, not the mathematics.
* **Previous formalization.** Release
  [v1.0.1](https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS/tree/v1.0.1)
  of the same repository formalized only the combinatorial core. It derived Theorem A from two
  hypotheses, the Alexandrov–Urysohn theorem and the geometric identification, both of which are
  now proved. Its files (`Tree`, `CodeSpace`, `Topology`, `GdeltaPolish`, `TheoremA`) are reused,
  changed only to use the module system.

## Authorship and AI involvement

**Lucas Alves de Almeida** is the author and the responsible maintainer. He chose the problem,
supplied the literature, directed the work and reviewed its outputs; he did not write the Lean
code.

**Claude Opus 5.5 (Anthropic)**, working as an agent:

* proposed the construction and wrote the proofs of the paper together with the author;
* wrote this entire formalization;
* ran the checks below.

ChatGPT-Astra (OpenAI) was used with the author to check versions of the manuscript, not the Lean
code. The AI disclosure of the paper gives the full account. The first prompt of the project is
kept unedited in `prompt/first-prompt.md` on the `main` branch.

No independent human expert has reviewed the paper or the Lean statement. The statement was audited
against the paper by the producing agent (see `SanityChecks.lean` and `REVIEW_AND_VERIFICATION.md`
on the `main` branch). Its correctness relies on the mechanical checks below.

## Files and the paper

The files are listed in dependency order (4686 lines in all). Paper numbers refer to the paper (v15).

| File | Lines | Content | Paper |
| --- | ---: | --- | --- |
| `RegSub/Tree.lean` | 224 | the index tree `Piece`, descendants `IsDesc`, tree paths `OnPath`, convexity | §3.2 |
| `RegSub/CodeSpace.lean` | 202 | admissible sets `Admissible` (conditions (a)–(c)), the code modifications of both cases of Prop. 5.4 | Thm 4.6, Prop. 5.4 |
| `RegSub/Topology.lean` | 280 | the code space `codeSet` is nonempty, `G_δ` and zero-dimensional, and its compact subsets have empty interior | Prop. 5.3, Prop. 5.4 (code form) |
| `RegSub/GdeltaPolish.lean` | 56 | a `G_δ` subset of a Polish space is Polish | Fact 2.5(a) |
| `RegSub/TheoremA.lean` | 83 | Theorem A from two intermediate statements (both proved later) | §5 |
| `RegSub/Knaster.lean` | 481 | the template `K`: inverse limit of the tent map; compact, connected, nondegenerate; Fact 2.4(a) | §3.1, Fact 2.4(a) |
| `RegSub/Composant.lean` | 263 | composants (`Joinable`), Baire category, Fact 2.4(d), the template points | Fact 2.4, Lemma 3.1 |
| `RegSub/AlexandrovUrysohn.lean` | 316 | the Alexandrov–Urysohn theorem, by a Lusin scheme | Fact 2.5(b) |
| `RegSub/Irrational.lean` | 89 | `ℕ^ℕ ≅ ℝ \ ℚ`, from Alexandrov–Urysohn | Fact 2.5(c) |
| `RegSub/Hilbert.lean` | 349 | `ℓ²`, coordinate blocks `J P`, `C P`, the embedding `ι : K → ℓ²` | §3.3 |
| `RegSub/Construction.lean` | 504 | scales, attaching points, the maps `φ_P`, coordinates, finiteness of `𝒫_N` | §3.2–3.3, Lemma 3.2, Lemma 3.3(a) |
| `RegSub/Geometry.lean` | 419 | the sets `Y_P`, `Z_P`, `X`; Lemma 3.3(b)–(h) | Lemma 3.3 |
| `RegSub/Interiors.lean` | 270 | relative interiors; Lemma 3.5(a),(c) | Lemma 3.5 |
| `RegSub/Description.lean` | 363 | retractions, branches, crossing, atoms, Lemma 4.5 | Lemmas 4.2–4.5 |
| `RegSub/Theorem46.lean` | 447 | Theorem 4.6 (both directions) and Lemma 5.1 | Thm 4.6, Lemma 5.1 |
| `RegSub/Identification.lean` | 277 | `Φ : 𝒟(X) ≃ₜ 𝔇` | Prop. 5.2 |
| `RegSub/Main.lean` | 63 | Theorem A | Theorem A |

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
  The paper (v15) gives this proof.

## Checks

The logs are in [`checks/`](checks/), and `checks/run_checks.sh` reproduces them.

* **Build.** `lake build` builds every module with no errors and no warnings. The one expected
  warning is the `sorry` in `Challenge.lean`.
* **Comparator.** `lake comparator` checks `Solution` against `Challenge`. The Lean kernel, nanoda
  and con-ron accept the solution ("Your solution is okay!"; con-ron accepted 22,508 declarations).
  The local run used `--inadvisably-no-sandbox`, because `bwrap` was not available.
  `scripts/verify-comparator.sh` runs the sandboxed check, as Palomar does.
* **Axioms.** `CheckAxioms.lean` prints the axioms of 33 main results. They use only `propext`,
  `Classical.choice` and `Quot.sound`.
* **Sanity checks.** `SanityChecks.lean` prints the elaborated statements and checks examples:
  * tree paths, and small admissible and non-admissible sets;
  * values of the tent map, the parent map of `childOf`, and the scale recursion;
  * `φ_P(o_P) = p_P`, and that `X` is nondegenerate;
  * that `K` is indecomposable;
  * that the Vietoris topology on `NonemptyCompacts` is the Hausdorff-metric topology.
* **Kernel replay.** `leanchecker` replays every module through the kernel.
* **Independent checker.** `lean4export` exports `RegSub.theoremA_l2` and
  `RegSub.theoremA_unconditional` with all their dependencies (23,933 declarations, including the
  Mathlib ones). The independent type checker `nanoda` checks the export: no errors, and only the
  three standard axioms.

## Building

The project uses Lean `v4.35.0` (`lean-toolchain`) and Mathlib at commit
`6015dbbfc399f4548bafd46f9560ff61595fd328`, pinned in `lakefile.toml` and `lake-manifest.json`.
Every file uses the Lean module system.

```
lake exe cache get
lake build
lake env lean CheckAxioms.lean
lake env lean SanityChecks.lean
./scripts/verify-comparator.sh   # needs bubblewrap
./checks/run_checks.sh           # leanchecker and nanoda as well
```

## Licence

The Lean code and the files in this project are licensed under the Apache License 2.0
(`LICENSE`). The paper itself is distributed separately under CC BY 4.0 (see the `main` branch and
Zenodo).
