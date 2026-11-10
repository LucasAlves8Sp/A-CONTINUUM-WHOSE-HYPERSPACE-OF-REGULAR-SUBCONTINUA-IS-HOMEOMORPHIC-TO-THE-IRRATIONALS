# Review and verification

This file records the mathematical review of the paper and the checks run on the Lean formalization. The paper is version v15, in `paper/`. The Lean development is in `lean/`.

The logs of the checks are in [`lean/checks/`](lean/checks/), and [`lean/checks/run_checks.sh`](lean/checks/run_checks.sh) reproduces them.

## 1. Outcome

**The Lean development now proves Theorem A completely, including the known results it uses.** There is no `sorry`, no added axiom and no hypothesis. The only axioms are Lean's standard three: `propext`, `Classical.choice` and `Quot.sound`. The final theorem is:

```lean
theorem RegSub.theoremA_l2 :
    ∃ X : Set (lp (fun _ : ℕ => ℝ) 2), IsCompact X ∧ IsConnected X ∧ X.Nontrivial ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) ∧
      Nonempty (regularSubcontinua X ≃ₜ {x : ℝ // Irrational x})
```

In words: there is a nondegenerate continuum X in ℓ² whose hyperspace of regular subcontinua 𝒟(X) is homeomorphic to the Baire space ℕ^ℕ and to the irrationals.

* **Size.** About 4,600 lines in 17 files.
* **New since v14.** Twelve files are new: the Knaster continuum, composants, Alexandrov–Urysohn, the irrationals, ℓ², the construction, its geometry, interiors, the regular-subcontinuum description, Theorem 4.6, the identification, and the main theorem.
* **What changed in status.** The two former hypotheses are now theorems:
  * the Alexandrov–Urysohn theorem;
  * the geometric identification of 𝒟(X) with the code space.

  The step ℕ^ℕ ≅ 𝕀, which was not formalized before, is now proved too.

**The review found no mathematical error in the paper (v14).** Every proof was checked line by line, and the formalization independently confirms Sections 3–5. The review led to small changes, collected in **v15**:

* a shorter proof of Lemma 3.5(c);
* one added sentence closing a small gap in Section 6.1;
* a sentence in the introduction announcing the formalization;
* a rewritten Lean paragraph in the AI disclosure, plus a new round 5 in its list.

No statement, numbering or reference changed. The paper is still 18 pages.

## 2. What the formal statement means

The statement uses only Mathlib definitions plus one definition of the project:

```lean
def regularSubcontinua (X : Type) [MetricSpace X] : Set (NonemptyCompacts X) :=
  {A | IsConnected (A : Set X) ∧ closure (interior (A : Set X)) = A}
```

This is exactly 𝒟(X): nonempty compact connected subsets equal to the closure of their interior. Closure and interior are taken in X, because X is a subtype here.

* **Topology of the hyperspace.** Mathlib's `NonemptyCompacts X` carries the Vietoris topology. `SanityChecks.lean` proves by `rfl` that this is definitionally the topology of the Hausdorff metric, and that the distance is `hausdorffDist`. So `≃ₜ` is a homeomorphism for the Hausdorff metric, as in the paper.
* **The ambient spaces.** `lp (fun _ : ℕ => ℝ) 2` is ℓ², `{x : ℝ // Irrational x}` is 𝕀 with the subspace topology, and `ℕ → ℕ` carries the product topology.
* **Nondegeneracy.** `X.Nontrivial` (more than one point) was added to the final theorem. A continuum is usually required to be nondegenerate, although the conclusion already forces it.

**What one must trust:**

* the Lean kernel;
* Mathlib's definitions of the objects in the statement: `lp`, `NonemptyCompacts` and its topology, `closure`, `interior`, `IsConnected`, `IsCompact`, `Homeomorph`, `Irrational`;
* the two-line definition above.

Everything else is checked.

## 3. Coverage: paper → Lean

| Paper | Lean (file) |
|---|---|
| Template continuum K (§3.1) | `Knaster`, compact, connected, nondegenerate (`Knaster.lean`) |
| Fact 2.4(a) | `eq_univ_of_interior_nonempty` (`Knaster.lean`) |
| Fact 2.4(c), composants | `Joinable`, `eq_univ_of_not_joinable`, `isMeagre_joinable` (`Composant.lean`) |
| Fact 2.4(d) | `dense_compl_of_countable`, `dense_diff_countable`, `dense_diff_finite` |
| Fact 2.5(a) (direction used) | `isGδ_polishSpace` (`GdeltaPolish.lean`) |
| Fact 2.5(b), Alexandrov–Urysohn | `alexandrovUrysohn` (`AlexandrovUrysohn.lean`, Lusin scheme) |
| Fact 2.5(c), ℕ^ℕ ≅ 𝕀 | `baire_homeomorph_irr` (`Irrational.lean`) |
| Lemma 3.1 | `Template`, `exists_template`, `tmpl` (`Composant.lean`) |
| Tree, scales, attachments (§3.2) | `Piece`, `childOf`, `lam`, `tpt`, `opt` (`Tree.lean`, `Construction.lean`) |
| Realization in ℓ² (§3.3) | `J`, `C`, `ι` (`Hilbert.lean`), `pt`, `phi` (`Construction.lean`) |
| Lemma 3.2 | `C_phi_self`, `C_phi_of_not_isDesc`, `C_phi_of_isDesc_child` |
| Lemma 3.3(a)–(h) | `finite_lam_ge`, `Y_subset_closedBall`, `Y_eq`, `C_of_mem_Y_child`, `C_of_mem_Z`, `C_eq_zero_iff_of_mem_Y`, `disjoint_Y_child`, `Y_child_inter_piece`, `X_eq_Y_union_Z`, `Y_inter_Z`, `isCompact_X`, `isConnected_X` |
| Lemma 3.5(a),(c) | `piece_subset_closure_relInt_block`, `relInt_piece_disjoint`, `X_subset_closure_Ublk` |
| Lemma 4.2 | `X_eq_brY_union_brZ`, `brY_inter_brZ`, `not_joinable_brT` |
| Lemma 4.3 | `ret`, `mem_of_cut`, `piece_subset_of_crossing` |
| Lemma 4.4 | `piece_subset_of_relInt` |
| Lemma 4.5 | `eq_closure_blocks`, `blocksU_subset_closure_relInt` |
| Theorem 4.6 | `pcs_admissible` (necessity); `reg_Psi`, `pcs_Psi`, `Psi_pcs` (sufficiency, representation) |
| Encoding of condition (c) | `dense_iff_infinite` |
| Lemma 5.1 | `hausdorffDist_Psi_le` |
| Proposition 5.2 | `PhiHomeo : 𝒟(X) ≃ₜ 𝔇` |
| Proposition 5.3 | `isGδ_codeSet`, `instZeroDimensionalSpaceCodeSet`, `codeSet_nonempty` |
| Proposition 5.4 (code form) | `isCompact_interior_eq_empty` |
| Theorem A | `theoremA_l2`, `theoremA_unconditional`, `DX_homeomorph_baire` |

**Not formalized, because Theorem A does not need them:**

* Example 2.6;
* Lemma 3.5(b);
* the second sentence of Lemma 3.3(h), on branch limits;
* the geometric form of Proposition 5.4 (the non-regular limit A\*);
* Remarks 4.7 and 5.5–5.7;
* Section 6.

## 4. Differences between the Lean proof and the paper

These are differences of presentation. Each is stated in the v15 AI disclosure and in [`lean/README.md`](lean/README.md).

1. **Template model.** The template is the inverse limit of the tent map t ↦ min(2t, 2−2t), which is a standard model of the Knaster continuum, inside [0,1]^ℕ. The paper uses the planar bucket-handle picture. Only Fact 2.4(a) is used, and Lean proves it for this model. As a check, `SanityChecks.lean` derives from it that K is indecomposable.
2. **Coordinates in ℓ².** Each piece gets its own infinite block of coordinates instead of a 2-dimensional plane. The template is embedded by ι(z) = (2^{−(n+1)} z_n). The projection π_P becomes the restriction map `C P`.
   * Consequence: planarity of K is never used. With coordinate blocks, any nondegenerate indecomposable continuum works as the template.
3. **Root offset.** o_{B∅} = ρ instead of (0,0). As in the paper, Lemma 3.3(e) is used only for non-root pieces.
4. **Indexing.** Indices start at 0. After the shift, the scales are the paper's.
5. **Composants.** "Distinct composants" is formalized as "not in a common proper subcontinuum", which is the property the proofs use (Fact 2.4(c)). Lemma 3.1 is proved with the Baire category theorem (a composant is meagre) rather than from the existence of uncountably many dense composants.
6. **Condition (c).** It is encoded through a countable base: N_j = {k : a_k ∈ V_j}, and an included spine needs infinitely many included children with index in each N_j. `dense_iff_infinite` proves this equivalent to the paper's density condition.
7. **Proposition 5.4.** It is proved in the code space and transferred to 𝒟(X) through the homeomorphism Φ of Proposition 5.2. This is enough for Alexandrov–Urysohn, and it makes Lemma 3.5(b), Fact 2.2 and Fact 2.3(a) unnecessary for Theorem A.

## 5. Verification performed

The development was then ported to the Lean module system, the format the Palomar registry requires: each file starts with `module`, uses `public import`, and puts its contents in an `@[expose] public section`. The project also gained `Challenge.lean`, a Mathlib-only statement of Theorem A, and `Solution.lean`. All checks below were rerun on the ported code; the logs are in `lean/checks/`.

| Check | Result |
|---|---|
| Clean `lake build` against the pinned Mathlib (commit `6015dbb`), build directory deleted first | **Build completed successfully**; no errors. The only warning is the deliberate `sorry` in `Challenge.lean`. |
| `lake comparator`: `Solution` against `Challenge` | **"Your solution is okay!"** Accepted by the Lean kernel, nanoda and con-ron (con-ron accepted 22,508 declarations). |
| `CheckAxioms.lean`: 33 declarations, including Theorem A, Alexandrov–Urysohn, ℕ^ℕ ≅ 𝕀, Φ, Theorem 4.6, Lemma 5.1 and the Lemma 3.3 parts | all depend only on `propext`, `Classical.choice`, `Quot.sound`; `pathConvex_iff_parentClosed` uses only `propext`, `Quot.sound` |
| `SanityChecks.lean` | passes; no errors |
| `leanchecker` (kernel replay), run separately on each of the 17 modules | passes for all |
| `nanoda` (independent type checker, written in Rust), on `lean4export` output of `theoremA_l2`, `theoremA_unconditional` and all dependencies | **"Checked 23933 declarations with no errors"**; axioms: `propext`, `Quot.sound`, `Classical.choice` |
| Palomar's own source scan (module header, at most 10,000 lines per file) and metadata loader (`formalization.yaml`) | pass |
| Source scan for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` outside `Challenge.lean` | none |

The local `lake comparator` run used `--inadvisably-no-sandbox`, because `bwrap` was not available in the workspace. Palomar runs the sandboxed version.

**What `SanityChecks.lean` checks:**

* tent map values: T(1/4) = T(3/4) = 1/2 and T(1) = 0;
* 0 ∈ K, and indecomposability of K (`knaster_indecomposable`);
* the parent map of `childOf`, and the scale recursion λ(child n) = λ(P)/2^{n+2};
* φ_P(o_P) = p_P, and nondegeneracy of X;
* the earlier tree and code-space examples;
* the Vietoris/Hausdorff identity described in Section 2;
* the elaborated statements of `Reg`, `relInt`, `reg_iff`, `dense_iff_infinite`, and the main theorems.

**Two notes on the external checks:**

* **nanoda memory.** Exporting the whole environment of `RegSub.Main` (1.7 GB, most of it Mathlib tactic code) ran out of memory in nanoda on this 8 GB machine. Exporting Theorem A with its transitive dependencies (112 MB) is the standard way to run it, and it passed.
* **lean4lean.** The `lean4lean` binary on this machine was built for a different Lean version (incompatible `.olean` headers), so it was not used.

## 6. Mathematical review of the paper

I rechecked every argument of v14. The formalization independently confirms Lemma 3.1, Lemmas 3.2–3.3, Lemma 3.5(a),(c), Lemmas 4.2–4.5, Theorem 4.6, Lemma 5.1 and Propositions 5.2–5.4 (the last in code form).

**Verdict: the proof of Theorem A is correct.** No error was found.

### 6.1 Section-by-section

* **§2 Preliminaries.**
  * Lemma 2.1 and Fact 2.2: correct.
  * Fact 2.4(d): the argument is complete; a nonempty perfect compact metric space is uncountable.
  * Fact 2.5(e): correct. (x_n) ↦ (x_n/n) is a continuous injection of a compact space, hence an embedding.
  * Example 2.6:
    * Both continuity arguments are correct.
    * The orthogonality estimate is correct.
    * The classification A = A_Δ is correct.
    * The conclusion 𝒟(X) ≅ 2^ℕ ∖ {∅} is correct; this space is locally compact and uncountable, hence neither ℚ nor 𝕀.
* **§3 Construction.**
  * Lemma 3.1: correct.
  * Lemma 3.2: correct. For the root it reads π_root(x) = J(z), consistent with o = (0,0).
  * Lemma 3.3:
    * (b): the bound 4/3·λ_P follows because every child has at most a quarter of its parent's scale.
    * (c): the subsequence argument is complete.
    * (e)–(g) are correct, and so is the use of (e) for the non-root child in (f).
  * Lemma 3.5(a):
    * The finite set ℰ of large children is handled correctly.
    * The bound d(x, Y_c) > δ/2 is correct.
    * The parent side Z_B is handled correctly.
* **§4 Regular subcontinua.**
  * Lemma 4.2: (a)–(d) are correct; uniqueness in (d) holds because the closed one-point enlargements are pairwise disjoint.
  * Lemma 4.3:
    * r_M is a 1-Lipschitz retraction, including at the root, where p = 0 and o = (0,0).
    * (iii) and (iv) are correct.
  * Lemma 4.4 and Lemma 4.5: correct.
  * Theorem 4.6, necessity:
    * Convexity follows from Lemma 4.2(d) and 4.3(iv).
    * In the density argument the block lies below S because N(x,η) misses Z_S, and the child c is not in ℰ.
  * Theorem 4.6, sufficiency: the argument with two blocks below different children of S, in the "no unrecorded spine" step, is correct.
* **§5 Proof of Theorem A.**
  * Lemma 5.1: correct. The path [R,B] passes through M because R is not below M′.
  * Proposition 5.2: correct. Sequential openness of 𝒰_P suffices in the metric space 𝒟(X), and the spine case uses two distinct included children, which exist because a dense subset of a nondegenerate continuum is infinite.
  * Proposition 5.3: the three-part G_δ description is correct.
  * Proposition 5.4, Case 1:
    * F_k is convex.
    * The closure identity cl ⋃_{j≥k} B^{(j)} = S ∪ ⋃_{j≥k} B^{(j)} holds.
    * The intersection is A ∪ S.
    * A ∪ S is non-regular, by Fact 2.2 and Lemma 3.5(b).
  * Proposition 5.4, Case 2:
    * Deleting hanging subtrees preserves convexity.
    * The retained spines keep their selected children.
    * No block below S lies in A\*.
    * The final open-set argument is correct.
  * Remarks 5.5–5.7: correct as stated. Remark 5.6 is a sketch ("one checks"), which is appropriate for a remark.
* **§6 Rational case.**
  * §6.1: Ramírez's G_δ argument for [0,1]² is correct. One step was implicit: the ε-net unions of segments are connected. v15 adds the one-sentence justification.
  * Remark 6.1: correct.
  * §6.3: the classification of 𝒟(L) is correct:
    * the pasting for ρ_n;
    * the interval argument for Δ;
    * the clopen sets;
    * 𝒟(L) ≅ ω².
  * The closing example (p ∈ K₁) is correct.

### 6.2 Findings and suggestions

1. **Applied in v15. Simpler proof of Lemma 3.5(c).**
   * The old proof needed branch limits from Lemma 3.3(h).
   * The new proof notes that every piece lies in cl_X U, by (a) and the argument of (b), and that X is the closure of the union of the pieces.
   * The second sentence of Lemma 3.3(h) is then no longer used by Theorem A. It is still true and descriptive, so it was kept.
2. **Applied in v15. One sentence in §6.1** saying why the finite unions of segments are connected.
3. **Noted in the disclosure. Proposition 5.4 can be proved entirely in the code space.**
   * Once Φ is a homeomorphism, it suffices that every compact subset of 𝔇 has empty interior.
   * The code modifications F_k of Cases 1–2 converge in 2^𝒫 to a code violating (c). This is the version formalized.
   * The paper's geometric version is stronger: it exhibits the non-regular limit continuum A\*. It is worth keeping.
4. **Optional. Planarity is not needed.** With the infinite coordinate blocks used in Lean, any nondegenerate indecomposable continuum can be the template. The sentence "Any nondegenerate indecomposable plane continuum would suffice" could be strengthened accordingly. I left the main text unchanged and recorded this in the disclosure.
5. **Optional. Lemma 3.1 via Baire.** A composant of an indecomposable metric continuum is a countable union of nowhere dense closed sets, so the Baire category theorem gives the template points directly. The paper's argument, from uncountably many dense composants, is equally correct.

## 7. Changes from v14 to v15

* **Introduction, end of §1.1:** one sentence saying that the proof, including the classical results, is formalized in Lean 4 with Mathlib, with a pointer to the end of the paper.
* **Lemma 3.5(c):** shorter proof (finding 1).
* **§6.1:** one sentence on connectedness of the ε-net unions (finding 2).
* **AI disclosure:**
  * New round (5): the request for the complete formalization and the review, and what the review changed.
  * The Lean paragraph rewritten: complete formalization, the coverage list, the differences from the text, and the leanchecker and nanoda checks.
* **Unchanged:** the title page (no date; email lucasderiva8x@gmail.com), the statements, the numbering and the bibliography.
