# A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23528477.svg)](https://doi.org/10.5281/zenodo.23528477)
[![Hexagon](https://img.shields.io/badge/hexagon-2610.00570-4b5563.svg)](https://hexagonmath.org/pdf/2610.00570v1)
[![Lean 4](https://img.shields.io/badge/Lean_4-fully_formalized-2f6f4f.svg)](lean/)
[![Palomar](https://img.shields.io/badge/Palomar-PALOMAR--2026--11--10--000005-1f4e79.svg)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-10-000005&version=1)

**Lucas Alves de Almeida** (independent researcher)

**Main result.** There is a continuum $X\subseteq\ell^2$ whose hyperspace $\mathcal D(X)$ of regular subcontinua is homeomorphic to the Baire space $\mathbb N^{\mathbb N}$, and hence to the irrationals. This answers the irrational case of a question of Camargo, Ordoñez and Ramírez (Appl. Gen. Topol. 25 (2024), Question 3.26). The proof is **completely formalized in Lean 4 with Mathlib**, including the classical results it uses. The formalization is registered in the [Palomar registry](https://palomar-registry.org/) of Lean-verified mathematics as [PALOMAR-2026-11-10-000005](https://palomar-registry.org/entry?id=PALOMAR-2026-11-10-000005&version=1).

| | |
| --- | --- |
| Paper (PDF) | [`paper/regular-subcontinua-irrationals.pdf`](paper/regular-subcontinua-irrationals.pdf) |
| Zenodo (all versions) | [doi:10.5281/zenodo.23528477](https://doi.org/10.5281/zenodo.23528477) |
| Hexagon preprint | [hexagon:2610.00570v1](https://hexagonmath.org/pdf/2610.00570v1) |
| Lean formalization | [`lean/`](lean/), with the main theorem `RegSub.theoremA_l2` |
| Review and verification | [`REVIEW_AND_VERIFICATION.md`](REVIEW_AND_VERIFICATION.md) |
| Palomar registry | [PALOMAR-2026-11-10-000005 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-10-000005&version=1), registered 10 November 2026 from commit [`1261e4b`](https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS/tree/1261e4bc3eefa83f95df9db1346949845930bf6d) of the branch [`palomar`](https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS/tree/palomar) |

## Abstract

For a metric continuum $X$, let $\mathcal D(X)$ be the hyperspace of subcontinua of $X$ equal to the closure of their interior, with the Hausdorff metric. Camargo, Ordoñez and Ramírez asked whether $\mathcal D(X)$ can be homeomorphic to the rationals or to the irrationals. We answer the latter question affirmatively. We construct a continuum $X\subseteq\ell^2$ as the closure of a countable tree of scaled copies of an indecomposable plane continuum. Two types of piece alternate: blocks with dense interior, and spines with empty interior carrying densely attached blocks. We characterize all regular subcontinua by nonempty convex sets of pieces satisfying a density condition, and prove that this coding is a homeomorphism onto a $G_\delta$ subset of a Cantor cube. We then show that no point of $\mathcal D(X)$ has a compact neighborhood. The Alexandrov–Urysohn characterization yields $\mathcal D(X)\cong\mathbb N^{\mathbb N}$, and hence $\mathcal D(X)$ is homeomorphic to the irrationals. We also explain why this construction does not extend to the rational case, which remains open.

## Contents

| Path | Description |
| --- | --- |
| [`paper/regular-subcontinua-irrationals.pdf`](paper/regular-subcontinua-irrationals.pdf) | The paper (PDF, version v15) |
| [`paper/regular-subcontinua-irrationals.tex`](paper/regular-subcontinua-irrationals.tex) | LaTeX source of the paper (single file, `amsart`, figures in TikZ) |
| [`lean/`](lean/) | Complete Lean 4 / Mathlib formalization of Theorem A; see [`lean/README.md`](lean/README.md) |
| [`lean/checks/`](lean/checks/) | Logs of the build, comparator, axiom, kernel-replay and external type-checker runs, and a script that reproduces them |
| [`REVIEW_AND_VERIFICATION.md`](REVIEW_AND_VERIFICATION.md) | Mathematical review of the paper; coverage of the paper by the Lean code; the checks performed |
| [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md) | The AI disclosure, as it appears in the paper |
| [`prompt/first-prompt.md`](prompt/first-prompt.md) | The full first prompt given to Claude to start the work, unedited |
| [`LICENSE.md`](LICENSE.md) | CC BY 4.0 for the paper and texts; Apache-2.0 for the Lean code |

## The Lean formalization

The folder [`lean/`](lean/) contains a Lean 4 / Mathlib development that formalizes the **complete proof of Theorem A**, including the classical results it uses. It uses Lean 4.35.0 and Mathlib commit `6015dbb`, has about 4,700 lines in 17 files, and uses the Lean module system throughout. There is no `sorry`, no added axiom and no hypothesis. `#print axioms` reports only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. The final theorem (`RegSub/Main.lean`) is

```lean
theorem RegSub.theoremA_l2 :
    ∃ X : Set (lp (fun _ : ℕ => ℝ) 2), IsCompact X ∧ IsConnected X ∧ X.Nontrivial ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) ∧
      Nonempty (regularSubcontinua X ≃ₜ {x : ℝ // Irrational x})
```

Here `regularSubcontinua X` is the set of connected nonempty compact subsets `A` of `X` with `closure (interior A) = A`, with the Hausdorff-metric topology.

**What is formalized:**

- the template continuum (the inverse limit of the tent map, a model of the Knaster continuum), Fact 2.4(a),(d) for it, and Lemma 3.1 on points in distinct composants (via the Baire category theorem);
- the construction in $\ell^2$ and Lemmas 3.2, 3.3 and 3.5(a),(c);
- branches, retractions and crossing, atoms, and the block representation (Lemmas 4.2–4.5);
- Theorem 4.6, both directions;
- Lemma 5.1, Proposition 5.2 ($\mathcal D(X)\cong\mathfrak D$), Proposition 5.3, and Proposition 5.4 in code form;
- the Alexandrov–Urysohn theorem (Kechris, Theorem 7.7), proved with a Lusin scheme, and $\mathbb N^{\mathbb N}\cong\mathbb I$.

The formalization follows the paper. It differs only in presentation: the template model, coordinate blocks in $\ell^2$ instead of planes, the root offset, the indexing, and the encoding of condition (c). These differences are listed in the AI disclosure and in [`lean/README.md`](lean/README.md).

**Checks** (logs in [`lean/checks/`](lean/checks/)):

| Check | Result |
| --- | --- |
| clean `lake build` against the pinned Mathlib | no errors; the only warning is the deliberate `sorry` in `Challenge.lean` |
| `lake comparator`: `Solution` against `Challenge` | accepted by the Lean kernel, nanoda and con-ron |
| `CheckAxioms.lean` (33 results, including Theorem A) | only `propext`, `Classical.choice`, `Quot.sound` |
| `SanityChecks.lean` (the translation checked on examples) | passes |
| kernel replay with `leanchecker`, all 17 modules | passes |
| independent type checker `nanoda`, Theorem A and all dependencies | "Checked 23933 declarations with no errors" |

**Palomar.** The formalization is registered in the [Palomar registry](https://palomar-registry.org/) of Lean-verified mathematics as **[PALOMAR-2026-11-10-000005 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-10-000005&version=1)** (registered 10 November 2026). For the registration:

- Palomar ran `lake comparator` in its sandbox. It checked that `Solution.lean` proves the statement in `Challenge.lean`, which uses only Mathlib.
- Lean's kernel and the independent kernels nanoda and con-ron all accepted the exported proof.
- An automated review compared the formal statement with the informal claim and found no problems. This is an AI review, not human peer review.

Palomar keeps a preserved copy of the source. Its files here:

- `lean/Challenge.lean` states Theorem A using only Mathlib.
- `lean/Solution.lean` re-exports the proof.
- `lean/comparator.json` and `lean/formalization.yaml` hold the comparator configuration and the provenance metadata.

Palomar requires a single licence file at the repository root, so the registered snapshot is commit [`1261e4b`](https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS/tree/1261e4bc3eefa83f95df9db1346949845930bf6d) of the branch [`palomar`](https://github.com/LucasAlves8Sp/A-CONTINUUM-WHOSE-HYPERSPACE-OF-REGULAR-SUBCONTINUA-IS-HOMEOMORPHIC-TO-THE-IRRATIONALS/tree/palomar). It contains the same Lean project at its root, with an Apache-2.0 `LICENSE`.

## Building

**Paper.** Run `latexmk -pdf regular-subcontinua-irrationals.tex` (or `pdflatex` twice) in `paper/`.

**Lean.** In `lean/`, with Lean 4.35.0 and Mathlib at commit `6015dbbfc399f4548bafd46f9560ff61595fd328`:

```
lake update
lake exe cache get
lake build
lake env lean CheckAxioms.lean
lake env lean SanityChecks.lean
./scripts/verify-comparator.sh   # Challenge vs Solution; needs bubblewrap
./checks/run_checks.sh           # optional: leanchecker and nanoda as well
```

## How to cite

Lucas Alves de Almeida, *A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals*, preprint, Zenodo, 2026. [doi:10.5281/zenodo.23528477](https://doi.org/10.5281/zenodo.23528477). Also available as [hexagon:2610.00570](https://hexagonmath.org/pdf/2610.00570v1).

The Zenodo DOI above always resolves to the latest version.

To cite the registered Lean formalization: Lucas Alves de Almeida, *A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals*, Palomar, [PALOMAR-2026-11-10-000005 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-10-000005&version=1), 2026.

| Version | Content | DOI |
| --- | --- | --- |
| v1.0.1 | paper v14; Lean formalization of the combinatorial core | [10.5281/zenodo.23528478](https://doi.org/10.5281/zenodo.23528478) |
| (no tag) | paper (PDF only) | [10.5281/zenodo.23528598](https://doi.org/10.5281/zenodo.23528598) |
| v2.0.0 | paper v15 (PDF) and repository snapshot with the complete Lean formalization of Theorem A | [10.5281/zenodo.24095687](https://doi.org/10.5281/zenodo.24095687) |

```bibtex
@misc{AlvesdeAlmeida2026irrationals,
  author    = {Alves de Almeida, Lucas},
  title     = {A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint, hexagon:2610.00570},
  doi       = {10.5281/zenodo.23528477},
  url       = {https://doi.org/10.5281/zenodo.23528477}
}

@misc{palomar-2026-11-10-000005-v1,
  author       = {{Lucas Alves de Almeida}},
  title        = {{A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals}},
  year         = {2026},
  howpublished = {Palomar, PALOMAR-2026-11-10-000005 v1},
  url          = {https://palomar-registry.org/entry?id=PALOMAR-2026-11-10-000005&version=1}
}
```

## Status

No independent expert has yet verified the proofs. The Lean formalization checks the complete proof of Theorem A against the definitions stated above. It is registered in Palomar (PALOMAR-2026-11-10-000005), where the proof was mechanically verified and the statement passed an automated, non-human review. Problem Q, whether $\mathcal D(X)$ can be homeomorphic to the rationals, remains open.
