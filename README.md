# A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23528477.svg)](https://doi.org/10.5281/zenodo.23528477)

**Lucas Alves de Almeida** (independent researcher)

## Abstract

For a metric continuum $X$, let $\mathcal D(X)$ be the hyperspace of subcontinua of $X$ equal to the closure of their interior, with the Hausdorff metric. Camargo, Ordoñez and Ramírez asked whether $\mathcal D(X)$ can be homeomorphic to the rationals or to the irrationals. We answer the latter question affirmatively. We construct a continuum $X\subseteq\ell^2$ as the closure of a countable tree of scaled copies of an indecomposable plane continuum. Two types of piece alternate: blocks with dense interior, and spines with empty interior carrying densely attached blocks. We characterize all regular subcontinua by nonempty convex sets of pieces satisfying a density condition, and prove that this coding is a homeomorphism onto a $G_\delta$ subset of a Cantor cube. We then show that no point of $\mathcal D(X)$ has a compact neighborhood. The Alexandrov–Urysohn characterization yields $\mathcal D(X)\cong\mathbb N^{\mathbb N}$, and hence $\mathcal D(X)$ is homeomorphic to the irrationals. We also explain why this construction does not extend to the rational case, which remains open.

## Contents

| Path | Description |
| --- | --- |
| [`paper/regular-subcontinua-irrationals.pdf`](paper/regular-subcontinua-irrationals.pdf) | The paper (PDF) |
| [`paper/regular-subcontinua-irrationals.tex`](paper/regular-subcontinua-irrationals.tex) | LaTeX source of the paper (single file, `amsart`, figures in TikZ) |
| [`lean/`](lean/) | Lean 4 / Mathlib formalization of the combinatorial core of the proof; see [`lean/README.md`](lean/README.md) |
| [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md) | The AI disclosure, as it appears in the paper |
| [`prompt/first-prompt.md`](prompt/first-prompt.md) | The full first prompt given to Claude to start the work, unedited |
| [`LICENSE.md`](LICENSE.md) | CC BY 4.0 for the paper and texts; Apache-2.0 for the Lean code |

## The Lean formalization

The folder [`lean/`](lean/) contains a Lean 4 / Mathlib development (Lean 4.35.0, Mathlib commit `6015dbb`, about 830 lines) that machine-checks the combinatorial and topological core of the proof.

**What Lean proves** (no `sorry`, only the standard axioms `propext`, `Classical.choice`, `Quot.sound`):

- the index tree of the construction, tree paths and convexity (`RegSub/Tree.lean`);
- the admissible sets of pieces, conditions (a)–(c) of Theorem 4.6, and the code modifications used in both cases of Proposition 5.4 (`RegSub/CodeSpace.lean`);
- the code space $\mathfrak D\subseteq 2^{\mathcal P}$ is nonempty, $G_\delta$ and zero-dimensional, and every compact subset of it has empty interior (`RegSub/Topology.lean`);
- a $G_\delta$ subset of a Polish space is Polish (`RegSub/GdeltaPolish.lean`), so $\mathfrak D$ is Polish.

**What enters as explicit hypotheses** (`RegSub/TheoremA.lean`):

- the Alexandrov–Urysohn characterization of the Baire space (Kechris, Theorem 7.7);
- the geometric identification of $\mathcal D(X)$ with the code space (Theorem 4.6 and Proposition 5.2), which relies on the Knaster continuum, composants and the construction in $\ell^2$, none of which are in Mathlib.

From these, `theoremA` concludes $\mathcal D(X)\cong\mathbb N^{\mathbb N}$; the classical step $\mathbb N^{\mathbb N}\cong\mathbb I$ is not formalized. `SanityChecks.lean` checks that the Lean definitions match the paper on small examples, and the development was also re-checked with `leanchecker` and the external type checker `nanoda`. See [`lean/README.md`](lean/README.md) for details.

## Building

**Paper.** Run `latexmk -pdf regular-subcontinua-irrationals.tex` (or `pdflatex` twice) in `paper/`.

**Lean.** In `lean/`, with Lean 4.35.0 and Mathlib at commit `6015dbbfc399f4548bafd46f9560ff61595fd328`:

```
lake update
lake exe cache get
lake build
lake env lean CheckAxioms.lean
lake env lean SanityChecks.lean
```

`CheckAxioms.lean` reports only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The Alexandrov–Urysohn theorem and the geometric identification of $\mathcal D(X)$ with the code space (Theorem 4.6 and Proposition 5.2) enter as explicit hypotheses; see [`lean/README.md`](lean/README.md) for what is proved and what is assumed.

## How to cite

Lucas Alves de Almeida, *A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals*, preprint, Zenodo, 2026. [doi:10.5281/zenodo.23528477](https://doi.org/10.5281/zenodo.23528477)

This DOI always resolves to the latest version; version v1.0.1 has DOI [10.5281/zenodo.23528478](https://doi.org/10.5281/zenodo.23528478).

```bibtex
@misc{AlvesdeAlmeida2026irrationals,
  author    = {Alves de Almeida, Lucas},
  title     = {A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.23528477},
  url       = {https://doi.org/10.5281/zenodo.23528477}
}
```

## Status

No independent expert has yet verified the proofs. Problem Q (whether $\mathcal D(X)$ can be homeomorphic to the rationals) remains open.
