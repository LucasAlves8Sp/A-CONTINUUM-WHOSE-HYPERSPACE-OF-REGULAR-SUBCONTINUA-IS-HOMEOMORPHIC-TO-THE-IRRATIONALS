# RegSub — Lean 4 formalization of the combinatorial core of Theorem A

Lean 4 / Mathlib formalization accompanying the paper
*A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals*
(supplementary material).

## What is proved

Everything below is proved in Lean with no `sorry` and no added axioms. `#print axioms` reports only
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Lean declaration | File | Paper |
| --- | --- | --- |
| `Piece`, `IsDesc`, `OnPath`, `PathConvex` | `RegSub/Tree.lean` | §3.2: the index tree, `M ⪯ P`, tree paths, convexity |
| `pathConvex_iff_parentClosed` | `RegSub/Tree.lean` | parent-closure form of convexity, used in all later proofs |
| `Admissible` | `RegSub/CodeSpace.lean` | conditions (a)–(c) of Theorem 4.6 |
| `Admissible.addTail`, `Admissible.not_admissible_union_spine` | `RegSub/CodeSpace.lean` | Proposition 5.4, Case 1 (admissibility of the modified codes; non-admissible limit) |
| `Admissible.cutHead`, `not_admissible_cutAll` | `RegSub/CodeSpace.lean` | Proposition 5.4, Case 2 |
| `codeSet`, `codeSet_nonempty` | `RegSub/Topology.lean` | the code space 𝔇 ⊆ 2^𝒫 is nonempty |
| `isGδ_codeSet` | `RegSub/Topology.lean` | Proposition 5.3: 𝔇 is G_δ in the Cantor cube |
| `instZeroDimensionalSpaceCodeSet` | `RegSub/Topology.lean` | 𝔇 is zero-dimensional |
| `instPolishSpaceCube` | `RegSub/Topology.lean` | the Cantor cube 2^𝒫 is Polish |
| `isGδ_polishSpace`, `gδPolishStatement` | `RegSub/GdeltaPolish.lean`, `RegSub/TheoremA.lean` | a G_δ subset of a Polish space is Polish (Kechris, Theorem 3.11, one direction); hence 𝔇 is Polish |
| `exists_escape`, `isCompact_interior_eq_empty` | `RegSub/Topology.lean` | Proposition 5.4 in code form: every compact subset of 𝔇 has empty interior |
| `codeSet_homeomorph_baire` | `RegSub/TheoremA.lean` | 𝔇 ≅ ℕ^ℕ, given Assumption 1 |
| `theoremA` | `RegSub/TheoremA.lean` | Theorem A, given Assumptions 1–2 |

Condition (c) is formalized as follows. For a family `N : ℕ → Set ℕ` of infinite sets, each
included spine must have, for every `j`, infinitely many included children with index in `N j`.
In the paper `N j = {k | a_k ∈ V_j}` for a countable base `(V_j)` of the template continuum `K`
(up to the shift of indices described under *Translation notes*).
Because `K` has no isolated points and the `a_k` are distinct, this condition is equivalent to the
density of the attaching points. The code-space results hold for every family of infinite sets
`N j`.

## What is assumed

Two results are not available in Mathlib. They are stated as propositions in
`RegSub/TheoremA.lean` and enter `theoremA` as explicit hypotheses rather than as `axiom`
declarations. A misstated hypothesis therefore cannot make the rest of the development
inconsistent.

1. `AlexandrovUrysohnStatement` — a nonempty zero-dimensional Polish space in which every compact
   set has empty interior is homeomorphic to `ℕ → ℕ` (Kechris, *Classical Descriptive Set
   Theory*, Theorem 7.7).
2. `GeometricIdentification` — there is a continuum `X` and a family `N` of infinite sets such
   that the hyperspace of regular subcontinua of `X` (with the Hausdorff metric) is homeomorphic
   to `codeSet N`. This is the geometric part of the paper (Sections 3–4 and Proposition 5.2). It
   relies on the Knaster bucket-handle continuum, composants and the realization in `ℓ²`, none of
   which are in Mathlib.

An earlier version also assumed that G_δ subsets of Polish spaces are Polish. This is now proved
in `RegSub/GdeltaPolish.lean`: writing `s = ⋂ n, U n` with each `U n` open, the diagonal map
`s → ∀ n, U n` is a closed embedding into a countable product of Polish spaces.

The final identification `ℕ^ℕ ≅ ℝ \ ℚ` (continued fractions) is classical and not formalized, so
`theoremA` concludes `𝒟(X) ≃ₜ (ℕ → ℕ)`.

## Translation notes

These points were checked when comparing the Lean statements with the paper.

* **Indexing.** The paper uses `ℕ = {1, 2, …}`; Lean's `ℕ` starts at `0`. The index tree is the
  same up to the relabelling `k ↦ k + 1` of every index, which preserves the parent map. With this
  relabelling, `N j = {k | a_{k+1} ∈ V_j}`.
* **Lists.** `block β` stores the sequence `β` with the most recent pair first, so the child
  `B_{β⌢(m,k)}` of `S_{β,m}` is `block ((m, k) :: β)` (`child β m k`).
* **Tree paths.** `OnPath P R Q` says that `Q` is an ancestor of `P` or of `R` (possibly equal) and
  that `P` and `R` do not both lie below a single child of `Q`. In a rooted tree this holds exactly
  when `Q` lies on the path from `P` up to their lowest common ancestor and down to `R`, i.e.
  `Q ∈ [P, R]`. `PathConvex` is therefore condition (b) of Theorem 4.6.
* **Condition (c).** Density of the attaching points is encoded through the index sets `N j`;
  see above. The equivalence uses that `K` has no isolated points and that the `a_k` are distinct.
* **Case 2 of Proposition 5.4.** `cutHead` deletes the subtrees below all children `j < k`, the
  paper only below the selected ones; for the convex sets to which it is applied the results agree
  (see the docstring of `cutHead`).
* **Topology of the hyperspace.** Mathlib gives `NonemptyCompacts X` the Vietoris topology, and its
  metric is the Hausdorff distance. `SanityChecks.lean` confirms by `rfl` that the Vietoris topology
  is definitionally the topology of the Hausdorff metric, so `regularSubcontinua X` carries the
  topology of the paper.
* **Zero-dimensional.** Mathlib's `ZeroDimensionalSpace` means that the clopen sets form a basis,
  as in Kechris. `AlexandrovUrysohnStatement` is Kechris, Theorem 7.7, with nonemptiness stated
  separately.
* **Conclusion.** `theoremA` concludes `𝒟(X) ≃ₜ (ℕ → ℕ)`; the further step `ℕ^ℕ ≅ ℝ \ ℚ` is not
  formalized (see above).

## Independent checks

* `SanityChecks.lean` prints the elaborated statements and checks small examples: the path
  between two sibling blocks passes through their parent spine and not through the root; a single
  block is admissible; a block with a childless spine is not; the empty set is not admissible.
* The modules were replayed through the kernel with `leanchecker` (exit code 0).
* The main theorems and all their dependencies were exported with `lean4export` and checked by the
  external type checker `nanoda` (16997 declarations, no errors, only `propext`,
  `Classical.choice` and `Quot.sound` as axioms).

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
'RegSub.pathConvex_iff_parentClosed' depends on axioms: [propext, Quot.sound]
'RegSub.codeSet_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isGδ_codeSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.instZeroDimensionalSpaceCodeSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isCompact_interior_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.isGδ_polishSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.codeSet_homeomorph_baire' depends on axioms: [propext, Classical.choice, Quot.sound]
'RegSub.theoremA' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The development was checked with Lean 4.35.0 against a local build of Mathlib at the commit above;
`lake build` succeeds. It prints style warnings suggesting the `module` keyword, which do not affect
the results.
