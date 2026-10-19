import RegSub.Topology
import RegSub.GdeltaPolish
import Mathlib.Topology.MetricSpace.Closeds

/-!
# Theorem A, conditional on two explicitly stated results

The combinatorial core of the proof of Theorem A is proved in `RegSub.Topology`: the code space
`codeSet N` is a nonempty, zero-dimensional `G_δ` subset of the Cantor cube in which every compact
set has empty interior. By `RegSub.isGδ_polishSpace` (file `RegSub.GdeltaPolish`), the code space
is therefore Polish. This file derives Theorem A from that core and two results that are not
available in Mathlib. They are stated below as propositions and enter the main theorem as
explicit hypotheses, so `#print axioms RegSub.theoremA` lists only Lean's standard axioms.

1. `AlexandrovUrysohnStatement` — the Alexandrov–Urysohn characterization of the Baire space
   (Kechris, *Classical Descriptive Set Theory*, Theorem 7.7).
2. `GeometricIdentification` — the geometric part of the paper: there is a continuum `X` whose
   hyperspace of regular subcontinua is homeomorphic to a code space `codeSet N` (Theorem 4.6 and
   Proposition 5.2, which rely on the Knaster bucket-handle continuum, composants and the
   realization in `ℓ²` of Section 3).

Earlier versions also assumed `GδPolishStatement` (Kechris, Theorem 3.11); it is now proved as
`gδPolishStatement`.
-/

open Set Topology

namespace RegSub

/-- Kechris, Theorem 3.11 (one direction): a `G_δ` subset of a Polish space is Polish. -/
def GδPolishStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] (s : Set X), IsGδ s → PolishSpace s

/-- The statement `GδPolishStatement` is proved, not assumed. -/
theorem gδPolishStatement : GδPolishStatement :=
  fun _ _ _ _ hs => isGδ_polishSpace hs

/-- **Assumption 1** (Alexandrov–Urysohn; Kechris, Theorem 7.7). A nonempty zero-dimensional
Polish space in which every compact subset has empty interior is homeomorphic to the Baire space
`ℕ → ℕ`. -/
def AlexandrovUrysohnStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] [ZeroDimensionalSpace X] [Nonempty X],
    (∀ K : Set X, IsCompact K → interior K = ∅) → Nonempty (X ≃ₜ (ℕ → ℕ))

/-- The hyperspace `𝒟(X)` of regular subcontinua of a metric space `X`: the connected nonempty
compact sets that equal the closure of their interior, with the Hausdorff metric topology
inherited from `NonemptyCompacts X`. -/
def regularSubcontinua (X : Type) [MetricSpace X] : Set (TopologicalSpace.NonemptyCompacts X) :=
  {A | IsConnected (A : Set X) ∧ closure (interior (A : Set X)) = (A : Set X)}

/-- **Assumption 2** (Theorem 4.6 and Proposition 5.2 of the paper). There is a continuum `X`
(a nonempty compact connected metric space) and a family `N` of infinite subsets of `ℕ` such that
the hyperspace of regular subcontinua of `X` is homeomorphic to the code space `codeSet N`.
In the paper, `X ⊆ ℓ²` is the null tree of Knaster continua of Section 3, the homeomorphism is
`A ↦ 𝓕(A)`, and `N j = {k | a_k ∈ V_j}` for a countable base `(V_j)` of the template (with the
indices shifted by one, since the paper's indices start at `1`). -/
def GeometricIdentification : Prop :=
  ∃ (X : Type) (_ : MetricSpace X), CompactSpace X ∧ ConnectedSpace X ∧
    ∃ N : ℕ → Set ℕ, (∀ j, (N j).Infinite) ∧ Nonempty (regularSubcontinua X ≃ₜ codeSet N)

/-- The code space is homeomorphic to the Baire space, given Assumption 1. -/
theorem codeSet_homeomorph_baire (hAU : AlexandrovUrysohnStatement)
    {N : ℕ → Set ℕ} (hN : ∀ j, (N j).Infinite) : Nonempty (codeSet N ≃ₜ (ℕ → ℕ)) := by
  have : PolishSpace (codeSet N) := isGδ_polishSpace (isGδ_codeSet N)
  have : Nonempty (codeSet N) := (codeSet_nonempty hN).to_subtype
  exact hAU (codeSet N) (isCompact_interior_eq_empty hN)

/-- **Theorem A** (conditional on Assumptions 1 and 2). There is a continuum `X` whose hyperspace
of regular subcontinua is homeomorphic to the Baire space `ℕ → ℕ`. -/
theorem theoremA (hAU : AlexandrovUrysohnStatement) (hGeo : GeometricIdentification) :
    ∃ (X : Type) (_ : MetricSpace X), CompactSpace X ∧ ConnectedSpace X ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) := by
  obtain ⟨X, _, hc, hconn, N, hN, ⟨e⟩⟩ := hGeo
  obtain ⟨f⟩ := codeSet_homeomorph_baire hAU hN
  exact ⟨X, inferInstance, hc, hconn, ⟨e.trans f⟩⟩

end RegSub
