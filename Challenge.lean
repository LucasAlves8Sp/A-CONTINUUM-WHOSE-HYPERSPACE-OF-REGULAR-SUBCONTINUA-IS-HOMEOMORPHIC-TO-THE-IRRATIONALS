module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals

This is the statement of Theorem A of the paper

> Lucas Alves de Almeida, *A continuum whose hyperspace of regular subcontinua is homeomorphic to
> the irrationals*, preprint, Zenodo, doi:10.5281/zenodo.23528477 (also hexagon:2610.00570).

A *continuum* is a nonempty compact connected metric space. A subcontinuum `A` of a continuum `X`
is *regular* if it equals the closure of its interior in `X`. The hyperspace `𝒟(X)` of regular
subcontinua carries the Hausdorff metric. Camargo, Ordoñez and Ramírez asked whether `𝒟(X)` can
be homeomorphic to the rationals or to the irrationals (Appl. Gen. Topol. 25 (2024), Question
3.26; earlier in Ramírez's thesis, Pregunta 3.2.14). Theorem A answers the irrational case: there
is a nondegenerate continuum `X` in the Hilbert space `ℓ²` such that `𝒟(X)` is homeomorphic to the
Baire space `ℕ^ℕ`, and hence to the space of irrational numbers.

In Lean:

* `lp (fun _ : ℕ => ℝ) 2` is the Hilbert space `ℓ²` of square-summable real sequences;
* a set `X` of it is a continuum when `IsCompact X ∧ IsConnected X`, and `X.Nontrivial` says that
  it has more than one point;
* `TopologicalSpace.NonemptyCompacts X` is the space of nonempty compact subsets of `X`. Its
  topology is the Vietoris topology, which coincides with the topology of the Hausdorff metric;
  its distance is `Metric.hausdorffDist`;
* `RegSub.regularSubcontinua X` below is `𝒟(X)`: the nonempty compact subsets that are connected
  and equal to the closure of their interior. Closure and interior are taken in `X`, because `X`
  enters as a subtype;
* `≃ₜ` is a homeomorphism, `ℕ → ℕ` carries the product topology (the Baire space), and
  `{x : ℝ // Irrational x}` carries the subspace topology of `ℝ`.
-/

namespace RegSub

/-- The hyperspace `𝒟(X)` of regular subcontinua of a metric space `X`: the connected nonempty
compact sets that equal the closure of their interior, with the Hausdorff metric topology
inherited from `NonemptyCompacts X`. -/
def regularSubcontinua (X : Type) [MetricSpace X] : Set (TopologicalSpace.NonemptyCompacts X) :=
  {A | IsConnected (A : Set X) ∧ closure (interior (A : Set X)) = (A : Set X)}

/-- **Theorem A.** There is a nondegenerate continuum `X ⊆ ℓ²` whose hyperspace `𝒟(X)` of regular
subcontinua is homeomorphic to the Baire space `ℕ → ℕ` and to the space of irrational numbers. -/
theorem theoremA_l2 :
    ∃ X : Set (lp (fun _ : ℕ => ℝ) 2), IsCompact X ∧ IsConnected X ∧ X.Nontrivial ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) ∧
      Nonempty (regularSubcontinua X ≃ₜ {x : ℝ // Irrational x}) := by
  sorry

end RegSub
