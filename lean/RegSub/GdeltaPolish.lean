import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.Basic

/-!
# `G_δ` subsets of Polish spaces are Polish

This is one direction of Kechris, *Classical Descriptive Set Theory*, Theorem 3.11. Mathlib
already knows that open and closed subsets of Polish spaces are Polish and that countable products
of Polish spaces are Polish. Writing `s = ⋂ n, U n` with each `U n` open, the map
`x ↦ (x, x, x, …)` is a closed embedding of `s` into the Polish space `∀ n, U n`, so `s` is Polish.
-/

open Set Topology

namespace RegSub

theorem isGδ_polishSpace {X : Type*} [TopologicalSpace X] [PolishSpace X] {s : Set X}
    (hs : IsGδ s) : PolishSpace s := by
  obtain ⟨U, hUo, rfl⟩ := isGδ_iff_eq_iInter_nat.1 hs
  have : ∀ n, PolishSpace (U n) := fun n => (hUo n).polishSpace
  -- the diagonal map into the product of the open sets
  let f : (⋂ n, U n : Set X) → ∀ n, U n := fun x n => ⟨x.1, mem_iInter.1 x.2 n⟩
  have hf : Continuous f :=
    continuous_pi fun n => (continuous_subtype_val).subtype_mk _
  have hg : Continuous fun y : (∀ n, U n) => ((y 0 : U 0) : X) :=
    continuous_subtype_val.comp (continuous_apply 0)
  have hind : IsInducing f := by
    refine IsInducing.of_comp hf hg ?_
    exact IsInducing.subtypeVal
  have hinj : Function.Injective f := by
    intro x y hxy
    have h0 : ((f x 0 : U 0) : X) = ((f y 0 : U 0) : X) := by rw [hxy]
    exact Subtype.ext h0
  have hrange : range f = ⋂ n, {y : ∀ n, U n | ((y n : U n) : X) = ((y 0 : U 0) : X)} := by
    ext y
    simp only [mem_range, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩ n
      rfl
    · intro hy
      refine ⟨⟨(y 0 : X), mem_iInter.2 fun n => ?_⟩, ?_⟩
      · rw [← hy n]
        exact (y n).2
      · funext n
        exact Subtype.ext (hy n).symm
  have hclosed : IsClosed (range f) := by
    rw [hrange]
    refine isClosed_iInter fun n => isClosed_eq ?_ hg
    exact continuous_subtype_val.comp (continuous_apply n)
  exact (IsClosedEmbedding.mk ⟨hind, hinj⟩ hclosed).polishSpace

end RegSub
