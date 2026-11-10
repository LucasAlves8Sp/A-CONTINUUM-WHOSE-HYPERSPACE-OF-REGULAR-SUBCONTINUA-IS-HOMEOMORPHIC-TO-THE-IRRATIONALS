module

public import RegSub.AlexandrovUrysohn
public import Mathlib.Topology.Instances.Irrational

@[expose] public section

/-!
# The Baire space is homeomorphic to the irrationals

Fact 2.5(c) of the paper. We deduce it from the Alexandrov–Urysohn theorem: the space of
irrational numbers is a nonempty zero-dimensional Polish space in which every compact set has
empty interior.
-/

open Set Filter Topology TopologicalSpace Metric

namespace RegSub

/-- The irrational numbers as a subspace of `ℝ`. -/
abbrev Irr : Type := {x : ℝ // Irrational x}

instance : PolishSpace Irr := isGδ_polishSpace IsGδ.setOfPred_irrational

instance : Nonempty Irr := ⟨⟨√2, irrational_sqrt_two⟩⟩

/-- Rational intervals form a clopen basis of the irrationals. -/
theorem irr_basis :
    IsTopologicalBasis {s : Set Irr | ∃ a b : ℚ, s = {x : Irr | (a : ℝ) < x ∧ (x : ℝ) < b}} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨a, b, rfl⟩
    exact isOpen_Ioo.preimage continuous_subtype_val
  · intro x U hxU hU
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hxU
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show (x : ℝ) - ε < x by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show (x : ℝ) < x + ε by linarith)
    refine ⟨_, ⟨a, b, rfl⟩, ⟨ha2, hb1⟩, fun y hy => hball ?_⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    obtain ⟨hy1, hy2⟩ := hy
    constructor <;> linarith

theorem irr_isClopen (a b : ℚ) : IsClopen {x : Irr | (a : ℝ) < x ∧ (x : ℝ) < b} := by
  refine ⟨?_, isOpen_Ioo.preimage continuous_subtype_val⟩
  have : {x : Irr | (a : ℝ) < x ∧ (x : ℝ) < b} = (↑) ⁻¹' Icc (a : ℝ) b := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.le, h2.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨lt_of_le_of_ne h1 fun h => x.2.ne_rat a h.symm,
        lt_of_le_of_ne h2 fun h => x.2.ne_rat b h⟩
  rw [this]
  exact isClosed_Icc.preimage continuous_subtype_val

instance : ZeroDimensionalSpace Irr :=
  ZeroDimensionalSpace.of_isTopologicalBasis (by rintro _ ⟨a, b, rfl⟩; exact irr_isClopen a b)
    irr_basis

/-- Every compact set of irrationals has empty interior. -/
theorem irr_compact_interior (K : Set Irr) (hK : IsCompact K) : interior K = ∅ := by
  by_contra hne
  obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨_, ⟨a, b, rfl⟩, hya, hsub⟩ :=
    irr_basis.exists_subset_of_mem_open hy isOpen_interior
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (hya.1.trans hya.2)
  -- the rational `q` lies in the closure of the compact set `K ⊆ ℝ`
  have hKc : IsClosed (((↑) : Irr → ℝ) '' K) := (hK.image continuous_subtype_val).isClosed
  have hq : (q : ℝ) ∈ ((↑) : Irr → ℝ) '' K := by
    refine hKc.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨r, hr, hr1, hr2⟩ := exists_irrational_btwn
      (show max (a : ℝ) ((q : ℝ) - ε) < min (b : ℝ) ((q : ℝ) + ε) by
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨hq1.trans hq2, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
    refine ⟨r, ⟨⟨r, hr⟩, interior_subset (hsub ⟨(le_max_left _ _).trans_lt hr1,
      hr2.trans_le (min_le_left _ _)⟩), rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [hr2.trans_le (min_le_right (b : ℝ) ((q : ℝ) + ε))]
    · linarith [(le_max_right (a : ℝ) ((q : ℝ) - ε)).trans_lt hr1]
  obtain ⟨z, -, hz⟩ := hq
  exact z.2 ⟨q, hz.symm⟩

/-- **Fact 2.5(c).** The Baire space is homeomorphic to the irrationals. -/
theorem baire_homeomorph_irr : Nonempty ((ℕ → ℕ) ≃ₜ Irr) :=
  alexandrovUrysohn Irr irr_compact_interior

end RegSub
