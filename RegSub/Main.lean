module

public import RegSub.Identification
public import RegSub.Irrational

@[expose] public section

/-!
# Theorem A, unconditionally

All ingredients are now proved:
* the Alexandrov–Urysohn theorem (`RegSub.AlexandrovUrysohn`);
* the geometric identification of `𝒟(X)` with the code space (`RegSub.Identification`,
  Theorem 4.6 and Proposition 5.2, with the Knaster continuum of `RegSub.Knaster`);
* the combinatorics of the code space (`RegSub.Topology`, Propositions 5.3 and 5.4);
* the Baire space is homeomorphic to the irrationals (`RegSub.Irrational`, Fact 2.5(c)).

**Theorem A.** There exists a continuum `X ⊆ ℓ²` such that `𝒟(X)` is homeomorphic to the Baire
space `ℕ^ℕ`, and hence to the irrationals.
-/

open Set Topology

noncomputable section

namespace RegSub

/-- The Alexandrov–Urysohn statement of `RegSub.TheoremA`, now proved. -/
theorem alexandrovUrysohnStatement : AlexandrovUrysohnStatement :=
  fun X _ _ _ _ hK => ⟨(alexandrovUrysohn X hK).some.symm⟩

/-- **Theorem A** (abstract form, as in `RegSub.TheoremA`), with no hypotheses. -/
theorem theoremA_unconditional :
    ∃ (X : Type) (_ : MetricSpace X), CompactSpace X ∧ ConnectedSpace X ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) :=
  theoremA alexandrovUrysohnStatement geometricIdentification

/-- `𝒟(X)` for the continuum `X` of the construction is homeomorphic to the Baire space. -/
theorem DX_homeomorph_baire : Nonempty (regularSubcontinua XS ≃ₜ (ℕ → ℕ)) := by
  obtain ⟨f⟩ := codeSet_homeomorph_baire alexandrovUrysohnStatement Nset_infinite
  exact ⟨PhiHomeo.trans f⟩

/-- The continuum `X` is nondegenerate: it contains the injective image of the Knaster
continuum, which has two distinct points. -/
theorem nontrivial_X : X.Nontrivial := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne KnasterSpace
  exact ⟨phi root a, piece_subset_X root ⟨a, rfl⟩, phi root b, piece_subset_X root ⟨b, rfl⟩,
    (phi_injective root).ne hab⟩

/-- **Theorem A.** There is a nondegenerate continuum `X ⊆ ℓ²` (here
`ℓ² = lp (fun _ : ℕ => ℝ) 2`) whose hyperspace of regular subcontinua `𝒟(X)` is homeomorphic to
the Baire space `ℕ → ℕ` and to the space of irrational numbers. -/
theorem theoremA_l2 :
    ∃ X : Set (lp (fun _ : ℕ => ℝ) 2), IsCompact X ∧ IsConnected X ∧ X.Nontrivial ∧
      Nonempty (regularSubcontinua X ≃ₜ (ℕ → ℕ)) ∧
      Nonempty (regularSubcontinua X ≃ₜ {x : ℝ // Irrational x}) := by
  obtain ⟨f⟩ := DX_homeomorph_baire
  obtain ⟨g⟩ := baire_homeomorph_irr
  exact ⟨X, isCompact_X, isConnected_X, nontrivial_X, ⟨f⟩, ⟨f.trans g⟩⟩

end RegSub

end
