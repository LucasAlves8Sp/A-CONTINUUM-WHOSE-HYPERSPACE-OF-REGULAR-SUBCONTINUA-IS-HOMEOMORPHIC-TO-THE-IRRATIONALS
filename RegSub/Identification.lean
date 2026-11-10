module

public import RegSub.Theorem46
public import RegSub.TheoremA

@[expose] public section

/-!
# Proposition 5.2: `𝒟(X)` is homeomorphic to the code space

We work with the continuum `X ⊆ ℓ²` as a metric space `XS = ↥X`, and with its hyperspace of
regular subcontinua `regularSubcontinua XS` (defined in `RegSub.TheoremA`: the connected nonempty
compact sets equal to the closure of their interior, with the Hausdorff metric).

* `reg_iff`: a nonempty compact `A ⊆ XS` is a regular subcontinuum iff its image in `ℓ²`
  satisfies `Reg`;
* `Phi`: `A ↦ 𝓕(A)` and `PsiD`: `F ↦ cl ⋃ {blocks of F}` are mutually inverse
  (Theorem 4.6);
* `Phi` is continuous because `{A | P ⊆ A}` is clopen (Proposition 5.2);
* `PsiD` is continuous by Lemma 5.1.
-/

open Set Filter Topology Function Metric TopologicalSpace

noncomputable section

namespace RegSub

open Piece

/-- The continuum `X` as a metric space. -/
abbrev XS : Type := ↥X

instance : CompactSpace XS := isCompact_iff_compactSpace.1 isCompact_X

instance : ConnectedSpace XS := isConnected_iff_connectedSpace.1 isConnected_X

/-- The image in `ℓ²` of a subset of `X`. -/
def toL2 (A : Set XS) : Set L2 := (↑) '' A

theorem toL2_subset_X (A : Set XS) : toL2 A ⊆ X := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem toL2_injective : Injective toL2 := Subtype.val_injective.image_injective

theorem isClosedEmbedding_val : IsClosedEmbedding ((↑) : XS → L2) :=
  isClosed_X.isClosedEmbedding_subtypeVal

theorem toL2_closure (A : Set XS) : toL2 (closure A) = closure (toL2 A) :=
  (isClosedEmbedding_val.closure_image_eq A).symm

theorem toL2_interior (A : Set XS) : toL2 (interior A) = relInt (toL2 A) := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx')
    refine ⟨⟨x', interior_subset hx', rfl⟩, ε, hε, fun y hy hyx => ⟨⟨y, hy⟩, hball ?_, rfl⟩⟩
    rw [mem_ball, Subtype.dist_eq]
    exact hyx
  · rintro ⟨⟨x', hx'A, rfl⟩, ε, hε, hball⟩
    refine ⟨x', mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨ε, hε, fun y hy => ?_⟩), rfl⟩
    rw [mem_ball, Subtype.dist_eq] at hy
    obtain ⟨y', hy'A, hyy'⟩ := hball y y.2 hy
    rw [← Subtype.ext hyy']
    exact hy'A

theorem reg_iff (A : NonemptyCompacts XS) :
    A ∈ regularSubcontinua XS ↔ Reg (toL2 (A : Set XS)) := by
  have hcl : IsClosed (toL2 (A : Set XS)) := (A.isCompact.image continuous_subtype_val).isClosed
  constructor
  · rintro ⟨hconn, hreg⟩
    refine ⟨toL2_subset_X _, A.isCompact.image continuous_subtype_val,
      (hconn.image _ continuous_subtype_val.continuousOn).isPreconnected,
      A.nonempty.image _, ?_⟩
    conv_lhs => rw [← hreg]
    rw [toL2_closure, toL2_interior]
  · rintro ⟨-, -, hpre, hne, hreg⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := hne
      exact ⟨⟨x, hx⟩, Topology.IsInducing.subtypeVal.isPreconnected_image.1 hpre⟩
    · apply toL2_injective
      rw [toL2_closure, toL2_interior]
      exact Subset.antisymm (closure_minimal (relInt_subset _) hcl) hreg

/-- The regular subcontinua as a subtype. -/
abbrev DX : Type := ↥(regularSubcontinua XS)

theorem reg_of_DX (A : DX) : Reg (toL2 (A.1 : Set XS)) := (reg_iff A.1).1 A.2

theorem dist_DX (A B : DX) :
    dist A B = hausdorffDist (toL2 (A.1 : Set XS)) (toL2 (B.1 : Set XS)) := by
  rw [Subtype.dist_eq, TopologicalSpace.NonemptyCompacts.dist_eq, toL2, toL2,
    hausdorffDist_image isometry_subtype_coe]

theorem hausdorffEDist_ne_top_DX (A B : DX) :
    hausdorffEDist (toL2 (A.1 : Set XS)) (toL2 (B.1 : Set XS)) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded (A.1.nonempty.image _) (B.1.nonempty.image _)
    ((A.1.isCompact.image continuous_subtype_val).isBounded)
    ((B.1.isCompact.image continuous_subtype_val).isBounded)

/-! ### The map `Φ` -/

/-- `Φ(A) = 𝓕(A)`. -/
def Phi (A : DX) : codeSet Nset :=
  ⟨toCode (pcs (toL2 (A.1 : Set XS))), toCode_mem_codeSet.2 (pcs_admissible (reg_of_DX A))⟩

/-- The regular subcontinuum `Ψ F` as a point of `𝒟(X)`. -/
def PsiNC (F : codeSet Nset) : NonemptyCompacts XS where
  carrier := ((↑) : XS → L2) ⁻¹' Psi (ofCode F.1)
  isCompact' := isClosedEmbedding_val.isCompact_preimage (reg_Psi F.2).2.1
  nonempty' := by
    obtain ⟨x, hx⟩ := (reg_Psi F.2).2.2.2.1
    exact ⟨(⟨x, (reg_Psi F.2).1 hx⟩ : XS), hx⟩

theorem toL2_PsiNC (F : codeSet Nset) : toL2 ((PsiNC F : NonemptyCompacts XS) : Set XS) =
    Psi (ofCode F.1) := by
  show ((↑) : XS → L2) '' (((↑) : XS → L2) ⁻¹' Psi (ofCode F.1)) = _
  rw [image_preimage_eq_of_subset]
  rw [Subtype.range_coe]
  exact (reg_Psi F.2).1

def PsiD (F : codeSet Nset) : DX :=
  ⟨PsiNC F, (reg_iff _).2 (by rw [toL2_PsiNC]; exact reg_Psi F.2)⟩

theorem PsiD_Phi (A : DX) : PsiD (Phi A) = A := by
  apply Subtype.ext
  apply NonemptyCompacts.ext
  apply toL2_injective
  rw [show ((PsiD (Phi A)).1 : Set XS) = (PsiNC (Phi A) : Set XS) from rfl, toL2_PsiNC]
  simp only [Phi, ofCode_toCode]
  exact Psi_pcs (reg_of_DX A)

theorem Phi_PsiD (F : codeSet Nset) : Phi (PsiD F) = F := by
  apply Subtype.ext
  funext P
  simp only [Phi]
  rw [show ((PsiD F).1 : Set XS) = (PsiNC F : Set XS) from rfl, toL2_PsiNC, pcs_Psi F.2]
  exact toCode_eq_of_iff Iff.rfl

/-! ### Continuity of `Φ` (Proposition 5.2) -/

theorem isOpen_block (β : List (ℕ × ℕ)) :
    IsOpen {A : DX | piece (block β) ⊆ toL2 (A.1 : Set XS)} := by
  rw [Metric.isOpen_iff]
  intro A hA
  obtain ⟨x, hx⟩ : (relInt (piece (block β))).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := piece_subset_closure_relInt_block β (pt_mem_piece (block β))
    rw [h, closure_empty] at this
    exact this
  obtain ⟨δ, hδ, hδball⟩ := relInt_open hx
  refine ⟨δ / 2, by positivity, fun A' hA' => ?_⟩
  rw [mem_ball, dist_DX] at hA'
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt (hA (relInt_subset _ hx))
    (by rw [hausdorffDist_comm]; exact hA') (hausdorffEDist_ne_top_DX A A')
  have hreg := reg_of_DX A'
  obtain ⟨y', hy', hyy'⟩ := Metric.mem_closure_iff.1 (hreg.2.2.2.2 hy) (δ / 2) (by positivity)
  have hy'X : y' ∈ X := hreg.1 (relInt_subset _ hy')
  have hy'B : y' ∈ relInt (piece (block β)) := hδball y' hy'X (by
    calc dist y' x ≤ dist y' y + dist y x := dist_triangle _ _ _
      _ < δ := by rw [dist_comm y' y, dist_comm y x]; linarith)
  exact piece_subset_of_relInt hreg.1 hreg.2.1 hreg.2.2.1 ⟨y', hy', relInt_subset _ hy'B⟩

theorem isOpen_piece_subset (P : Piece) : IsOpen {A : DX | piece P ⊆ toL2 (A.1 : Set XS)} := by
  cases P with
  | block β => exact isOpen_block β
  | spine β m =>
    rw [isOpen_iff_forall_mem_open]
    intro A hA
    have hadm := pcs_admissible (reg_of_DX A)
    obtain ⟨k₁, hk₁⟩ := (hadm.dense β m hA 0).nonempty
    obtain ⟨k₂, hk₂, hne⟩ := ((hadm.dense β m hA 0).sdiff (finite_singleton k₁)).nonempty
    rw [mem_singleton_iff] at hne
    refine ⟨{A' | piece (child β m k₁) ⊆ toL2 (A'.1 : Set XS)} ∩
      {A' | piece (child β m k₂) ⊆ toL2 (A'.1 : Set XS)}, ?_,
      (isOpen_block _).inter (isOpen_block _), hk₁.2, hk₂.2⟩
    rintro A' ⟨h₁, h₂⟩
    refine pcs_pathConvex (reg_of_DX A') (child β m k₁) (child β m k₂) (spine β m) h₁ h₂
      ⟨Or.inl (.of_parent (parent_child β m k₁)), ?_⟩
    rintro ⟨c, hc, h1, h2⟩
    obtain ⟨n, rfl⟩ := exists_childOf hc
    rw [child_eq_childOf] at h1 h2
    have e1 : k₁ = n := by
      have := h1.eq_of_depth_le (by rw [depth_childOf, depth_childOf])
      exact childOf_injective _ this
    have e2 : k₂ = n := by
      have := h2.eq_of_depth_le (by rw [depth_childOf, depth_childOf])
      exact childOf_injective _ this
    exact hne (e2.trans e1.symm)

theorem isClosed_piece_subset (P : Piece) :
    IsClosed {A : DX | piece P ⊆ toL2 (A.1 : Set XS)} := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro A hA
  simp only [mem_compl_iff, mem_ofPred_eq, not_subset] at hA
  obtain ⟨x, hxP, hxA⟩ := hA
  have hcl : IsClosed (toL2 (A.1 : Set XS)) := (reg_of_DX A).2.1.isClosed
  have hpos : 0 < infDist x (toL2 (A.1 : Set XS)) :=
    (hcl.notMem_iff_infDist_pos ((reg_of_DX A).2.2.2.1)).1 hxA
  refine ⟨_, hpos, fun A' hA' hsub => ?_⟩
  rw [mem_ball, dist_DX] at hA'
  have h1 := infDist_le_infDist_add_hausdorffDist (x := x) (hausdorffEDist_ne_top_DX A' A)
  rw [infDist_zero_of_mem (hsub hxP), zero_add] at h1
  linarith

theorem continuous_Phi : Continuous Phi := by
  apply Continuous.subtype_mk
  refine continuous_pi fun P => ?_
  rw [continuous_discrete_rng]
  intro b
  have hset : (fun A : DX => toCode (pcs (toL2 (A.1 : Set XS))) P) ⁻¹' {true} =
      {A : DX | piece P ⊆ toL2 (A.1 : Set XS)} := by
    ext A
    simp [pcs]
  cases b with
  | true => rw [hset]; exact isOpen_piece_subset P
  | false =>
    have : (fun A : DX => toCode (pcs (toL2 (A.1 : Set XS))) P) ⁻¹' {false} =
        ({A : DX | piece P ⊆ toL2 (A.1 : Set XS)})ᶜ := by
      ext A
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_ofPred_eq]
      rw [Bool.eq_false_iff, Ne, toCode_eq_true]
      rfl
    rw [this]
    exact (isClosed_piece_subset P).isOpen_compl

/-! ### Continuity of `Φ⁻¹` (Lemma 5.1) -/

theorem continuous_PsiD : Continuous PsiD := by
  rw [continuous_iff_continuousAt]
  intro F
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨β, hβ⟩ := F.2.hasBlock
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (lt_min (lam_pos (block β)) (by positivity : 0 < 3 / 4 * ε)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hN1 : (1 / 2 : ℝ) ^ N ≤ lam (block β) := (lt_of_lt_of_le hN (min_le_left _ _)).le
  have hN2 : 4 / 3 * (1 / 2 : ℝ) ^ N < ε := by
    have := lt_of_lt_of_le hN (min_le_right _ _)
    linarith
  set I := (finite_lam_ge N).toFinset
  have hopen : IsOpen {G : codeSet Nset | ∀ P ∈ I, G.1 P = F.1 P} := by
    have : {G : codeSet Nset | ∀ P ∈ I, G.1 P = F.1 P} =
        (↑) ⁻¹' ⋂ P ∈ I, {G : Piece → Bool | G P = F.1 P} := by
      ext G
      simp
    rw [this]
    exact (isOpen_biInter_finset fun P _ => isOpen_coord P _).preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds (fun P _ => rfl)] with G hG
  have hagree : ∀ P ∈ PN N, (P ∈ ofCode G.1 ↔ P ∈ ofCode F.1) := by
    intro P hP
    have hPI : P ∈ I := (finite_lam_ge N).mem_toFinset.2 hP
    simp only [mem_ofCode, hG P hPI]
  have hne : (ofCode G.1 ∩ PN N).Nonempty :=
    ⟨block β, (hagree _ hN1).2 hβ, hN1⟩
  rw [dist_DX, show ((PsiD G).1 : Set XS) = (PsiNC G : Set XS) from rfl,
    show ((PsiD F).1 : Set XS) = (PsiNC F : Set XS) from rfl, toL2_PsiNC, toL2_PsiNC]
  exact lt_of_le_of_lt (hausdorffDist_Psi_le G.2 F.2 hagree hne) hN2

/-- **Proposition 5.2.** `Φ : 𝒟(X) → 𝔇` is a homeomorphism. -/
def PhiHomeo : DX ≃ₜ codeSet Nset where
  toFun := Phi
  invFun := PsiD
  left_inv := PsiD_Phi
  right_inv := Phi_PsiD
  continuous_toFun := continuous_Phi
  continuous_invFun := continuous_PsiD

/-- The geometric identification, formerly an explicit hypothesis, is now proved. -/
theorem geometricIdentification : GeometricIdentification :=
  ⟨XS, inferInstance, inferInstance, inferInstance, Nset, Nset_infinite, ⟨PhiHomeo⟩⟩

end RegSub

end
