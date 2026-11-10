module

public import RegSub.Description
public import RegSub.Topology

@[expose] public section

/-!
# Theorem 4.6 (description of `𝒟(X)`) and Lemma 5.1

The density condition (c) of Theorem 4.6 is encoded, as in `RegSub.CodeSpace`, through a fixed
sequence `Vb` of nonempty open sets of `K` that forms a basis: `Nset j = {k | a_k ∈ Vb j}`.
`dense_iff_infinite` shows that this encoding is equivalent to the density of the included
attaching points.

* `pcs_admissible`: necessity, `𝓕(A)` is admissible for every regular `A`;
* `reg_Psi`, `pcs_Psi`: sufficiency, for an admissible `F` the set
  `Ψ F = cl ⋃ {B ∈ F | B block}` is regular and `𝓕(Ψ F) = F`;
* `eq_closure_blocks` (Lemma 4.5): `A = Ψ (𝓕 A)`;
* `hausdorffDist_Psi_le`: Lemma 5.1.
-/

open Set Filter Topology Function Metric

noncomputable section

namespace RegSub

open Piece

/-! ### The encoding of the density condition -/

theorem exists_basisSeq : ∃ V : ℕ → Set KnasterSpace, (∀ j, IsOpen (V j)) ∧
    (∀ j, (V j).Nonempty) ∧ ∀ U, IsOpen U → U.Nonempty → ∃ j, V j ⊆ U := by
  obtain ⟨b, hbc, hb0, hb⟩ := TopologicalSpace.exists_countable_basis KnasterSpace
  have hbne : b.Nonempty := by
    obtain ⟨U, hUb, -, -⟩ := hb.exists_subset_of_mem_open (mem_univ T.ρ) isOpen_univ
    exact ⟨U, hUb⟩
  obtain ⟨e, he⟩ := hbc.exists_eq_range hbne
  have hmem : ∀ j, e j ∈ b := fun j => he ▸ mem_range_self j
  refine ⟨e, fun j => hb.isOpen (hmem j),
    fun j => nonempty_iff_ne_empty.2 fun h => hb0 (h ▸ hmem j), fun U hU ⟨x, hx⟩ => ?_⟩
  obtain ⟨W, hWb, -, hWU⟩ := hb.exists_subset_of_mem_open hx hU
  rw [he] at hWb
  obtain ⟨j, rfl⟩ := hWb
  exact ⟨j, hWU⟩

/-- A basis of nonempty open sets of `K`, indexed by `ℕ`. -/
def Vb : ℕ → Set KnasterSpace := exists_basisSeq.choose

theorem isOpen_Vb (j : ℕ) : IsOpen (Vb j) := exists_basisSeq.choose_spec.1 j

theorem Vb_nonempty (j : ℕ) : (Vb j).Nonempty := exists_basisSeq.choose_spec.2.1 j

theorem exists_Vb_subset {U : Set KnasterSpace} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ j, Vb j ⊆ U :=
  exists_basisSeq.choose_spec.2.2 U hU hne

/-- `N j = {k | a_k ∈ V_j}`. -/
def Nset (j : ℕ) : Set ℕ := {k | T.a k ∈ Vb j}

theorem Nset_infinite (j : ℕ) : (Nset j).Infinite := by
  rw [show Nset j = {k | T.a k ∈ Vb j} from rfl, infinite_setOf_iff]
  intro n
  obtain ⟨k, hk, hak⟩ := T.a_dense _ (isOpen_Vb j) (Vb_nonempty j) n
  exact ⟨k, hk, hak⟩

/-- Density of the included attaching template points of a spine is equivalent to the encoded
condition (c). -/
theorem dense_iff_infinite (β : List (ℕ × ℕ)) (m : ℕ) (F : Set Piece) :
    (∀ j, {k | k ∈ Nset j ∧ child β m k ∈ F}.Infinite) ↔
      Dense {z | ∃ k, child β m k ∈ F ∧ T.a k = z} := by
  constructor
  · intro h
    rw [dense_iff_inter_open]
    intro U hU hne
    obtain ⟨j, hj⟩ := exists_Vb_subset hU hne
    obtain ⟨k, hk⟩ := (h j).nonempty
    exact ⟨T.a k, hj hk.1, k, hk.2, rfl⟩
  · intro h j
    rw [infinite_setOf_iff]
    intro n
    have hfin : (T.a '' {k | k < n}).Finite := (finite_lt_nat n).image _
    have hd := dense_diff_finite hiso h hfin
    obtain ⟨_, hzV, ⟨k, hk, rfl⟩, hkn⟩ :=
      dense_iff_inter_open.1 hd _ (isOpen_Vb j) (Vb_nonempty j)
    refine ⟨k, ?_, hzV, hk⟩
    by_contra hlt
    push Not at hlt
    exact hkn ⟨k, hlt, rfl⟩

theorem child_eq_childOf (β : List (ℕ × ℕ)) (m k : ℕ) : child β m k = childOf (spine β m) k :=
  rfl

/-! ### Small facts used below -/

theorem piece_meets_sdiff {P : Piece} {S : Set L2} (hPS : piece P ⊆ S) (w : L2) :
    (piece P ∩ (S \ {w})).Nonempty := by
  obtain ⟨x, hx, hxw⟩ := exists_mem_piece_ne P w
  exact ⟨x, hx, hPS hx, hxw⟩

theorem not_isDesc_block_spine (β β' : List (ℕ × ℕ)) (m : ℕ) (h : IsDesc (spine β m) (block β')) :
    ∃ n, IsDesc (spine β m) (childOf (block β') n) := by
  rcases isDesc_iff_eq_or_child.1 h with h | h
  · simp at h
  · exact h

/-! ### Necessity -/

/-- Convexity of `𝓕(A)` (Theorem 4.6(b)), in parent-closed form. -/
theorem pcs_parentClosed {A : Set L2} (hA : Reg A) : ParentClosed (pcs A) := by
  obtain ⟨hAX, hAc, hAp, -, -⟩ := hA
  intro P R Q hP hR hRP hPQ
  obtain ⟨n, rfl⟩ := exists_childOf hPQ
  by_cases hRQ : R = Q
  · exact hRQ ▸ hR
  have h1 : (A ∩ (brY Q (some n) \ {brW Q (some n)})).Nonempty := by
    obtain ⟨x, hx, hxS⟩ := piece_meets_sdiff (piece_subset_Y (.refl (childOf Q n)))
      (brW Q (some n))
    exact ⟨x, hP hx, hxS⟩
  by_cases hdesc : IsDesc R Q
  · obtain ⟨c, hc, hRc⟩ := hdesc.exists_child hRQ
    obtain ⟨n', rfl⟩ := exists_childOf hc
    have hnn : n ≠ n' := fun h => hRP (h ▸ hRc)
    have h2 : (A ∩ (brY Q (some n') \ {brW Q (some n')})).Nonempty := by
      obtain ⟨x, hx, hxS⟩ := piece_meets_sdiff (piece_subset_Y hRc) (brW Q (some n'))
      exact ⟨x, hR hx, hxS⟩
    exact piece_subset_of_crossing (b := some n) (b' := some n') hAX hAc hAp trivial trivial
      (fun h => hnn (Option.some.inj h)) h1 h2
  · obtain ⟨Q', hQ'⟩ : ∃ Q', Q.parent = some Q' := by
      rcases eq_root_or_parent Q with rfl | h
      · exact absurd (isDesc_root R) hdesc
      · exact h
    have h2 : (A ∩ (brY Q none \ {brW Q none})).Nonempty := by
      obtain ⟨x, hx, hxS⟩ := piece_meets_sdiff (piece_subset_Z hdesc) (brW Q none)
      exact ⟨x, hR hx, hxS⟩
    exact piece_subset_of_crossing (b := some n) (b' := none) hAX hAc hAp trivial ⟨Q', hQ'⟩
      (by simp) h1 h2

theorem pcs_pathConvex {A : Set L2} (hA : Reg A) : PathConvex (pcs A) :=
  (pathConvex_iff_parentClosed _).2 (pcs_parentClosed hA)

/-- Points of a piece off the attaching points avoid the other side and the child subtrees. -/
theorem phi_notMem_Z {P Q : Piece} (hP : P.parent = some Q) {z : KnasterSpace}
    (hz : z ∉ tset P) : phi P z ∉ Z P := by
  intro hZ
  have : phi P z ∈ Y P ∩ Z P := ⟨piece_subset_Y (.refl P) (phi_mem_piece P z), hZ⟩
  rw [Y_inter_Z hP, mem_singleton_iff, ← phi_opt] at this
  exact hz (Or.inr (phi_injective P this))

theorem phi_notMem_Y_child (P : Piece) {z : KnasterSpace} (hz : z ∉ tset P) (n : ℕ) :
    phi P z ∉ Y (childOf P n) := by
  intro hY
  have : phi P z ∈ Y (childOf P n) ∩ piece P := ⟨hY, phi_mem_piece P z⟩
  rw [Y_child_inter_piece, mem_singleton_iff, pt_childOf] at this
  exact hz (Or.inl ⟨n, (phi_injective P this).symm⟩)

/-- A block of `blocksU F` near a point of `S` off the attaching points and off a closed set
avoiding that point lies below a child of `S`. -/
theorem block_near_spine {β : List (ℕ × ℕ)} {m : ℕ} {F : Set Piece} {y : L2}
    (hy : y ∈ blocksU F) (hyZ : y ∉ Z (spine β m)) :
    ∃ β', block β' ∈ F ∧ y ∈ piece (block β') ∧ ∃ k, IsDesc (block β') (childOf (spine β m) k) := by
  obtain ⟨β', hβ', hyB⟩ := mem_iUnion₂.1 hy
  refine ⟨β', hβ', hyB, ?_⟩
  have hdesc : IsDesc (block β') (spine β m) := by
    by_contra h
    exact hyZ (piece_subset_Z h hyB)
  rcases isDesc_iff_eq_or_child.1 hdesc with h | h
  · simp at h
  · exact h

/-- **Theorem 4.6(c), necessity**, in the form of density of template points. -/
theorem pcs_dense {A : Set L2} (hA : Reg A) {β : List (ℕ × ℕ)} {m : ℕ}
    (hS : spine β m ∈ pcs A) : Dense {z | ∃ k, child β m k ∈ pcs A ∧ T.a k = z} := by
  set S := spine β m
  have hconv := pcs_pathConvex hA
  -- it suffices to approximate the points off the attaching template points
  suffices hsub : (tset S)ᶜ ⊆ closure {z | ∃ k, child β m k ∈ pcs A ∧ T.a k = z} by
    rw [dense_iff_closure_eq, eq_univ_iff_forall]
    intro z
    have := closure_minimal hsub isClosed_closure
    rw [(dense_compl_tset S).closure_eq] at this
    exact this (mem_univ z)
  intro z hz
  rw [_root_.mem_closure_iff]
  intro U hU hzU
  -- a metric neighbourhood in `ℓ²` pulled back into `U`
  have hnhds : U ∈ 𝓝 z := hU.mem_nhds hzU
  rw [(isClosedEmbedding_phi S).isInducing.nhds_eq_comap] at hnhds
  obtain ⟨t, ht, htU⟩ := mem_comap.1 hnhds
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 ht
  set x := phi S z
  have hxZ : x ∉ Z S := phi_notMem_Z (parent_spine β m) hz
  set Fb := {k | ε₀ / 2 ≤ 4 / 3 * lam (childOf S k)}
  have hFb : Fb.Finite := finite_big_children S (by positivity)
  set W := Z S ∪ ⋃ k ∈ Fb, Y (childOf S k)
  have hW : IsClosed W := (isClosed_Z S).union (hFb.isClosed_biUnion fun k _ => isClosed_Y _)
  have hxW : x ∉ W := by
    rintro (h | h)
    · exact hxZ h
    · obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 h
      exact phi_notMem_Y_child S hz k hk
  obtain ⟨η₁, hη₁, hη₁ball⟩ := Metric.isOpen_iff.1 hW.isOpen_compl x hxW
  have hxA : x ∈ closure (blocksU (pcs A)) := subset_closure_blocks hA (hS (phi_mem_piece S z))
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hxA (min (ε₀ / 2) η₁)
    (lt_min (by positivity) hη₁)
  have hxy' : dist y x < η₁ := by
    rw [dist_comm]
    exact lt_of_lt_of_le hxy (min_le_right _ _)
  have hyW : y ∉ W := hη₁ball (mem_ball.2 hxy')
  obtain ⟨β', hβ'F, hyB, k, hk⟩ := block_near_spine hy (fun h => hyW (Or.inl h))
  have hyY : y ∈ Y (childOf S k) := piece_subset_Y hk hyB
  have hkF : k ∉ Fb := fun h => hyW (Or.inr (mem_biUnion h hyY))
  simp only [Fb, mem_ofPred_eq, not_le] at hkF
  have h1 := dist_le_of_mem_Y hyY
  have h2 : dist (pt (childOf S k)) x < ε₀ := by
    have := dist_triangle (pt (childOf S k)) y x
    rw [dist_comm] at h1
    have h3 : dist y x < ε₀ / 2 := by
      rw [dist_comm]; exact lt_of_lt_of_le hxy (min_le_left _ _)
    linarith
  -- the child is included by convexity
  have hcA : childOf S k ∈ pcs A := by
    refine hconv (block β') S (childOf S k) hβ'F hS ⟨Or.inl hk, ?_⟩
    rintro ⟨c, hc, -, hSc⟩
    have := hSc.depth_le
    rw [depth_of_parent hc, depth_childOf] at this
    omega
  refine ⟨T.a k, htU ?_, k, hcA, rfl⟩
  apply hball
  rw [mem_ball]
  rw [pt_childOf, tpt_childOf_spine] at h2
  exact h2

/-- **Theorem 4.6, necessity.** -/
theorem pcs_admissible {A : Set L2} (hA : Reg A) : Admissible Nset (pcs A) where
  hasBlock := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := hA.2.2.2.1
    have := subset_closure_blocks hA hx
    have hempty : blocksU (pcs A) = ∅ := by
      ext y
      simp only [blocksU, mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      exact fun β hβ => absurd hβ (h β)
    rw [hempty, closure_empty] at this
    exact this
  convex := pcs_pathConvex hA
  dense := fun β m hS => (dense_iff_infinite β m (pcs A)).2 (pcs_dense hA hS)

/-! ### Sufficiency -/

/-- `Ψ F`: the closure of the union of the blocks of `F`. -/
def Psi (F : Set Piece) : Set L2 := closure (blocksU F)

theorem Psi_subset_X (F : Set Piece) : Psi F ⊆ X :=
  closure_minimal (iUnion₂_subset fun _ _ => piece_subset_X _) isClosed_X

theorem block_subset_Psi {F : Set Piece} {β : List (ℕ × ℕ)} (h : block β ∈ F) :
    piece (block β) ⊆ Psi F :=
  fun _ hx => subset_closure (mem_iUnion₂.2 ⟨β, h, hx⟩)

theorem spine_subset_Psi {F : Set Piece} (hF : Admissible Nset F) {β : List (ℕ × ℕ)} {m : ℕ}
    (hS : spine β m ∈ F) : piece (spine β m) ⊆ Psi F := by
  have hd := (dense_iff_infinite β m F).1 (hF.dense β m hS)
  refine (piece_subset_closure_image _ hd).trans (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have : phi (spine β m) (T.a k) = pt (child β m k) := by
    rw [child_eq_childOf, pt_childOf, tpt_childOf_spine]
  rw [this]
  exact block_subset_Psi hk (pt_mem_piece _)

theorem piece_subset_Psi {F : Set Piece} (hF : Admissible Nset F) {P : Piece} (hP : P ∈ F) :
    piece P ⊆ Psi F := by
  cases P with
  | block β => exact block_subset_Psi hP
  | spine β m => exact spine_subset_Psi hF hP

/-- Two members of a parent-closed set are joined by a chain of members with successive
intersecting pieces. -/
theorem climb {F : Set Piece} (hpc : ParentClosed F) {R P : Piece} (h : IsDesc R P)
    (hR : R ∈ F) (hP : P ∈ F) :
    Relation.ReflTransGen (fun p q : F => adjP p q) ⟨R, hR⟩ ⟨P, hP⟩ := by
  induction h with
  | refl => exact .refl
  | @step R' Q P' hp hdesc ih =>
    have hPR : ¬ IsDesc P' R' := by
      intro h'
      have h1 := h'.depth_le
      have h2 := hdesc.depth_le
      have h3 := depth_of_parent hp
      omega
    have hQ : Q ∈ F := hpc R' P' Q hR hP hPR hp
    exact Relation.ReflTransGen.head (b := ⟨Q, hQ⟩)
      ⟨pt R', pt_mem_piece R', pt_mem_piece_parent hp⟩ (ih hQ hP)

instance (F : Set Piece) : Std.Symm (fun p q : F => adjP p q) :=
  ⟨fun p q h => Std.Symm.symm (r := adjP) p.1 q.1 h⟩

theorem chain {F : Set Piece} (hpc : ParentClosed F) : ∀ n, ∀ P (hP : P ∈ F), P.depth = n →
    ∀ R (hR : R ∈ F), Relation.ReflTransGen (fun p q : F => adjP p q) ⟨P, hP⟩ ⟨R, hR⟩ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hP hPn R hR
    by_cases hRP : IsDesc R P
    · exact Std.Symm.symm _ _ (climb hpc hRP hR hP)
    · obtain ⟨Q, hQ⟩ : ∃ Q, P.parent = some Q := by
        rcases eq_root_or_parent P with rfl | h
        · exact absurd (isDesc_root R) hRP
        · exact h
      have hQF : Q ∈ F := hpc P R Q hP hR hRP hQ
      exact Relation.ReflTransGen.head (b := ⟨Q, hQF⟩)
        ⟨pt P, pt_mem_piece P, pt_mem_piece_parent hQ⟩
        (ih Q.depth (by rw [← hPn, depth_of_parent hQ]; omega) Q hQF rfl R hR)

theorem Psi_eq_closure_union {F : Set Piece} (hF : Admissible Nset F) :
    Psi F = closure (⋃ P : F, piece P.1) := by
  apply Subset.antisymm
  · exact closure_mono (iUnion₂_subset fun β hβ =>
      subset_iUnion_of_subset (⟨_, hβ⟩ : F) subset_rfl)
  · exact closure_minimal (iUnion_subset fun P => piece_subset_Psi hF P.2) isClosed_closure

theorem isPreconnected_Psi {F : Set Piece} (hF : Admissible Nset F) :
    IsPreconnected (Psi F) := by
  rw [Psi_eq_closure_union hF]
  refine (IsPreconnected.iUnion_of_reflTransGen
    (fun P : F => (isConnected_piece P.1).isPreconnected) fun P R => ?_).closure
  exact chain hF.parentClosed _ P.1 P.2 rfl R.1 R.2

/-- **Theorem 4.6, sufficiency (regularity).** -/
theorem reg_Psi {F : Set Piece} (hF : Admissible Nset F) : Reg (Psi F) := by
  refine ⟨Psi_subset_X F, isCompact_X.of_isClosed_subset isClosed_closure (Psi_subset_X F),
    isPreconnected_Psi hF, ?_, blocksU_subset_closure_relInt F _ subset_closure⟩
  obtain ⟨β, hβ⟩ := hF.hasBlock
  exact ⟨_, block_subset_Psi hβ (pt_mem_piece _)⟩

/-- **Theorem 4.6, sufficiency (no unrecorded piece).** -/
theorem pcs_Psi {F : Set Piece} (hF : Admissible Nset F) : pcs (Psi F) = F := by
  ext P
  refine ⟨fun hP => ?_, fun hP => piece_subset_Psi hF hP⟩
  cases P with
  | block β =>
    -- the interior of the block meets an included block
    obtain ⟨x, hx⟩ : (relInt (piece (block β))).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      have := piece_subset_closure_relInt_block β (pt_mem_piece (block β))
      rw [h, closure_empty] at this
      exact this
    obtain ⟨r, hr, hrball⟩ := relInt_open hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 (hP (relInt_subset _ hx)) r hr
    obtain ⟨β', hβ', hyB⟩ := mem_iUnion₂.1 hy
    have hyint : y ∈ relInt (piece (block β)) :=
      hrball y (piece_subset_X _ hyB) (by rw [dist_comm]; exact hxy)
    by_cases hββ : block β' = block β
    · rw [← hββ]; exact hβ'
    · exact absurd hyB (disjoint_left.1 (relInt_piece_disjoint hββ) hyint)
  | spine β m =>
    set S := spine β m
    obtain ⟨z, hz⟩ := (dense_compl_tset S).nonempty
    set x := phi S z
    have hxZ : x ∉ Z S := phi_notMem_Z (parent_spine β m) hz
    have hxA : x ∈ Psi F := hP (phi_mem_piece S z)
    obtain ⟨η₁, hη₁, hη₁ball⟩ := Metric.isOpen_iff.1 (isClosed_Z S).isOpen_compl x hxZ
    obtain ⟨y₁, hy₁, hxy₁⟩ := Metric.mem_closure_iff.1 hxA η₁ hη₁
    obtain ⟨β₁, hβ₁, hy₁B, k₁, hk₁⟩ := block_near_spine hy₁
      (hη₁ball (by rw [mem_ball, dist_comm]; exact hxy₁))
    have hxY : x ∉ Z S ∪ Y (childOf S k₁) := by
      rintro (h | h)
      · exact hxZ h
      · exact phi_notMem_Y_child S hz k₁ h
    obtain ⟨η₂, hη₂, hη₂ball⟩ := Metric.isOpen_iff.1
      ((isClosed_Z S).union (isClosed_Y _)).isOpen_compl x hxY
    obtain ⟨y₂, hy₂, hxy₂⟩ := Metric.mem_closure_iff.1 hxA η₂ hη₂
    have hy₂W := hη₂ball (by rw [mem_ball, dist_comm]; exact hxy₂)
    obtain ⟨β₂, hβ₂, hy₂B, k₂, hk₂⟩ := block_near_spine hy₂ (fun h => hy₂W (Or.inl h))
    have hk : k₁ ≠ k₂ := by
      rintro rfl
      exact hy₂W (Or.inr (piece_subset_Y hk₂ hy₂B))
    refine hF.convex (block β₁) (block β₂) S hβ₁ hβ₂ ⟨Or.inl ?_, ?_⟩
    · exact hk₁.trans (.of_parent (parent_childOf S k₁))
    · rintro ⟨c, hc, h1, h2⟩
      obtain ⟨n, rfl⟩ := exists_childOf hc
      have e1 := eq_of_isDesc_childOf hk₁ h1
      have e2 := eq_of_isDesc_childOf hk₂ h2
      exact hk (e1.trans e2.symm)

/-- **Theorem 4.6, representation.** -/
theorem Psi_pcs {A : Set L2} (hA : Reg A) : Psi (pcs A) = A := (eq_closure_blocks hA).symm

/-! ### Lemma 5.1 -/

/-- The finite set `𝒫_N`. -/
def PN (N : ℕ) : Set Piece := {P | (1 / 2 : ℝ) ^ N ≤ lam P}

theorem infDist_le_of_agree {F F' : Set Piece} (hF : Admissible Nset F) (hF' : Admissible Nset F')
    {N : ℕ} (hagree : ∀ P ∈ PN N, (P ∈ F ↔ P ∈ F')) {R : Piece} (hR : R ∈ F ∩ PN N)
    {y : L2} (hy : y ∈ Psi F') : infDist y (Psi F) ≤ 4 / 3 * (1 / 2) ^ N := by
  have hcl : IsClosed {w : L2 | infDist w (Psi F) ≤ 4 / 3 * (1 / 2) ^ N} :=
    isClosed_le (continuous_infDist_pt _) continuous_const
  refine closure_minimal ?_ hcl hy
  intro w hw
  obtain ⟨β, hβ, hwB⟩ := mem_iUnion₂.1 hw
  simp only [mem_ofPred_eq]
  by_cases hBN : (1 / 2 : ℝ) ^ N ≤ lam (block β)
  · have : block β ∈ F := (hagree _ hBN).2 hβ
    rw [infDist_zero_of_mem (block_subset_Psi this hwB)]
    positivity
  · push Not at hBN
    obtain ⟨P, Q, hBP, hP, hPQ, hQ⟩ := exists_first_out N (block β).depth (block β) rfl hBN
    have hRP : ¬ IsDesc R P := fun h => by
      have := lam_le_of_isDesc h
      have := hR.2
      simp only [PN, mem_ofPred_eq] at this
      linarith
    have hRF' : R ∈ F' := (hagree R hR.2).1 hR.1
    have hQF' : Q ∈ F' := by
      refine hF'.convex (block β) R Q hβ hRF' ⟨Or.inl (hBP.trans (.of_parent hPQ)), ?_⟩
      rintro ⟨c, hc, hBc, hRc⟩
      have hcP : c = P := by
        rcases hBc.total hBP with h | h
        · exact h.eq_of_depth_le (by rw [depth_of_parent hc, depth_of_parent hPQ])
        · exact (h.eq_of_depth_le (by rw [depth_of_parent hc, depth_of_parent hPQ])).symm
      exact hRP (hcP ▸ hRc)
    have hQF : Q ∈ F := (hagree Q hQ).2 hQF'
    have hptP : pt P ∈ Psi F := piece_subset_Psi hF hQF (pt_mem_piece_parent hPQ)
    obtain ⟨z, rfl⟩ := hwB
    calc infDist (phi (block β) z) (Psi F) ≤ dist (phi (block β) z) (pt P) :=
          infDist_le_dist_of_mem hptP
      _ ≤ 4 / 3 * lam P := dist_phi_pt_le' hBP z
      _ ≤ 4 / 3 * (1 / 2) ^ N := by linarith

/-- **Lemma 5.1.** -/
theorem hausdorffDist_Psi_le {F F' : Set Piece} (hF : Admissible Nset F)
    (hF' : Admissible Nset F') {N : ℕ} (hagree : ∀ P ∈ PN N, (P ∈ F ↔ P ∈ F'))
    (hne : (F ∩ PN N).Nonempty) :
    hausdorffDist (Psi F) (Psi F') ≤ 4 / 3 * (1 / 2) ^ N := by
  obtain ⟨R, hR⟩ := hne
  have hR' : R ∈ F' ∩ PN N := ⟨(hagree R hR.2).1 hR.1, hR.2⟩
  refine hausdorffDist_le_of_infDist (by positivity) (fun y hy => ?_) (fun y hy => ?_)
  · exact infDist_le_of_agree hF' hF (fun P hP => (hagree P hP).symm) hR' hy
  · exact infDist_le_of_agree hF hF' hagree hR hy

end RegSub

end
