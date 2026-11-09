import RegSub.Interiors

/-!
# The regular subcontinua of `X` (Section 4)

* the retractions `r_M` (`ret`), Lemma 4.3(i);
* branches (Definition 4.1, Lemma 4.2), encoded by `Option ℕ`: `some n` is the branch of the
  `n`-th child, `none` the parent side of a non-root piece;
* the crossing lemma, Lemma 4.3(iii),(iv);
* pieces are atoms, Lemma 4.4;
* regularity comes from blocks, Lemma 4.5.
-/

open Set Filter Topology Function Metric

noncomputable section

namespace RegSub

open Piece

/-! ### Retractions (Lemma 4.3(i)) -/

/-- The retraction `r_M(x) = p_M + π_M(x)`. -/
def ret (M : Piece) (x : L2) : L2 := pt M + J M (C M x)

theorem ret_phi (M : Piece) (z : KnasterSpace) : ret M (phi M z) = phi M z := by
  rw [ret, C_phi_self, map_smul, phi]

theorem ret_of_mem_piece {M : Piece} {x : L2} (hx : x ∈ piece M) : ret M x = x := by
  obtain ⟨z, rfl⟩ := hx
  exact ret_phi M z

theorem ret_of_mem_Y_child {M : Piece} {n : ℕ} {x : L2} (hx : x ∈ Y (childOf M n)) :
    ret M x = pt (childOf M n) := by
  rw [ret, C_of_mem_Y_child hx, map_smul, pt_childOf, phi]

theorem ret_of_mem_Z {M : Piece} {x : L2} (hx : x ∈ Z M) : ret M x = pt M := by
  rw [ret, C_of_mem_Z hx, map_zero, add_zero]

theorem continuous_ret (M : Piece) : Continuous (ret M) :=
  continuous_const.add ((continuous_J M).comp (continuous_C M))

/-! ### Branches (Lemma 4.2) -/

/-- The closed side containing the branch. -/
def brY (M : Piece) : Option ℕ → Set L2
  | some n => Y (childOf M n)
  | none => Z M

/-- The complementary closed side. -/
def brZ (M : Piece) : Option ℕ → Set L2
  | some n => Z (childOf M n)
  | none => Y M

/-- The attaching point of the branch. -/
def brW (M : Piece) : Option ℕ → L2
  | some n => pt (childOf M n)
  | none => pt M

/-- The template point of the attaching point. -/
def brT (M : Piece) : Option ℕ → KnasterSpace
  | some n => tpt (childOf M n)
  | none => opt M

/-- A branch exists: child branches always, the parent branch only for non-root pieces. -/
def Valid (M : Piece) : Option ℕ → Prop
  | some _ => True
  | none => ∃ Q, M.parent = some Q

theorem isClosed_brY (M : Piece) (b : Option ℕ) : IsClosed (brY M b) := by
  cases b <;> simp only [brY] <;> first | exact isClosed_Y _ | exact isClosed_Z _

theorem isClosed_brZ (M : Piece) (b : Option ℕ) : IsClosed (brZ M b) := by
  cases b <;> simp only [brZ] <;> first | exact isClosed_Y _ | exact isClosed_Z _

theorem X_eq_brY_union_brZ (M : Piece) (b : Option ℕ) : X = brY M b ∪ brZ M b := by
  cases b with
  | none => rw [brY, brZ, union_comm]; exact X_eq_Y_union_Z M
  | some n => exact X_eq_Y_union_Z (childOf M n)

theorem brY_inter_brZ {M : Piece} {b : Option ℕ} (hb : Valid M b) :
    brY M b ∩ brZ M b = {brW M b} := by
  cases b with
  | none =>
    obtain ⟨Q, hQ⟩ := hb
    rw [brY, brZ, brW, inter_comm]
    exact Y_inter_Z hQ
  | some n => exact Y_inter_Z (parent_childOf M n)

theorem brW_eq (M : Piece) (b : Option ℕ) : brW M b = phi M (brT M b) := by
  cases b with
  | none => exact (phi_opt M).symm
  | some n => exact pt_childOf M n

theorem brW_mem_piece (M : Piece) (b : Option ℕ) : brW M b ∈ piece M := by
  rw [brW_eq]
  exact phi_mem_piece M _

theorem piece_subset_brZ (M : Piece) (b : Option ℕ) : piece M ⊆ brZ M b := by
  cases b with
  | none => exact piece_subset_Y (.refl M)
  | some n => exact piece_subset_Z_child M n

theorem ret_of_mem_brY {M : Piece} {b : Option ℕ} {x : L2} (hx : x ∈ brY M b) :
    ret M x = brW M b := by
  cases b with
  | none => exact ret_of_mem_Z hx
  | some n => exact ret_of_mem_Y_child hx

/-- Every point of `X` lies in `M` or in (the closed side of) a branch at `M`. -/
theorem mem_X_branch (M : Piece) {x : L2} (hx : x ∈ X) :
    x ∈ piece M ∨ ∃ b, Valid M b ∧ x ∈ brY M b := by
  rcases mem_X_cases M hx with h | ⟨n, hn⟩ | ⟨hQ, hZ⟩
  · exact Or.inl h
  · exact Or.inr ⟨some n, trivial, hn⟩
  · exact Or.inr ⟨none, hQ, hZ⟩

/-- Distinct branches: the open branch of one lies in the far side of the other. -/
theorem brY_sdiff_subset {M : Piece} {b b' : Option ℕ} (hb : Valid M b) (hb' : Valid M b')
    (hne : b ≠ b') : brY M b \ {brW M b} ⊆ brZ M b' \ {brW M b'} := by
  rintro y ⟨hy, hyw⟩
  rw [mem_singleton_iff] at hyw
  -- `y` is not the attaching point of `b'`, which lies in `M`
  have hyw' : y ≠ brW M b' := by
    intro hyeq
    apply hyw
    have hyM : y ∈ piece M := hyeq ▸ brW_mem_piece M b'
    have : y ∈ brY M b ∩ brZ M b := ⟨hy, piece_subset_brZ M b hyM⟩
    rwa [brY_inter_brZ hb, mem_singleton_iff] at this
  refine ⟨?_, hyw'⟩
  cases b with
  | none =>
    cases b' with
    | none => exact absurd rfl hne
    | some n' =>
      -- `Z M ⊆ Z (childOf M n')`
      refine closure_mono (iUnion₂_subset fun R hR => piece_subset_Zu ?_) hy
      exact fun h => hR (h.trans (.of_parent (parent_childOf M n')))
  | some n =>
    cases b' with
    | none =>
      exact closure_mono (iUnion₂_subset fun R hR =>
        piece_subset_U (hR.trans (.of_parent (parent_childOf M n)))) hy
    | some n' =>
      have hnn : n ≠ n' := fun h => hne (h ▸ rfl)
      exact Y_child_subset_Z (Ne.symm hnn) hy

theorem not_joinable_brT {M : Piece} {b b' : Option ℕ} (hb : Valid M b) (hb' : Valid M b')
    (hne : b ≠ b') : ¬ Joinable (brT M b) (brT M b') := by
  cases b with
  | none =>
    cases b' with
    | none => exact absurd rfl hne
    | some n' =>
      obtain ⟨Q, hQ⟩ := hb
      exact not_joinable_opt_tpt hQ n'
  | some n =>
    cases b' with
    | none =>
      obtain ⟨Q, hQ⟩ := hb'
      exact fun h => not_joinable_opt_tpt hQ n h.symm
    | some n' =>
      exact not_joinable_tpt M (fun h => hne (h ▸ rfl))

/-! ### The crossing lemma (Lemma 4.3) -/

/-- **Lemma 4.3(iii)**, in a general form: a connected subset of `X` meeting both sides of a
one-point cut contains the cut point. -/
theorem mem_of_cut {A Y' Z' : Set L2} {w : L2} (hY' : IsClosed Y') (hZ' : IsClosed Z')
    (hX : X = Y' ∪ Z') (hYZ : Y' ∩ Z' = {w}) (hAX : A ⊆ X) (hA : IsPreconnected A)
    (h1 : (A ∩ (Y' \ {w})).Nonempty) (h2 : (A ∩ (Z' \ {w})).Nonempty) : w ∈ A := by
  by_contra hw
  have hcover : A ⊆ Z'ᶜ ∪ Y'ᶜ := by
    intro a ha
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    have : a ∈ Y' ∩ Z' := ⟨hcon.2, hcon.1⟩
    rw [hYZ, mem_singleton_iff] at this
    exact hw (this ▸ ha)
  have hu : (A ∩ Z'ᶜ).Nonempty := by
    obtain ⟨a, ha, haY, haw⟩ := h1
    refine ⟨a, ha, fun haZ => haw ?_⟩
    have : a ∈ Y' ∩ Z' := ⟨haY, haZ⟩
    rwa [hYZ] at this
  have hv : (A ∩ Y'ᶜ).Nonempty := by
    obtain ⟨a, ha, haZ, haw⟩ := h2
    refine ⟨a, ha, fun haY => haw ?_⟩
    have : a ∈ Y' ∩ Z' := ⟨haY, haZ⟩
    rwa [hYZ] at this
  obtain ⟨a, ha, hau, hav⟩ := hA _ _ hZ'.isOpen_compl hY'.isOpen_compl hcover hu hv
  have := hAX ha
  rw [hX] at this
  rcases this with h | h
  · exact hav h
  · exact hau h

theorem brW_mem {M : Piece} {b : Option ℕ} (hb : Valid M b) {A : Set L2} (hAX : A ⊆ X)
    (hA : IsPreconnected A) (h1 : (A ∩ (brY M b \ {brW M b})).Nonempty)
    (h2 : (A ∩ (brZ M b \ {brW M b})).Nonempty) : brW M b ∈ A :=
  mem_of_cut (isClosed_brY M b) (isClosed_brZ M b) (X_eq_brY_union_brZ M b) (brY_inter_brZ hb)
    hAX hA h1 h2

/-- A closed connected subset of a piece containing two non-joinable template points is the
whole piece; formulated through `φ_M`. -/
theorem piece_subset_of_preimage {M : Piece} {S : Set L2} (hS : IsClosed S)
    (hSc : IsPreconnected S) (hSM : S ⊆ piece M) {z z' : KnasterSpace}
    (hzz' : ¬ Joinable z z') (hz : phi M z ∈ S) (hz' : phi M z' ∈ S) : piece M ⊆ S := by
  have hpre : IsPreconnected (phi M ⁻¹' S) := by
    rw [← (isClosedEmbedding_phi M).isInducing.isPreconnected_image,
      image_preimage_eq_of_subset hSM]
    exact hSc
  have := eq_univ_of_not_joinable hzz' (hS.preimage (continuous_phi M)) hpre hz hz'
  rintro _ ⟨y, rfl⟩
  have : y ∈ phi M ⁻¹' S := this ▸ mem_univ y
  exact this

/-- **Lemma 4.3(iv).** A compact connected subset of `X` meeting two distinct branches at `M`
contains `M`. -/
theorem piece_subset_of_crossing {M : Piece} {A : Set L2} (hAX : A ⊆ X) (hAc : IsCompact A)
    (hA : IsPreconnected A) {b b' : Option ℕ} (hb : Valid M b) (hb' : Valid M b') (hne : b ≠ b')
    (h1 : (A ∩ (brY M b \ {brW M b})).Nonempty) (h1' : (A ∩ (brY M b' \ {brW M b'})).Nonempty) :
    piece M ⊆ A := by
  -- (iii): `A` meets the far side of every branch it meets
  have hfar : ∀ b'', Valid M b'' → (A ∩ (brY M b'' \ {brW M b''})).Nonempty →
      brW M b'' ∈ A := by
    intro b'' hb'' hmeet
    apply brW_mem hb'' hAX hA hmeet
    by_cases hbb : b = b''
    · subst hbb
      obtain ⟨a, ha, ha'⟩ := h1'
      exact ⟨a, ha, brY_sdiff_subset hb' hb (Ne.symm hne) ha'⟩
    · obtain ⟨a, ha, ha'⟩ := h1
      exact ⟨a, ha, brY_sdiff_subset hb hb'' hbb ha'⟩
  -- the retraction maps `A` into `A`
  have hret : ret M '' A ⊆ A := by
    rintro _ ⟨x, hx, rfl⟩
    rcases mem_X_branch M (hAX hx) with hxM | ⟨b'', hb'', hxb⟩
    · rw [ret_of_mem_piece hxM]
      exact hx
    · rw [ret_of_mem_brY hxb]
      by_cases hxw : x = brW M b''
      · exact hxw ▸ hx
      · exact hfar b'' hb'' ⟨x, hx, hxb, hxw⟩
  have hretM : ret M '' A ⊆ piece M := by
    rintro _ ⟨x, hx, rfl⟩
    rcases mem_X_branch M (hAX hx) with hxM | ⟨b'', -, hxb⟩
    · rw [ret_of_mem_piece hxM]
      exact hxM
    · rw [ret_of_mem_brY hxb]
      exact brW_mem_piece M b''
  have hw : ∀ b'', Valid M b'' → (A ∩ (brY M b'' \ {brW M b''})).Nonempty →
      phi M (brT M b'') ∈ ret M '' A := by
    intro b'' hb'' hmeet
    refine ⟨brW M b'', hfar b'' hb'' hmeet, ?_⟩
    rw [ret_of_mem_piece (brW_mem_piece M b''), brW_eq]
  have hsub := piece_subset_of_preimage ((hAc.image (continuous_ret M)).isClosed)
    (hA.image _ (continuous_ret M).continuousOn) hretM (not_joinable_brT hb hb' hne)
    (hw b hb h1) (hw b' hb' h1')
  exact hsub.trans hret

/-! ### Pieces are atoms (Lemma 4.4) -/

theorem ret_image_subset {M : Piece} {A : Set L2} (hAX : A ⊆ X) {z : KnasterSpace}
    (hz : phi M z ∈ ret M '' A) (hzT : z ∉ tset M) : phi M z ∈ A := by
  obtain ⟨a, ha, hret⟩ := hz
  rcases mem_X_branch M (hAX ha) with haM | ⟨b, -, hab⟩
  · rw [ret_of_mem_piece haM] at hret
    exact hret ▸ ha
  · rw [ret_of_mem_brY hab, brW_eq] at hret
    exfalso
    apply hzT
    rw [← phi_injective M hret]
    cases b with
    | none => exact Or.inr rfl
    | some n => exact Or.inl ⟨n, rfl⟩

/-- **Lemma 4.4.** If a compact connected subset of `X` has a relative interior point in a piece,
it contains the piece. -/
theorem piece_subset_of_relInt {P : Piece} {A : Set L2} (hAX : A ⊆ X) (hAc : IsCompact A)
    (hA : IsPreconnected A) (h : (relInt A ∩ piece P).Nonempty) : piece P ⊆ A := by
  obtain ⟨x, ⟨hxA, ε, hε, hball⟩, ⟨z₀, rfl⟩⟩ := h
  set S := phi P ⁻¹' (ret P '' A)
  have hRc : IsCompact (ret P '' A) := hAc.image (continuous_ret P)
  have hRsub : ret P '' A ⊆ piece P := by
    rintro _ ⟨a, ha, rfl⟩
    rcases mem_X_branch P (hAX ha) with haM | ⟨b, -, hab⟩
    · rw [ret_of_mem_piece haM]
      exact haM
    · rw [ret_of_mem_brY hab]
      exact brW_mem_piece P b
  have hSc : IsClosed S := hRc.isClosed.preimage (continuous_phi P)
  have hSp : IsPreconnected S := by
    rw [← (isClosedEmbedding_phi P).isInducing.isPreconnected_image,
      image_preimage_eq_of_subset hRsub]
    exact hA.image _ (continuous_ret P).continuousOn
  have hSint : (interior S).Nonempty := by
    refine ⟨z₀, mem_interior.2 ⟨phi P ⁻¹' ball (phi P z₀) ε, fun z hz => ?_,
      isOpen_ball.preimage (continuous_phi P), mem_ball_self hε⟩⟩
    have hzA : phi P z ∈ A := hball _ (piece_subset_X P (phi_mem_piece P z)) hz
    exact ⟨phi P z, hzA, ret_phi P z⟩
  have hSuniv := knaster_P2 S hSc hSp hSint
  -- the points of `P` off the attaching points lie in `A`
  have hdense : piece P ⊆ closure (phi P '' (tset P)ᶜ) :=
    piece_subset_closure_image P (dense_compl_tset P)
  refine hdense.trans (closure_minimal ?_ hAc.isClosed)
  rintro _ ⟨z, hz, rfl⟩
  have hzS : z ∈ S := hSuniv ▸ mem_univ z
  exact ret_image_subset hAX hzS hz

/-! ### Regularity comes from blocks (Lemma 4.5) -/

/-- Regular subcontinua of `X`, as subsets of `ℓ²`. -/
def Reg (A : Set L2) : Prop :=
  A ⊆ X ∧ IsCompact A ∧ IsPreconnected A ∧ A.Nonempty ∧ A ⊆ closure (relInt A)

/-- The pieces contained in `A`, `𝓕(A)`. -/
def pcs (A : Set L2) : Set Piece := {P | piece P ⊆ A}

/-- The union of the blocks of a set of pieces. -/
def blocksU (F : Set Piece) : Set L2 := ⋃ β, ⋃ (_ : block β ∈ F), piece (block β)

/-- **Lemma 4.5.** A regular subcontinuum is the closure of the union of the blocks it
contains. -/
theorem subset_closure_blocks {A : Set L2} (hA : Reg A) : A ⊆ closure (blocksU (pcs A)) := by
  obtain ⟨hAX, hAc, hAp, -, hAreg⟩ := hA
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, hyint, hxy⟩ := Metric.mem_closure_iff.1 (hAreg hx) (ε / 2) (by positivity)
  obtain ⟨r, hr, hrball⟩ := relInt_open hyint
  have hyX : y ∈ X := hAX (relInt_subset A hyint)
  obtain ⟨u, hu, huy⟩ := Metric.mem_closure_iff.1 (X_subset_closure_Ublk hyX) (min r (ε / 2))
    (lt_min hr (by positivity))
  obtain ⟨β, huB⟩ := mem_iUnion.1 hu
  have huX : u ∈ X := piece_subset_X _ (relInt_subset _ huB)
  have huA : u ∈ relInt A := hrball u huX (by rw [dist_comm]; exact lt_of_lt_of_le huy (min_le_left _ _))
  have hBA : piece (block β) ⊆ A :=
    piece_subset_of_relInt hAX hAc hAp ⟨u, huA, relInt_subset _ huB⟩
  refine ⟨u, mem_iUnion₂.2 ⟨β, hBA, relInt_subset _ huB⟩, ?_⟩
  calc dist x u ≤ dist x y + dist y u := dist_triangle _ _ _
    _ < ε := by
      have := lt_of_lt_of_le huy (min_le_right r (ε / 2))
      linarith

theorem eq_closure_blocks {A : Set L2} (hA : Reg A) : A = closure (blocksU (pcs A)) := by
  refine Subset.antisymm (subset_closure_blocks hA) (closure_minimal ?_ hA.2.1.isClosed)
  exact iUnion₂_subset fun β hβ => hβ

/-- **Lemma 4.5, converse.** The closure of a union of blocks is regular closed. -/
theorem blocksU_subset_closure_relInt (F : Set Piece) (A : Set L2) (hA : blocksU F ⊆ A) :
    closure (blocksU F) ⊆ closure (relInt A) := by
  refine closure_minimal (iUnion₂_subset fun β _ => ?_) isClosed_closure
  refine (piece_subset_closure_relInt_block β).trans (closure_mono (relInt_mono ?_))
  exact (subset_iUnion₂_of_subset β ‹_› subset_rfl).trans hA

end RegSub

end
