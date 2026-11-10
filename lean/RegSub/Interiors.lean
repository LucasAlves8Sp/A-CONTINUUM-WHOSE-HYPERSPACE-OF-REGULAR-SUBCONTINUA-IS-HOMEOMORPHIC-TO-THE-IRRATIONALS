module

public import RegSub.Geometry

@[expose] public section

/-!
# Interiors (Lemma 3.5)

`relInt A` is the interior of `A` relative to `X`. We prove:
* (a) for a block `B`, `relInt B` is dense in `B` and meets no other piece;
* (c) the union of the relative interiors of the blocks is dense in `X`.
(Part (b) of the lemma, spines have empty interior, is not needed for Theorem A: the description
of `𝒟(X)` and the homeomorphism onto the code space only use (a) and (c).)
-/

open Set Filter Topology Function Metric

noncomputable section

namespace RegSub

open Piece

/-- The interior of `A` relative to `X`. -/
def relInt (A : Set L2) : Set L2 := {x | x ∈ A ∧ ∃ ε > 0, ∀ y ∈ X, dist y x < ε → y ∈ A}

theorem relInt_subset (A : Set L2) : relInt A ⊆ A := fun _ h => h.1

theorem relInt_mono {A B : Set L2} (h : A ⊆ B) : relInt A ⊆ relInt B := by
  rintro x ⟨hx, ε, hε, hball⟩
  exact ⟨h hx, ε, hε, fun y hy hyx => h (hball y hy hyx)⟩

/-- `relInt A` is open in `X`. -/
theorem relInt_open {A : Set L2} {x : L2} (hx : x ∈ relInt A) :
    ∃ ε > 0, ∀ y ∈ X, dist y x < ε → y ∈ relInt A := by
  obtain ⟨-, ε, hε, hball⟩ := hx
  refine ⟨ε / 2, by positivity, fun y hy hyx => ⟨hball y hy (by linarith), ε / 2, by positivity,
    fun w hw hwy => hball w hw ?_⟩⟩
  calc dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
    _ < ε := by linarith

/-- A point that is a limit of points of `X` outside `A` is not in `relInt A`. -/
theorem notMem_relInt_of_approx {A : Set L2} {w : L2}
    (h : ∀ ε > 0, ∃ y ∈ X, y ∉ A ∧ dist y w < ε) : w ∉ relInt A := by
  rintro ⟨-, ε, hε, hball⟩
  obtain ⟨y, hyX, hyA, hyw⟩ := h ε hε
  exact hyA (hball y hyX hyw)

/-- Blocks. -/
def IsBlock (P : Piece) : Prop := ∃ β, P = block β

theorem isBlock_childOf_spine (β : List (ℕ × ℕ)) (m k : ℕ) : IsBlock (childOf (spine β m) k) :=
  ⟨_, rfl⟩

/-! ### The template points used on a piece -/

/-- The template points of the attaching points of a piece: those of its children and its own. -/
def tset (P : Piece) : Set KnasterSpace := range (fun n => tpt (childOf P n)) ∪ {opt P}

theorem tset_countable (P : Piece) : (tset P).Countable :=
  (countable_range _).union (countable_singleton _)

theorem hiso : ∀ x : KnasterSpace, ¬ IsOpen ({x} : Set KnasterSpace) := knaster_not_isOpen_singleton

theorem dense_compl_tset (P : Piece) : Dense (tset P)ᶜ :=
  dense_compl_of_countable hiso (tset_countable P)

/-- The closure of the template points of a block is countable. -/
theorem closure_tset_block_countable (β : List (ℕ × ℕ)) :
    (closure (tset (block β))).Countable := by
  have hcl : IsClosed (insert T.rinf (range T.r) ∪ {T.ρ}) :=
    T.r_tendsto.isCompact_insert_range.isClosed.union isClosed_singleton
  have hc : (insert T.rinf (range T.r) ∪ {T.ρ}).Countable :=
    ((countable_insert (a := T.rinf)).2 (countable_range T.r)).union (countable_singleton T.ρ)
  refine hc.mono ?_
  refine closure_minimal ?_ hcl
  rintro z (⟨n, rfl⟩ | rfl)
  · exact Or.inl (mem_insert_of_mem _ ⟨n, rfl⟩)
  · exact Or.inr rfl

/-- The image of a dense subset of `K` under `φ_P` is dense in the piece. -/
theorem piece_subset_closure_image (P : Piece) {D : Set KnasterSpace} (hD : Dense D) :
    piece P ⊆ closure (phi P '' D) := by
  rintro _ ⟨z, rfl⟩
  exact image_closure_subset_closure_image (continuous_phi P) ⟨z, hD.closure_eq ▸ mem_univ z, rfl⟩

/-! ### (a) interiors of blocks -/

/-- Points of a block whose template point avoids the closure of the attaching template points
are interior points of the block. -/
theorem phi_mem_relInt_block (β : List (ℕ × ℕ)) {z : KnasterSpace}
    (hz : z ∉ closure (tset (block β))) : phi (block β) z ∈ relInt (piece (block β)) := by
  set B := block β
  set x := phi B z
  set D := closure (tset B)
  -- distance from the image of the attaching template points
  have hK1 : IsClosed (phi B '' D) :=
    ((isClosed_closure.isCompact).image (continuous_phi B)).isClosed
  have hxK1 : x ∉ phi B '' D := by
    rintro ⟨z', hz', hzz'⟩
    exact hz (phi_injective B hzz' ▸ hz')
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.1 hK1.isOpen_compl x hxK1
  have hpt_far : ∀ n, δ ≤ dist (pt (childOf B n)) x := by
    intro n
    by_contra hlt
    push Not at hlt
    have hmem : pt (childOf B n) ∈ phi B '' D := by
      rw [pt_childOf]
      exact ⟨_, subset_closure (Or.inl ⟨n, rfl⟩), rfl⟩
    exact hδball (mem_ball.2 hlt) hmem
  -- finitely many big children, and the parent side
  set F := {n | δ / 2 ≤ 4 / 3 * lam (childOf B n)}
  have hF : F.Finite := finite_big_children B (by positivity)
  set W := (⋃ n ∈ F, Y (childOf B n)) ∪ Z B
  have hW : IsClosed W := (hF.isClosed_biUnion fun n _ => isClosed_Y _).union (isClosed_Z B)
  have hxW : x ∉ W := by
    rintro (hx | hx)
    · obtain ⟨n, -, hn⟩ := mem_iUnion₂.1 hx
      have : x ∈ Y (childOf B n) ∩ piece B := ⟨hn, phi_mem_piece B z⟩
      rw [Y_child_inter_piece, mem_singleton_iff] at this
      have := hpt_far n
      rw [← ‹x = pt (childOf B n)›, dist_self] at this
      linarith
    · rcases eq_root_or_parent B with hroot | ⟨Q, hQ⟩
      · rw [hroot, Z_root] at hx
        exact hx
      · have : x ∈ Y B ∩ Z B := ⟨piece_subset_Y (.refl B) (phi_mem_piece B z), hx⟩
        rw [Y_inter_Z hQ, mem_singleton_iff] at this
        apply hxK1
        refine ⟨opt B, subset_closure (Or.inr rfl), ?_⟩
        rw [phi_opt, this]
  obtain ⟨ε₁, hε₁, hε₁ball⟩ := Metric.isOpen_iff.1 hW.isOpen_compl x hxW
  refine ⟨phi_mem_piece B z, min (δ / 2) ε₁, lt_min (by positivity) hε₁, fun y hy hyx => ?_⟩
  have hyW : y ∉ W := hε₁ball (mem_ball.2 (lt_of_lt_of_le hyx (min_le_right _ _)))
  rcases mem_X_cases B hy with hyB | ⟨n, hn⟩ | ⟨-, hZ⟩
  · exact hyB
  · by_cases hnF : n ∈ F
    · exact absurd (Or.inl (mem_biUnion hnF hn)) hyW
    · exfalso
      simp only [F, mem_ofPred_eq, not_le] at hnF
      have h1 := dist_le_of_mem_Y hn
      have h2 := hpt_far n
      have h3 : dist y x < δ / 2 := lt_of_lt_of_le hyx (min_le_left _ _)
      have := dist_triangle (pt (childOf B n)) y x
      rw [dist_comm] at h1
      linarith
  · exact absurd (Or.inr hZ) hyW

/-- **Lemma 3.5(a).** The relative interior of a block is dense in it. -/
theorem piece_subset_closure_relInt_block (β : List (ℕ × ℕ)) :
    piece (block β) ⊆ closure (relInt (piece (block β))) := by
  have hD : Dense (closure (tset (block β)))ᶜ :=
    dense_compl_of_countable hiso (closure_tset_block_countable β)
  refine (piece_subset_closure_image (block β) hD).trans (closure_mono ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact phi_mem_relInt_block β hz

/-- Attaching points of children are not interior to the parent piece. -/
theorem pt_child_notMem_relInt (P : Piece) (n : ℕ) : pt (childOf P n) ∉ relInt (piece P) := by
  refine notMem_relInt_of_approx fun ε hε => ?_
  set c := childOf P n
  obtain ⟨z', hz', hdist⟩ := exists_mem_piece_near c (opt c) hε
  refine ⟨phi c z', piece_subset_X c (phi_mem_piece c z'), fun hP => ?_, ?_⟩
  · have : phi c z' ∈ Y c ∩ piece P := ⟨piece_subset_Y (.refl c) (phi_mem_piece c z'), hP⟩
    rw [Y_child_inter_piece, mem_singleton_iff, ← phi_opt] at this
    exact hz' (phi_injective c this)
  · rwa [phi_opt] at hdist

/-- The attaching point of a non-root piece is not interior to it. -/
theorem pt_notMem_relInt {P Q : Piece} (hP : P.parent = some Q) : pt P ∉ relInt (piece P) := by
  refine notMem_relInt_of_approx fun ε hε => ?_
  obtain ⟨z', hz', hdist⟩ := exists_mem_piece_near Q (tpt P) hε
  refine ⟨phi Q z', piece_subset_X Q (phi_mem_piece Q z'), fun hPmem => ?_, ?_⟩
  · have h1 : phi Q z' ∈ Y P ∩ Z P :=
      ⟨piece_subset_Y (.refl P) hPmem, piece_subset_Z
        (not_isDesc_of_depth_lt (by rw [depth_of_parent hP]; omega)) (phi_mem_piece Q z')⟩
    rw [Y_inter_Z hP, mem_singleton_iff, pt_of_parent hP] at h1
    exact hz' (phi_injective Q h1)
  · rwa [← pt_of_parent hP] at hdist

/-- Another piece meets a piece `P` only at attaching points of `P`. -/
theorem piece_inter_piece_subset {P R : Piece} (hRP : R ≠ P) {x : L2} (hxR : x ∈ piece R)
    (hxP : x ∈ piece P) : (∃ n, x = pt (childOf P n)) ∨ ∃ Q, P.parent = some Q ∧ x = pt P := by
  by_cases hdesc : IsDesc R P
  · obtain ⟨c, hc, hRc⟩ := hdesc.exists_child hRP
    obtain ⟨n, rfl⟩ := exists_childOf hc
    have : x ∈ Y (childOf P n) ∩ piece P := ⟨piece_subset_Y hRc hxR, hxP⟩
    rw [Y_child_inter_piece, mem_singleton_iff] at this
    exact Or.inl ⟨n, this⟩
  · rcases eq_root_or_parent P with rfl | ⟨Q, hQ⟩
    · exact absurd (isDesc_root R) hdesc
    · have : x ∈ Y P ∩ Z P := ⟨piece_subset_Y (.refl P) hxP, piece_subset_Z hdesc hxR⟩
      rw [Y_inter_Z hQ, mem_singleton_iff] at this
      exact Or.inr ⟨Q, hQ, this⟩

/-- **Lemma 3.5(a).** The relative interior of a piece meets no other piece. -/
theorem relInt_piece_disjoint {P R : Piece} (hRP : R ≠ P) :
    Disjoint (relInt (piece P)) (piece R) := by
  rw [disjoint_left]
  intro x hxint hxR
  rcases piece_inter_piece_subset hRP hxR (relInt_subset _ hxint) with ⟨n, rfl⟩ | ⟨Q, hQ, rfl⟩
  · exact pt_child_notMem_relInt P n hxint
  · exact pt_notMem_relInt hQ hxint

/-! ### (c) density of the block interiors -/

/-- The union of the relative interiors of the blocks. -/
def Ublk : Set L2 := ⋃ β : List (ℕ × ℕ), relInt (piece (block β))

theorem block_subset_closure_Ublk (β : List (ℕ × ℕ)) : piece (block β) ⊆ closure Ublk :=
  (piece_subset_closure_relInt_block β).trans (closure_mono (subset_iUnion
    (fun β => relInt (piece (block β))) β))

theorem lam_childOf_lt (P : Piece) {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀, ∀ k, k₀ ≤ k → 4 / 3 * lam (childOf P k) < ε := by
  obtain ⟨k₀, hk₀⟩ := (finite_big_children P hε).bddAbove
  refine ⟨k₀ + 1, fun k hk => ?_⟩
  by_contra h
  push Not at h
  have := hk₀ h
  omega

/-- Every point of a spine is a limit of points of its child blocks. -/
theorem spine_approx (β : List (ℕ × ℕ)) (m : ℕ) (z : KnasterSpace) {ε : ℝ} (hε : 0 < ε) (k₀ : ℕ) :
    ∃ k, k₀ ≤ k ∧ ∀ y ∈ Y (childOf (spine β m) k), dist y (phi (spine β m) z) < ε := by
  set S := spine β m
  have hW : IsOpen (phi S ⁻¹' ball (phi S z) (ε / 2)) :=
    isOpen_ball.preimage (continuous_phi S)
  obtain ⟨k₁, hk₁⟩ := lam_childOf_lt S (by positivity : 0 < ε / 2)
  obtain ⟨k, hk, hak⟩ := T.a_dense _ hW ⟨z, mem_ball_self (by positivity)⟩ (max k₀ k₁)
  refine ⟨k, (le_max_left _ _).trans hk, fun y hy => ?_⟩
  have h1 := dist_le_of_mem_Y hy
  have h2 := hk₁ k ((le_max_right _ _).trans hk)
  have h3 : dist (pt (childOf S k)) (phi S z) < ε / 2 := by
    rw [pt_childOf, tpt_childOf_spine]
    exact hak
  calc dist y (phi S z) ≤ dist y (pt (childOf S k)) + dist (pt (childOf S k)) (phi S z) :=
        dist_triangle _ _ _
    _ < ε := by linarith

theorem spine_subset_closure_Ublk (β : List (ℕ × ℕ)) (m : ℕ) :
    piece (spine β m) ⊆ closure Ublk := by
  rintro _ ⟨z, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨k, -, hk⟩ := spine_approx β m z (by positivity : 0 < ε / 2) 0
  set c := childOf (spine β m) k
  have hc : pt c ∈ closure Ublk := block_subset_closure_Ublk _ (pt_mem_piece c)
  obtain ⟨u, hu, hdist⟩ := Metric.mem_closure_iff.1 hc (ε / 2) (by positivity)
  refine ⟨u, hu, ?_⟩
  have := hk (pt c) (pt_mem_Y c)
  calc dist (phi (spine β m) z) u ≤ dist (phi (spine β m) z) (pt c) + dist (pt c) u :=
        dist_triangle _ _ _
    _ < ε := by rw [dist_comm] at this; linarith

/-- **Lemma 3.5(c).** The union of the interiors of the blocks is dense in `X`. -/
theorem X_subset_closure_Ublk : X ⊆ closure Ublk := by
  rw [X, Y, U_root]
  refine closure_minimal (iUnion_subset fun M => ?_) isClosed_closure
  cases M with
  | block β => exact block_subset_closure_Ublk β
  | spine β m => exact spine_subset_closure_Ublk β m

theorem relInt_subset_X (A : Set L2) (hA : A ⊆ X) : relInt A ⊆ X :=
  (relInt_subset A).trans hA

end RegSub

end
