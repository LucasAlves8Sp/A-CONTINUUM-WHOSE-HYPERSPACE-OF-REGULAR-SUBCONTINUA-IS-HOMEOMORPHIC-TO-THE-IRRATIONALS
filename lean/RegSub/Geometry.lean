module

public import RegSub.Construction

@[expose] public section

/-!
# Geometry of `X` (Lemma 3.3)

* `piece P = φ_P(K)`, `Y P` = closure of the union of the pieces below `P`,
  `Z P` = closure of the union of the other pieces, `X = Y B_∅`;
* (c) `Y P = P ∪ ⋃ₙ Y (childOf P n)`;
* (d) the coordinate `C P` is constant on each child subtree;
* (e) `C P` vanishes on `Z P` and, for non-root `P`, vanishes on `Y P` only at `p_P`;
* (f) child subtrees are disjoint and meet `P` only at their attaching points;
* (g) `X = Y P ∪ Z P` and `Y P ∩ Z P = {p_P}` for non-root `P`;
* (h) `X` is compact and connected.
-/

open Set Filter Topology Function Metric

noncomputable section

namespace RegSub

open Piece

/-- The piece `P` as a subset of `ℓ²`. -/
def piece (P : Piece) : Set L2 := range (phi P)

/-- The union of the pieces below `P`. -/
def U (P : Piece) : Set L2 := ⋃ M, ⋃ (_ : IsDesc M P), piece M

/-- The union of the pieces not below `P`. -/
def Zu (P : Piece) : Set L2 := ⋃ M, ⋃ (_ : ¬ IsDesc M P), piece M

/-- `Y_P`. -/
def Y (P : Piece) : Set L2 := closure (U P)

/-- `Z_P`. -/
def Z (P : Piece) : Set L2 := closure (Zu P)

/-- The continuum `X`. -/
def X : Set L2 := Y root

/-! ### Basic facts about pieces -/

theorem isCompact_piece (P : Piece) : IsCompact (piece P) :=
  isCompact_range (continuous_phi P)

theorem isClosed_piece (P : Piece) : IsClosed (piece P) := (isCompact_piece P).isClosed

theorem isConnected_piece (P : Piece) : IsConnected (piece P) :=
  isConnected_range (continuous_phi P)

theorem phi_mem_piece (P : Piece) (z : KnasterSpace) : phi P z ∈ piece P := mem_range_self z

theorem pt_mem_piece (P : Piece) : pt P ∈ piece P := phi_opt P ▸ phi_mem_piece P _

theorem pt_childOf_mem_piece (P : Piece) (n : ℕ) : pt (childOf P n) ∈ piece P := by
  rw [pt_childOf]
  exact phi_mem_piece P _

theorem pt_mem_piece_parent {M Q : Piece} (h : M.parent = some Q) : pt M ∈ piece Q := by
  rw [pt_of_parent h]
  exact phi_mem_piece Q _

/-- A piece is not a single point. -/
theorem exists_mem_piece_ne (P : Piece) (w : L2) : ∃ x ∈ piece P, x ≠ w := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne KnasterSpace
  by_cases h : phi P a = w
  · exact ⟨phi P b, phi_mem_piece P b, fun h' => hab (phi_injective P (h.trans h'.symm))⟩
  · exact ⟨phi P a, phi_mem_piece P a, h⟩

/-- Every point of a piece is a limit of other points of the piece. -/
theorem exists_mem_piece_near (P : Piece) (z : KnasterSpace) {ε : ℝ} (hε : 0 < ε) :
    ∃ z', z' ≠ z ∧ dist (phi P z') (phi P z) < ε := by
  have hc := (continuous_phi P).continuousAt (x := z)
  rw [ContinuousAt, Metric.tendsto_nhds] at hc
  have hev := hc ε hε
  by_contra hcon
  push Not at hcon
  -- then `{z}` would be a neighbourhood of `z`
  have : {z} ∈ 𝓝 z := by
    filter_upwards [hev] with z' hz'
    by_contra hne
    exact absurd hz' (not_lt.2 (hcon z' hne))
  exact knaster_not_isOpen_singleton z (isOpen_singleton_iff_nhds_eq_pure z |>.2
    (le_antisymm (le_pure_iff.2 this) (pure_le_nhds z)))

theorem piece_subset_U {M P : Piece} (h : IsDesc M P) : piece M ⊆ U P :=
  subset_iUnion₂_of_subset M h subset_rfl

theorem piece_subset_Y {M P : Piece} (h : IsDesc M P) : piece M ⊆ Y P :=
  (piece_subset_U h).trans subset_closure

theorem piece_subset_Zu {M P : Piece} (h : ¬ IsDesc M P) : piece M ⊆ Zu P :=
  subset_iUnion₂_of_subset M h subset_rfl

theorem piece_subset_Z {M P : Piece} (h : ¬ IsDesc M P) : piece M ⊆ Z P :=
  (piece_subset_Zu h).trans subset_closure

theorem isClosed_Y (P : Piece) : IsClosed (Y P) := isClosed_closure

theorem isClosed_Z (P : Piece) : IsClosed (Z P) := isClosed_closure

theorem isClosed_X : IsClosed X := isClosed_Y root

theorem U_root : U root = ⋃ M, piece M := by
  ext x
  simp only [U, mem_iUnion]
  exact ⟨fun ⟨M, _, h⟩ => ⟨M, h⟩, fun ⟨M, h⟩ => ⟨M, isDesc_root M, h⟩⟩

theorem piece_subset_X (M : Piece) : piece M ⊆ X := piece_subset_Y (isDesc_root M)

theorem Y_subset_X (P : Piece) : Y P ⊆ X :=
  closure_mono (iUnion₂_subset fun M _ => piece_subset_U (isDesc_root M))

theorem Z_subset_X (P : Piece) : Z P ⊆ X :=
  closure_mono (iUnion₂_subset fun M _ => piece_subset_U (isDesc_root M))

theorem pt_mem_Y (P : Piece) : pt P ∈ Y P := piece_subset_Y (.refl P) (pt_mem_piece P)

theorem pt_mem_Z {P Q : Piece} (h : P.parent = some Q) : pt P ∈ Z P :=
  piece_subset_Z (not_isDesc_of_depth_lt (by rw [depth_of_parent h]; omega))
    (pt_mem_piece_parent h)

/-! ### (b) the radius bound -/

theorem U_subset_closedBall (P : Piece) : U P ⊆ closedBall (pt P) (4 / 3 * lam P) := by
  refine iUnion₂_subset fun M hM => ?_
  rintro _ ⟨z, rfl⟩
  exact mem_closedBall.2 (dist_phi_pt_le' hM z)

/-- **Lemma 3.3(b).** -/
theorem Y_subset_closedBall (P : Piece) : Y P ⊆ closedBall (pt P) (4 / 3 * lam P) :=
  closure_minimal (U_subset_closedBall P) isClosed_closedBall

theorem dist_le_of_mem_Y {P : Piece} {x : L2} (hx : x ∈ Y P) : dist x (pt P) ≤ 4 / 3 * lam P :=
  mem_closedBall.1 (Y_subset_closedBall P hx)

/-! ### (c) the subtree decomposition -/

theorem U_eq (P : Piece) : U P = piece P ∪ ⋃ n, U (childOf P n) := by
  ext x
  simp only [U, mem_iUnion, mem_union]
  constructor
  · rintro ⟨M, hM, hx⟩
    rcases isDesc_iff_eq_or_child.1 hM with rfl | ⟨n, hn⟩
    · exact Or.inl hx
    · exact Or.inr ⟨n, M, hn, hx⟩
  · rintro (hx | ⟨n, M, hn, hx⟩)
    · exact ⟨P, .refl P, hx⟩
    · exact ⟨M, isDesc_iff_eq_or_child.2 (Or.inr ⟨n, hn⟩), hx⟩

/-- Only finitely many children of `P` have `4/3 λ_c ≥ δ`. -/
theorem finite_big_children (P : Piece) {δ : ℝ} (hδ : 0 < δ) :
    {n | δ ≤ 4 / 3 * lam (childOf P n)}.Finite := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 3 / 4 * δ)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine (finite_lt_nat N).subset fun n hn => ?_
  simp only [mem_ofPred_eq] at hn ⊢
  by_contra hnN
  push Not at hnN
  have h1 : lam (childOf P n) ≤ (1 / 2) ^ (n + 2) := by
    rw [lam_childOf, div_eq_mul_one_div, mul_comm, one_div_pow]
    have := lam_le_one P
    have := lam_pos P
    have : (0 : ℝ) < 1 / 2 ^ (n + 2) := by positivity
    calc 1 / 2 ^ (n + 2) * lam P ≤ 1 / 2 ^ (n + 2) * 1 := by gcongr
      _ = 1 / 2 ^ (n + 2) := mul_one _
  have h2 : (1 / 2 : ℝ) ^ (n + 2) ≤ (1 / 2) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

/-- **Lemma 3.3(c).** -/
theorem Y_eq (P : Piece) : Y P = piece P ∪ ⋃ n, Y (childOf P n) := by
  apply Subset.antisymm
  · intro y hy
    by_cases hyP : y ∈ piece P
    · exact Or.inl hyP
    right
    have hδ : 0 < infDist y (piece P) :=
      ((isClosed_piece P).notMem_iff_infDist_pos ⟨_, pt_mem_piece P⟩).1 hyP
    set δ := infDist y (piece P)
    set F := {n | δ / 2 ≤ 4 / 3 * lam (childOf P n)}
    have hF : F.Finite := finite_big_children P (by positivity)
    have hsplit : U P ⊆ piece P ∪ (⋃ n ∈ F, U (childOf P n)) ∪
        ⋃ n ∈ Fᶜ, U (childOf P n) := by
      rw [U_eq]
      rintro x (hx | hx)
      · exact Or.inl (Or.inl hx)
      · obtain ⟨n, hn⟩ := mem_iUnion.1 hx
        by_cases hnF : n ∈ F
        · exact Or.inl (Or.inr (mem_biUnion hnF hn))
        · exact Or.inr (mem_biUnion hnF hn)
    have hy' := closure_mono hsplit hy
    rw [closure_union, closure_union, (isClosed_piece P).closure_eq,
      hF.closure_biUnion] at hy'
    rcases hy' with (hy' | hy') | hy'
    · exact absurd hy' hyP
    · obtain ⟨n, -, hn⟩ := mem_iUnion₂.1 hy'
      exact mem_iUnion.2 ⟨n, hn⟩
    · -- the small children stay close to `P`
      exfalso
      have hsub : (⋃ n ∈ Fᶜ, U (childOf P n)) ⊆ {w | infDist w (piece P) ≤ δ / 2} := by
        refine iUnion₂_subset fun n hn => ?_
        intro w hw
        simp only [F, mem_compl_iff, mem_ofPred_eq, not_le] at hn
        have h1 := U_subset_closedBall (childOf P n) hw
        rw [mem_closedBall] at h1
        have h2 := infDist_le_dist_of_mem (pt_childOf_mem_piece P n) (x := w)
        simp only [mem_ofPred_eq]
        linarith
      have hcl : IsClosed {w | infDist w (piece P) ≤ δ / 2} :=
        isClosed_le (continuous_infDist_pt _) continuous_const
      have := closure_minimal hsub hcl hy'
      simp only [mem_ofPred_eq] at this
      linarith
  · refine union_subset (piece_subset_Y (.refl P)) (iUnion_subset fun n => closure_mono ?_)
    exact iUnion₂_subset fun M hM => piece_subset_U (hM.trans (.of_parent (parent_childOf P n)))

/-! ### (d), (e) coordinates on subtrees -/

/-- **Lemma 3.3(d).** -/
theorem C_of_mem_Y_child {P : Piece} {n : ℕ} {x : L2} (hx : x ∈ Y (childOf P n)) :
    C P x = lam P • (ι (tpt (childOf P n)) - ι (opt P)) := by
  have hcl : IsClosed {w : L2 | C P w = lam P • (ι (tpt (childOf P n)) - ι (opt P))} :=
    isClosed_eq (continuous_C P) continuous_const
  refine closure_minimal ?_ hcl hx
  refine iUnion₂_subset fun M hM => ?_
  rintro _ ⟨z, rfl⟩
  exact C_phi_of_isDesc_child (parent_childOf P n) hM z

/-- **Lemma 3.3(e), first part.** -/
theorem C_of_mem_Z {P : Piece} {x : L2} (hx : x ∈ Z P) : C P x = 0 := by
  have hcl : IsClosed {w : L2 | C P w = 0} := isClosed_eq (continuous_C P) continuous_const
  refine closure_minimal ?_ hcl hx
  refine iUnion₂_subset fun M hM => ?_
  rintro _ ⟨z, rfl⟩
  exact C_phi_of_not_isDesc hM z

theorem C_pt_self (P : Piece) : C P (pt P) = 0 := by
  rw [← phi_opt, C_phi_self, sub_self, smul_zero]

theorem tpt_ne_opt {P Q : Piece} (h : P.parent = some Q) (n : ℕ) :
    tpt (childOf P n) ≠ opt P :=
  (ne_of_not_joinable (not_joinable_opt_tpt h n)).symm

/-- **Lemma 3.3(e), second part.** -/
theorem C_eq_zero_iff_of_mem_Y {P Q : Piece} (hP : P.parent = some Q) {x : L2} (hx : x ∈ Y P) :
    C P x = 0 ↔ x = pt P := by
  constructor
  · intro h0
    rw [Y_eq] at hx
    rcases hx with ⟨z, rfl⟩ | hx
    · rw [C_phi_self, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (lam_ne_zero P)
      · rw [sub_eq_zero] at h0
        rw [ι_injective h0, phi_opt]
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      rw [C_of_mem_Y_child hn, smul_eq_zero] at h0
      exfalso
      rcases h0 with h0 | h0
      · exact lam_ne_zero P h0
      · rw [sub_eq_zero] at h0
        exact tpt_ne_opt hP n (ι_injective h0)
  · rintro rfl
    exact C_pt_self P

/-! ### (f) disjointness of child subtrees -/

theorem Y_child_subset_Z {P : Piece} {n n' : ℕ} (h : n ≠ n') :
    Y (childOf P n') ⊆ Z (childOf P n) := by
  refine closure_mono (iUnion₂_subset fun M hM => piece_subset_Zu ?_)
  intro hMn
  exact h (eq_of_isDesc_childOf hMn hM)

theorem piece_subset_Z_child (P : Piece) (n : ℕ) : piece P ⊆ Z (childOf P n) :=
  piece_subset_Z (not_isDesc_child_self P n)

theorem pt_childOf_injective (P : Piece) : Injective fun n => pt (childOf P n) := by
  intro n n' h
  simp only [pt_childOf] at h
  by_contra hne
  exact ne_of_not_joinable (not_joinable_tpt P hne) (phi_injective P h)

/-- **Lemma 3.3(f).** -/
theorem disjoint_Y_child {P : Piece} {n n' : ℕ} (h : n ≠ n') :
    Disjoint (Y (childOf P n)) (Y (childOf P n')) := by
  rw [disjoint_left]
  intro x hx hx'
  have h1 : x = pt (childOf P n) :=
    (C_eq_zero_iff_of_mem_Y (parent_childOf P n) hx).1 (C_of_mem_Z (Y_child_subset_Z h hx'))
  have h2 : x = pt (childOf P n') :=
    (C_eq_zero_iff_of_mem_Y (parent_childOf P n') hx').1
      (C_of_mem_Z (Y_child_subset_Z (Ne.symm h) hx))
  exact h (pt_childOf_injective P (h1.symm.trans h2))

/-- **Lemma 3.3(f).** -/
theorem Y_child_inter_piece (P : Piece) (n : ℕ) :
    Y (childOf P n) ∩ piece P = {pt (childOf P n)} := by
  ext x
  constructor
  · rintro ⟨hx, hxP⟩
    exact (C_eq_zero_iff_of_mem_Y (parent_childOf P n) hx).1
      (C_of_mem_Z (piece_subset_Z_child P n hxP))
  · rintro rfl
    exact ⟨pt_mem_Y _, pt_childOf_mem_piece P n⟩

/-! ### (g) the two sides of a non-root piece -/

/-- **Lemma 3.3(g).** -/
theorem X_eq_Y_union_Z (P : Piece) : X = Y P ∪ Z P := by
  rw [X, Y, Y, Z, ← closure_union]
  congr 1
  rw [U_root]
  ext x
  simp only [U, Zu, mem_iUnion, mem_union]
  constructor
  · rintro ⟨M, hx⟩
    by_cases hM : IsDesc M P
    · exact Or.inl ⟨M, hM, hx⟩
    · exact Or.inr ⟨M, hM, hx⟩
  · rintro (⟨M, -, hx⟩ | ⟨M, -, hx⟩) <;> exact ⟨M, hx⟩

/-- **Lemma 3.3(g).** -/
theorem Y_inter_Z {P Q : Piece} (h : P.parent = some Q) : Y P ∩ Z P = {pt P} := by
  ext x
  constructor
  · rintro ⟨hY, hZ⟩
    exact (C_eq_zero_iff_of_mem_Y h hY).1 (C_of_mem_Z hZ)
  · rintro rfl
    exact ⟨pt_mem_Y P, pt_mem_Z h⟩

theorem Z_root : Z root = ∅ := by
  have : Zu root = ∅ := by
    ext x
    simp only [Zu, mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
    intro M hM
    exact absurd (isDesc_root M) hM
  rw [Z, this, closure_empty]

/-- The decomposition of `X` around a piece. -/
theorem mem_X_cases (P : Piece) {x : L2} (hx : x ∈ X) :
    x ∈ piece P ∨ (∃ n, x ∈ Y (childOf P n)) ∨ (∃ Q, P.parent = some Q) ∧ x ∈ Z P := by
  rw [X_eq_Y_union_Z P] at hx
  rcases hx with hx | hx
  · rw [Y_eq] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl (mem_iUnion.1 hx))
  · rcases eq_root_or_parent P with rfl | hQ
    · rw [Z_root] at hx
      exact absurd hx (notMem_empty x)
    · exact Or.inr (Or.inr ⟨hQ, hx⟩)

/-! ### (h) `X` is a continuum -/

theorem totallyBounded_pieces : TotallyBounded (⋃ M, piece M) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 3 / 8 * ε)
    (by norm_num : (1 / 2 : ℝ) < 1)
  set F := {P : Piece | (1 / 2 : ℝ) ^ N ≤ lam P}
  have hF : F.Finite := finite_lam_ge N
  have hCc : IsCompact (⋃ P ∈ F, piece P) := hF.isCompact_biUnion fun P _ => isCompact_piece P
  obtain ⟨t, ht, hsub⟩ := Metric.totallyBounded_iff.1 hCc.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨_, ⟨M, rfl⟩, ⟨z, rfl⟩⟩
  by_cases hM : M ∈ F
  · obtain ⟨y, hy, hdist⟩ := mem_iUnion₂.1 (hsub (mem_biUnion hM (phi_mem_piece M z)))
    exact mem_biUnion hy (ball_subset_ball (by linarith) hdist)
  · simp only [F, mem_ofPred_eq, not_le] at hM
    obtain ⟨P, Q, hMP, hP, hPQ, hQ⟩ := exists_first_out N M.depth M rfl hM
    have hptP : pt P ∈ ⋃ P ∈ F, piece P := mem_biUnion hQ (pt_mem_piece_parent hPQ)
    obtain ⟨y, hy, hdist⟩ := mem_iUnion₂.1 (hsub hptP)
    refine mem_biUnion hy ?_
    rw [mem_ball] at hdist ⊢
    have h1 := dist_phi_pt_le' hMP z
    calc dist (phi M z) y ≤ dist (phi M z) (pt P) + dist (pt P) y := dist_triangle _ _ _
      _ < ε := by linarith

/-- **Lemma 3.3(h).** `X` is compact. -/
theorem isCompact_X : IsCompact X := by
  rw [X, Y, U_root]
  exact totallyBounded_pieces.closure.isCompact_of_isClosed isClosed_closure

/-- Two pieces meet. -/
def adjP (P Q : Piece) : Prop := (piece P ∩ piece Q).Nonempty

instance : Std.Symm adjP := ⟨fun P Q h => by unfold adjP at *; rwa [inter_comm]⟩

theorem reflTransGen_root (M : Piece) : Relation.ReflTransGen adjP M root := by
  induction h : M.depth using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    rcases eq_root_or_parent M with rfl | ⟨Q, hQ⟩
    · exact .refl
    · have hstep : adjP M Q := ⟨pt M, pt_mem_piece M, pt_mem_piece_parent hQ⟩
      exact Relation.ReflTransGen.head hstep
        (ih Q.depth (by rw [← h, depth_of_parent hQ]; omega) Q rfl)

theorem isPreconnected_pieces : IsPreconnected (⋃ M, piece M) := by
  refine IsPreconnected.iUnion_of_reflTransGen (fun M => (isConnected_piece M).isPreconnected)
    fun M M' => ?_
  exact (reflTransGen_root M).trans (Std.Symm.symm _ _ (reflTransGen_root M'))

/-- **Lemma 3.3(h).** `X` is connected. -/
theorem isConnected_X : IsConnected X := by
  rw [X, Y, U_root]
  refine ⟨⟨_, subset_closure (mem_iUnion.2 ⟨root, pt_mem_piece root⟩)⟩,
    isPreconnected_pieces.closure⟩

theorem X_nonempty : X.Nonempty := isConnected_X.nonempty

end RegSub

end
