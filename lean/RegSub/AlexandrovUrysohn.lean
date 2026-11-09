import Mathlib.Topology.MetricSpace.CantorScheme
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Order.OrderIsoNat
import RegSub.GdeltaPolish

/-!
# The Alexandrov–Urysohn characterization of the Baire space

**Theorem** (Alexandrov–Urysohn; Kechris, *Classical Descriptive Set Theory*, Theorem 7.7).
A nonempty zero-dimensional Polish space in which every compact subset has empty interior is
homeomorphic to the Baire space `ℕ → ℕ`.

Proof. Fix a complete compatible metric. Every nonempty clopen set `U` is not compact (it is its
own interior), so it is the union of infinitely many pairwise disjoint nonempty clopen sets of
diameter `≤ ε` (`exists_clopen_partition`). Iterating gives a Lusin scheme `A : List ℕ → Set X`
of nonempty clopen sets; Mathlib's `CantorScheme` shows that the induced map `(ℕ → ℕ) → X` is
defined everywhere, continuous and injective. It is onto because the children of each set cover
it, and open because it maps cylinders onto the (open) sets of the scheme.
-/

open Set Filter Topology TopologicalSpace Metric PiNat

namespace RegSub

section Disj

variable {X : Type*}

/-- Disjointification of a sequence of sets. -/
def disj (c : ℕ → Set X) (n : ℕ) : Set X := c n \ ⋃ i ∈ Finset.range n, c i

theorem disj_subset (c : ℕ → Set X) (n : ℕ) : disj c n ⊆ c n := sdiff_subset

theorem iUnion_disj (c : ℕ → Set X) : ⋃ n, disj c n = ⋃ n, c n := by
  classical
  refine Subset.antisymm (iUnion_mono fun n => disj_subset c n) ?_
  intro x hx
  rw [mem_iUnion] at hx
  have hex : ∃ n, x ∈ c n := hx
  refine mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  simp only [mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and]
  exact fun i hi hxi => Nat.find_min hex hi hxi

theorem disjoint_disj (c : ℕ → Set X) {i j : ℕ} (hij : i ≠ j) : Disjoint (disj c i) (disj c j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine disjoint_left.2 fun x hxi hxj => hxj.2 ?_
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 h)) hxi.1
  · refine disjoint_left.2 fun x hxi hxj => hxi.2 ?_
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 h)) hxj.1

theorem isClopen_disj [TopologicalSpace X] {c : ℕ → Set X} (hc : ∀ n, IsClopen (c n)) (n : ℕ) :
    IsClopen (disj c n) :=
  (hc n).diff (isClopen_biUnion_finset fun i _ => hc i)

end Disj

section Partition

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [ZeroDimensionalSpace X]

/-- A nonempty clopen non-compact set is the union of a sequence of pairwise disjoint nonempty
clopen sets of diameter at most `ε`. -/
theorem exists_clopen_partition {U : Set X} (hU : IsClopen U) (hUne : U.Nonempty)
    (hUc : ¬ IsCompact U) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : ℕ → Set X, (∀ n, IsClopen (W n)) ∧ (∀ n, (W n).Nonempty) ∧
      (∀ n, ∀ x ∈ W n, ∀ y ∈ W n, dist x y ≤ ε) ∧ (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
      ⋃ n, W n = U := by
  classical
  -- an open cover of `U` without finite subcover
  rw [isCompact_iff_finite_subcover] at hUc
  push Not at hUc
  obtain ⟨ι, O, hO, hUO, hfin⟩ := hUc
  -- small clopen sets inside `U` and inside a member of the cover
  let C : Set (Set X) :=
    {W | IsClopen W ∧ W ⊆ U ∧ (∀ x ∈ W, ∀ y ∈ W, dist x y ≤ ε) ∧ ∃ i, W ⊆ O i}
  have hCU : ⋃₀ C = U := by
    refine Subset.antisymm (sUnion_subset fun W hW => hW.2.1) fun x hx => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hUO hx)
    have hopen : IsOpen (U ∩ O i ∩ ball x (ε / 2)) :=
      (hU.isOpen.inter (hO i)).inter isOpen_ball
    obtain ⟨W, hWb, hxW, hWsub⟩ :=
      (isTopologicalBasis_isClopen (X := X)).exists_subset_of_mem_open
        (show x ∈ U ∩ O i ∩ ball x (ε / 2) from ⟨⟨hx, hi⟩, mem_ball_self (by linarith)⟩) hopen
    refine mem_sUnion.2 ⟨W, ⟨hWb, fun y hy => (hWsub hy).1.1, ?_, i, fun y hy => (hWsub hy).1.2⟩,
      hxW⟩
    intro y hy z hz
    have h1 := (hWsub hy).2
    have h2 := (hWsub hz).2
    rw [mem_ball] at h1 h2
    calc dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
      _ ≤ ε := by linarith
  obtain ⟨T, hTc, hTC, hTU⟩ := isOpen_sUnion_countable C fun W hW => hW.1.isOpen
  have hTne : T.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    rw [sUnion_empty, hCU] at hTU
    exact hUne.ne_empty hTU.symm
  obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
  have hcC : ∀ n, c n ∈ C := fun n => hTC (hc ▸ mem_range_self n)
  have hcU : ⋃ n, c n = U := by rw [← hCU, ← hTU, hc, sUnion_range]
  let D := disj c
  -- infinitely many of the `D n` are nonempty
  let S : Set ℕ := {n | (D n).Nonempty}
  have hS : S.Infinite := by
    intro hSfin
    obtain ⟨M, hM⟩ := hSfin.bddAbove
    choose i hi using fun n => (hcC n).2.2.2
    apply hfin ((Finset.range (M + 1)).image i)
    intro x hx
    rw [← hcU, ← iUnion_disj] at hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    have hnM : n ≤ M := hM ⟨x, hn⟩
    refine mem_biUnion (Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega),
      rfl⟩)) (hi n (disj_subset c n hn))
  have : Infinite S := hS.to_subtype
  let e := Nat.Subtype.orderIsoOfNat S
  refine ⟨fun k => D (e k), fun k => isClopen_disj (fun n => (hcC n).1) _, fun k => (e k).2,
    fun k x hx y hy => (hcC _).2.2.1 x (disj_subset c _ hx) y (disj_subset c _ hy),
    fun i j hij => disjoint_disj c (fun h => hij (e.injective (Subtype.ext h))), ?_⟩
  rw [← hcU, ← iUnion_disj c]
  refine Subset.antisymm (iUnion_mono' fun k => ⟨e k, le_rfl⟩) fun x hx => ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  obtain ⟨k, hk⟩ := e.surjective ⟨n, ⟨x, hn⟩⟩
  refine mem_iUnion.2 ⟨k, ?_⟩
  rw [hk]
  exact hn

end Partition

section Scheme

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [ZeroDimensionalSpace X]

/-- The chosen partition of a set (empty if the hypotheses fail). -/
noncomputable def part (U : Set X) (ε : ℝ) : ℕ → Set X := by
  classical
  exact if h : IsClopen U ∧ U.Nonempty ∧ ¬ IsCompact U ∧ 0 < ε then
    (exists_clopen_partition h.1 h.2.1 h.2.2.1 h.2.2.2).choose else fun _ => ∅

theorem part_spec {U : Set X} {ε : ℝ} (hU : IsClopen U) (hUne : U.Nonempty) (hUc : ¬ IsCompact U)
    (hε : 0 < ε) :
    (∀ n, IsClopen (part U ε n)) ∧ (∀ n, (part U ε n).Nonempty) ∧
      (∀ n, ∀ x ∈ part U ε n, ∀ y ∈ part U ε n, dist x y ≤ ε) ∧
      (∀ i j, i ≠ j → Disjoint (part U ε i) (part U ε j)) ∧ ⋃ n, part U ε n = U := by
  have h : IsClopen U ∧ U.Nonempty ∧ ¬ IsCompact U ∧ 0 < ε := ⟨hU, hUne, hUc, hε⟩
  unfold part
  rw [dite_eq_left h]
  exact (exists_clopen_partition h.1 h.2.1 h.2.2.1 h.2.2.2).choose_spec

/-- The Lusin scheme: `A [] = univ`, and `A (n :: l)` is the `n`-th piece of the partition of
`A l` into sets of diameter `≤ 2^{-(|l|+1)}`. -/
noncomputable def scheme : List ℕ → Set X
  | [] => univ
  | n :: l => part (scheme l) ((1 / 2) ^ (l.length + 1)) n

variable [Nonempty X] (hK : ∀ K : Set X, IsCompact K → interior K = ∅)
include hK

omit [SecondCountableTopology X] [ZeroDimensionalSpace X] [Nonempty X] in
theorem not_isCompact_of_isOpen {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ¬ IsCompact U :=
  fun hc => hne.ne_empty (by rw [← hU.interior_eq]; exact hK U hc)

theorem scheme_clopen_nonempty : ∀ l : List ℕ, IsClopen (scheme (X := X) l) ∧ (scheme (X := X) l).Nonempty
  | [] => ⟨isClopen_univ, univ_nonempty⟩
  | n :: l => by
    obtain ⟨h1, h2⟩ := scheme_clopen_nonempty l
    have := part_spec h1 h2 (not_isCompact_of_isOpen hK h1.isOpen h2) (by positivity :
      (0 : ℝ) < (1 / 2) ^ (l.length + 1))
    exact ⟨this.1 n, this.2.1 n⟩

theorem scheme_spec (l : List ℕ) :
    (∀ n, ∀ x ∈ scheme (X := X) (n :: l), ∀ y ∈ scheme (X := X) (n :: l),
        dist x y ≤ (1 / 2) ^ (l.length + 1)) ∧
      (∀ i j, i ≠ j → Disjoint (scheme (X := X) (i :: l)) (scheme (X := X) (j :: l))) ∧
      ⋃ n, scheme (X := X) (n :: l) = scheme (X := X) l := by
  obtain ⟨h1, h2⟩ := scheme_clopen_nonempty hK l
  have := part_spec h1 h2 (not_isCompact_of_isOpen hK h1.isOpen h2) (by positivity :
    (0 : ℝ) < (1 / 2) ^ (l.length + 1))
  exact ⟨this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩

theorem scheme_antitone : CantorScheme.Antitone (scheme (X := X)) := by
  intro l n
  rw [← (scheme_spec hK l).2.2]
  exact subset_iUnion (fun n => scheme (X := X) (n :: l)) n

theorem scheme_disjoint : CantorScheme.Disjoint (scheme (X := X)) :=
  fun l i j hij => (scheme_spec hK l).2.1 i j hij

theorem scheme_vanishingDiam : CantorScheme.VanishingDiam (scheme (X := X)) := by
  intro x
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  -- choose `n` with `2^{-n} < ε`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ENNReal.ofReal ((1 / 2) ^ (n + 1)) ≤ ε := by
    rcases eq_or_ne ε ⊤ with h | h
    · exact ⟨0, h ▸ le_top⟩
    · have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε' (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨n, ?_⟩
      rw [ENNReal.ofReal_le_iff_le_toReal h]
      calc (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ n :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
        _ ≤ ε.toReal := hn.le
  refine ⟨n + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show n + 1 + k = (n + k) + 1 by ring, res_succ]
  refine Metric.ediam_le fun y hy z hz => ?_
  have h := (scheme_spec hK (res x (n + k))).1 _ y hy z hz
  rw [res_length] at h
  rw [edist_dist]
  refine le_trans (ENNReal.ofReal_le_ofReal (h.trans ?_)) hn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem scheme_closureAntitone : CantorScheme.ClosureAntitone (scheme (X := X)) :=
  (scheme_antitone hK).closureAntitone fun l => (scheme_clopen_nonempty hK l).1.isClosed

/-- Two sets of the scheme at the same level that meet have the same label. -/
theorem eq_of_scheme_inter : ∀ (l l' : List ℕ), l.length = l'.length →
    (scheme (X := X) l ∩ scheme l').Nonempty → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, ⟨x, hx1, hx2⟩ => by
    have hl : l = l' := eq_of_scheme_inter l l' (by simpa using h)
      ⟨x, scheme_antitone hK l a hx1, scheme_antitone hK l' b hx2⟩
    subst hl
    by_cases hab : a = b
    · rw [hab]
    · exact absurd ⟨x, hx1, hx2⟩ (disjoint_iff_inter_eq_empty.1
        ((scheme_spec hK l).2.1 a b hab) ▸ Set.not_nonempty_empty)

end Scheme

/-- **The Alexandrov–Urysohn theorem** (Kechris, Theorem 7.7). -/
theorem alexandrovUrysohn (X : Type*) [TopologicalSpace X] [PolishSpace X]
    [ZeroDimensionalSpace X] [Nonempty X] (hK : ∀ K : Set X, IsCompact K → interior K = ∅) :
    Nonempty ((ℕ → ℕ) ≃ₜ X) := by
  let := upgradeIsCompletelyMetrizable X
  have hdom := (scheme_closureAntitone hK).map_of_vanishingDiam (scheme_vanishingDiam hK)
    fun l => (scheme_clopen_nonempty hK l).2
  let g := (CantorScheme.inducedMap (scheme (X := X))).2
  let f : (ℕ → ℕ) → X := fun x => g ⟨x, by rw [hdom]; trivial⟩
  have hfmem : ∀ x n, f x ∈ scheme (res x n) := fun x n =>
    CantorScheme.map_mem (A := scheme (X := X)) ⟨x, by rw [hdom]; trivial⟩ n
  have hfcont : Continuous f :=
    (scheme_vanishingDiam hK).map_continuous.comp (continuous_id.subtype_mk _)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have := (scheme_disjoint hK).map_injective hxy
    exact congrArg Subtype.val this
  -- the key: `f x ∈ A l` with `|l| = n` forces `l = res x n`
  have hkey : ∀ x l, f x ∈ scheme l → l = res x l.length := fun x l hx =>
    eq_of_scheme_inter hK l (res x l.length) (by rw [res_length]) ⟨f x, hx, hfmem x _⟩
  have hfsurj : Function.Surjective f := by
    intro y
    classical
    have hchild : ∀ l : List ℕ, y ∈ scheme l → ∃ a, y ∈ scheme (a :: l) := by
      intro l hl
      rw [← (scheme_spec hK l).2.2] at hl
      exact mem_iUnion.1 hl
    let idx : List ℕ → ℕ := fun l => if h : ∃ a, y ∈ scheme (a :: l) then h.choose else 0
    let L : ℕ → List ℕ := fun n => Nat.rec [] (fun _ l => idx l :: l) n
    have hL : ∀ n, y ∈ scheme (L n) := by
      intro n
      induction n with
      | zero => trivial
      | succ n ih =>
        show y ∈ scheme (idx (L n) :: L n)
        have h := hchild _ ih
        simp only [idx, dite_eq_left h]
        try exact h.choose_spec
    let x : ℕ → ℕ := fun n => idx (L n)
    have hres : ∀ n, res x n = L n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [res_succ, ih]
    refine ⟨x, ?_⟩
    -- `f x` and `y` lie in sets of arbitrarily small diameter
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    have h1 := hfmem x (n + 1)
    have h2 : y ∈ scheme (res x (n + 1)) := by rw [hres]; exact hL (n + 1)
    rw [res_succ] at h1 h2
    have := (scheme_spec hK (res x n)).1 _ _ h1 _ h2
    rw [res_length] at this
    exact this.trans ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans
      hn.le)
  -- images of cylinders are the sets of the scheme
  have himage : ∀ x n, f '' cylinder x n = scheme (res x n) := by
    intro x n
    refine Subset.antisymm ?_ fun z hz => ?_
    · rintro _ ⟨w, hw, rfl⟩
      rw [cylinder_eq_res, mem_ofPred] at hw
      rw [← hw]
      exact hfmem w n
    · obtain ⟨w, rfl⟩ := hfsurj z
      refine ⟨w, ?_, rfl⟩
      rw [cylinder_eq_res, mem_ofPred]
      have := hkey w _ hz
      rw [res_length] at this
      exact this.symm
  have hfopen : IsOpenMap f := by
    rw [(isTopologicalBasis_cylinders (E := fun _ : ℕ => ℕ)).isOpenMap_iff]
    rintro _ ⟨x, n, rfl⟩
    rw [himage]
    exact (scheme_clopen_nonempty hK _).1.isOpen
  exact ⟨(Equiv.ofBijective f ⟨hfinj, hfsurj⟩).toHomeomorphOfContinuousOpen hfcont hfopen⟩

end RegSub
