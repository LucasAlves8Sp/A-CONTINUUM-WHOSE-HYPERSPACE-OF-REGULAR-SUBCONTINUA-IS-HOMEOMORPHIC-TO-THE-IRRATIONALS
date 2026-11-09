import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Knaster continuum

The template continuum of the construction (Section 3.1 of the paper) is the Knaster
bucket-handle continuum. We use its standard description as the inverse limit of the unit interval
under the tent map `T(t) = min (2t) (2 - 2t)`:
`K = {x : ℕ → ℝ | ∀ n, x n ∈ [0,1] ∧ x n = T (x (n+1))}`,
with the product topology. (The paper draws `K` in the plane; the proof only uses that `K` is a
nondegenerate continuum whose proper subcontinua have empty interior, see Fact 2.4 and the
sentence "Any nondegenerate indecomposable plane continuum would suffice".)

Main results:
* `isCompact_knaster`, `isConnected_knaster`: `K` is a continuum;
* `knaster_nontrivial`: `K` has two distinct points;
* `eq_univ_of_interior_nonempty`: a closed connected subset of `K` with nonempty interior is all
  of `K` (Fact 2.4(a): proper subcontinua have empty interior).
-/

open Set Filter Topology

namespace RegSub

/-! ### The tent map -/

/-- The tent map `T(t) = min (2t) (2 - 2t)`. -/
def tent (t : ℝ) : ℝ := min (2 * t) (2 - 2 * t)

theorem continuous_tent : Continuous tent := by
  unfold tent; fun_prop

theorem tent_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : tent t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := ht
  unfold tent
  constructor
  · exact le_min (by linarith) (by linarith)
  · rcases le_total t (1 / 2) with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)

theorem tent_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : tent t = 2 * t := by
  unfold tent
  exact min_eq_left (by linarith)

theorem tent_one_sub (s : ℝ) : tent (1 - s) = tent s := by
  unfold tent
  rw [min_comm]
  congr 1 <;> ring

theorem abs_tent_sub_le (a b : ℝ) : |tent a - tent b| ≤ 2 * |a - b| := by
  unfold tent
  have h1 : |2 * a - 2 * b| = 2 * |a - b| := by
    rw [← mul_sub, abs_mul, abs_two]
  have h2 : |(2 - 2 * a) - (2 - 2 * b)| = 2 * |a - b| := by
    rw [show (2 - 2 * a) - (2 - 2 * b) = -(2 * (a - b)) by ring, abs_neg, abs_mul, abs_two]
  calc |min (2 * a) (2 - 2 * a) - min (2 * b) (2 - 2 * b)|
      ≤ max |2 * a - 2 * b| |(2 - 2 * a) - (2 - 2 * b)| := abs_min_sub_min_le_max _ _ _ _
    _ = 2 * |a - b| := by rw [h1, h2, max_self]

theorem tent_iterate_mem (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tent^[j] t ∈ Icc (0 : ℝ) 1 := by
  induction j generalizing t with
  | zero => simpa using ht
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (tent_mem ht)

theorem abs_tent_iterate_sub_le (j : ℕ) (a b : ℝ) :
    |tent^[j] a - tent^[j] b| ≤ 2 ^ j * |a - b| := by
  induction j generalizing a b with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    calc |tent^[j] (tent a) - tent^[j] (tent b)| ≤ 2 ^ j * |tent a - tent b| := ih _ _
      _ ≤ 2 ^ j * (2 * |a - b|) := by
          gcongr
          exact abs_tent_sub_le a b
      _ = 2 ^ (j + 1) * |a - b| := by ring

theorem continuous_tent_iterate (j : ℕ) : Continuous (tent^[j]) :=
  continuous_tent.iterate j

/-- On `[0, 2^{-j}]` the `j`-th iterate of the tent map is multiplication by `2^j`. -/
theorem tent_iterate_small (j : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2 ^ j) :
    tent^[j] s = 2 ^ j * s := by
  induction j generalizing s with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    have hs' : s ≤ 1 / 2 := by
      calc s ≤ 1 / 2 ^ (j + 1) := hs
        _ ≤ 1 / 2 := by
          rw [pow_succ]
          gcongr
          exact le_mul_of_one_le_left (by norm_num) (one_le_pow₀ (by norm_num))
    rw [tent_of_le_half hs', ih (by linarith)]
    · ring
    · calc 2 * s ≤ 2 * (1 / 2 ^ (j + 1)) := by linarith
        _ = 1 / 2 ^ j := by rw [pow_succ]; field_simp

theorem tent_iterate_one_sub (j : ℕ) (hj : 1 ≤ j) (s : ℝ) :
    tent^[j] (1 - s) = tent^[j] s := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [add_comm, Function.iterate_succ_apply, Function.iterate_succ_apply, tent_one_sub]

theorem tent_two_quarter {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : tent^[2] ((2 - t) / 4) = t := by
  obtain ⟨h0, h1⟩ := ht
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [tent_of_le_half (show (2 - t) / 4 ≤ 1 / 2 by linarith)]
  unfold tent
  rw [min_eq_right (by linarith)]
  ring

/-! ### The inverse limit -/

/-- The Knaster continuum as the inverse limit of `[0,1]` under the tent map. -/
def Knaster : Set (ℕ → ℝ) := {x | ∀ n, x n ∈ Icc (0 : ℝ) 1 ∧ x n = tent (x (n + 1))}

/-- Unfolding the first bonding relations. -/
theorem coord_of_bond {x : ℕ → ℝ} {N : ℕ} (hxb : ∀ i < N, x i = tent (x (i + 1))) :
    ∀ j n, n + j = N → x n = tent^[j] (x N) := by
  intro j
  induction j with
  | zero =>
    intro n h
    simp only [add_zero] at h
    subst h
    rfl
  | succ j ih =>
    intro n h
    rw [hxb n (by omega), ih (n + 1) (by omega), Function.iterate_succ_apply']

theorem knaster_coord_of_le {x : ℕ → ℝ} (hx : x ∈ Knaster) {n m : ℕ} (h : n ≤ m) :
    x n = tent^[m - n] (x m) :=
  coord_of_bond (fun i _ => (hx i).2) (m - n) n (by omega)

theorem isClosed_knaster : IsClosed Knaster := by
  have : Knaster = ⋂ n, ({x : ℕ → ℝ | x n ∈ Icc (0 : ℝ) 1} ∩ {x | x n = tent (x (n + 1))}) := by
    ext x; simp [Knaster]
  rw [this]
  refine isClosed_iInter fun n => IsClosed.inter ?_ ?_
  · exact isClosed_Icc.preimage (continuous_apply n)
  · exact isClosed_eq (continuous_apply n) (continuous_tent.comp (continuous_apply (n + 1)))

theorem knaster_subset_pi : Knaster ⊆ Set.pi univ fun _ => Icc (0 : ℝ) 1 :=
  fun _ hx n _ => (hx n).1

theorem isCompact_knaster : IsCompact Knaster :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset isClosed_knaster knaster_subset_pi

/-- Every value in `[0,1]` occurs as the `m`-th coordinate of a point of `K`. -/
theorem exists_knaster_coord (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Knaster, x m = t := by
  refine ⟨fun n => if n ≤ m then tent^[m - n] t else t / 2 ^ (n - m), ?_, by simp⟩
  have hsmall : ∀ j : ℕ, 1 ≤ j → t / 2 ^ j ≤ 1 / 2 := by
    intro j hj
    have h2 : (2 : ℝ) ≤ 2 ^ j := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [ht.1, ht.2]
  intro n
  by_cases hn : n + 1 ≤ m
  · have hn' : n ≤ m := by omega
    simp only [hn, hn', ite_true]
    refine ⟨tent_iterate_mem _ ht, ?_⟩
    rw [show m - n = (m - (n + 1)) + 1 by omega, Function.iterate_succ_apply']
  · by_cases hnm : n = m
    · subst hnm
      simp only [le_refl, ite_true, Nat.sub_self, Function.iterate_zero_apply,
        show ¬ n + 1 ≤ n by omega, ite_false, Nat.add_sub_cancel_left, pow_one]
      refine ⟨ht, ?_⟩
      rw [tent_of_le_half (by linarith [ht.2])]
      ring
    · have h1 : ¬ n ≤ m := by omega
      simp only [h1, hn, ite_false]
      have hpos : (0 : ℝ) < 2 ^ (n - m) := by positivity
      refine ⟨⟨div_nonneg ht.1 hpos.le, ?_⟩, ?_⟩
      · rw [div_le_one hpos]
        exact ht.2.trans (one_le_pow₀ (by norm_num))
      · rw [tent_of_le_half (hsmall _ (by omega)), show n + 1 - m = (n - m) + 1 by omega,
          pow_succ]
        field_simp

/-- The constant zero sequence lies in `K`. -/
theorem zero_mem_knaster : (0 : ℕ → ℝ) ∈ Knaster := by
  intro n
  simp [tent]

theorem knaster_nonempty : Knaster.Nonempty := ⟨0, zero_mem_knaster⟩

theorem knaster_nontrivial : ∃ x ∈ Knaster, ∃ y ∈ Knaster, x ≠ y := by
  obtain ⟨y, hy, hy0⟩ := exists_knaster_coord 0 (t := 1) ⟨by norm_num, le_rfl⟩
  refine ⟨0, zero_mem_knaster, y, hy, fun h => ?_⟩
  have := congrFun h 0
  rw [hy0] at this
  simp at this

/-! ### Connectedness -/

/-- In a compact Hausdorff space, the intersection of a decreasing sequence of closed connected
sets is connected. -/
theorem isPreconnected_iInter_of_antitone {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {C : ℕ → Set X} (hC : Antitone C) (hcl : ∀ n, IsClosed (C n))
    (hconn : ∀ n, IsPreconnected (C n)) : IsPreconnected (⋂ n, C n) := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_iInter hcl)]
  intro u v hu hv huv hd
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := normal_separation hu hv hd
  -- some `C n` lies in `U ∪ V`
  have key : ∃ n, C n ⊆ U ∪ V := by
    by_contra hcon
    push Not at hcon
    have hne : ∀ n, (C n \ (U ∪ V)).Nonempty := fun n => by
      obtain ⟨x, hxC, hxUV⟩ := not_subset.1 (hcon n)
      exact ⟨x, hxC, hxUV⟩
    have hcomp : ∀ n, IsCompact (C n \ (U ∪ V)) :=
      fun n => ((hcl n).sdiff (hU.union hV)).isCompact
    have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => C n \ (U ∪ V)) (fun n => sdiff_subset_sdiff_left (hC (Nat.le_succ n))) hne
      (hcomp 0) (fun n => (hcl n).sdiff (hU.union hV))
    obtain ⟨x, hx⟩ := this
    rw [mem_iInter] at hx
    have hxC : x ∈ ⋂ n, C n := mem_iInter.2 fun n => (hx n).1
    exact (hx 0).2 (huv hxC |>.elim (fun h => Or.inl (huU h)) (fun h => Or.inr (hvV h)))
  obtain ⟨n, hn⟩ := key
  rcases isPreconnected_iff_subset_of_disjoint.1 (hconn n) U V hU hV hn
      (by rw [hUV.inter_eq, inter_empty]) with h | h
  · left
    intro x hx
    rcases huv hx with h' | h'
    · exact h'
    · exact absurd (hvV h') (disjoint_left.1 hUV (h (mem_iInter.1 hx n)))
  · right
    intro x hx
    rcases huv hx with h' | h'
    · exact absurd (h (mem_iInter.1 hx n)) (disjoint_left.1 hUV (huU h'))
    · exact h'

/-- The `N`-th approximation of `K`: only the first `N` bonding relations are imposed. -/
def knasterApprox (N : ℕ) : Set (ℕ → ℝ) :=
  {x | (∀ n, x n ∈ Icc (0 : ℝ) 1) ∧ ∀ n < N, x n = tent (x (n + 1))}

theorem knasterApprox_eq_image (N : ℕ) :
    knasterApprox N = (fun y : ℕ → ℝ => fun n => if n ≤ N then tent^[N - n] (y N) else y n) ''
      (Set.pi univ fun _ => Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    refine ⟨x, fun n _ => hx n, funext fun n => ?_⟩
    dsimp only
    split_ifs with hn
    · exact (coord_of_bond hxb (N - n) n (by omega)).symm
    · rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun n => ?_, fun n hn => ?_⟩
    · dsimp only
      split_ifs
      · exact tent_iterate_mem _ (hy N (mem_univ _))
      · exact hy n (mem_univ _)
    · simp only [show n ≤ N by omega, ite_true]
      by_cases h : n + 1 ≤ N
      · simp only [h, ite_true]
        rw [show N - n = (N - (n + 1)) + 1 by omega, Function.iterate_succ_apply']
      · omega

theorem isConnected_knasterApprox (N : ℕ) : IsPreconnected (knasterApprox N) := by
  rw [knasterApprox_eq_image]
  refine (isPreconnected_univ_pi fun _ => isPreconnected_Icc).image _ ?_
  refine Continuous.continuousOn (continuous_pi fun n => ?_)
  split_ifs
  · exact (continuous_tent_iterate _).comp (continuous_apply N)
  · exact continuous_apply n

theorem isClosed_knasterApprox (N : ℕ) : IsClosed (knasterApprox N) := by
  have : knasterApprox N = (⋂ n, {x : ℕ → ℝ | x n ∈ Icc (0 : ℝ) 1}) ∩
      ⋂ n, ⋂ (_ : n < N), {x | x n = tent (x (n + 1))} := by
    ext x; simp [knasterApprox]
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun n => isClosed_Icc.preimage (continuous_apply n))
    (isClosed_iInter fun n => isClosed_iInter fun _ => ?_)
  exact isClosed_eq (continuous_apply n) (continuous_tent.comp (continuous_apply (n + 1)))

theorem knaster_eq_iInter : Knaster = ⋂ N, knasterApprox N := by
  ext x
  simp only [Knaster, knasterApprox, mem_iInter, mem_ofPred_eq]
  constructor
  · intro hx N
    exact ⟨fun n => (hx n).1, fun n _ => (hx n).2⟩
  · intro hx n
    exact ⟨(hx 0).1 n, (hx (n + 1)).2 n (by omega)⟩

theorem isConnected_knaster : IsConnected Knaster := by
  refine ⟨knaster_nonempty, ?_⟩
  -- work inside the compact space `[0,1]^ℕ`
  let Q : Set (ℕ → ℝ) := Set.pi univ fun _ => Icc (0 : ℝ) 1
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have : CompactSpace Q := isCompact_iff_compactSpace.1 hQ
  have hsub : ∀ N, knasterApprox N ⊆ Q := fun N x hx n _ => hx.1 n
  let C : ℕ → Set Q := fun N => (↑) ⁻¹' knasterApprox N
  have hC : Antitone C := by
    intro a b hab x hx
    exact ⟨hx.1, fun n hn => hx.2 n (by omega)⟩
  have hcl : ∀ N, IsClosed (C N) := fun N =>
    (isClosed_knasterApprox N).preimage continuous_subtype_val
  have hconn : ∀ N, IsPreconnected (C N) := by
    intro N
    have := (isConnected_knasterApprox N)
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    rwa [Subtype.image_preimage_coe, inter_eq_right.2 (hsub N)]
  have hI := isPreconnected_iInter_of_antitone hC hcl hconn
  have := hI.image ((↑) : Q → ℕ → ℝ) continuous_subtype_val.continuousOn
  rwa [← preimage_iInter, Subtype.image_preimage_coe, ← knaster_eq_iInter,
    inter_eq_right.2 knaster_subset_pi] at this

/-! ### Neighbourhoods in `K` -/

/-- Every neighbourhood of `z ∈ K` contains, for all large `n`, a set of the form
`{y ∈ K | |y n - z n| < δ}`. -/
theorem knaster_nhds {z : ℕ → ℝ} (hz : z ∈ Knaster) {U : Set (ℕ → ℝ)} (hU : IsOpen U)
    (hzU : z ∈ U) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ δ > 0, ∀ y ∈ Knaster, |y n - z n| < δ → y ∈ U := by
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU z hzU
  have hball : ∀ i ∈ I, ∃ ε > 0, Metric.ball (z i) ε ⊆ u i := fun i hi =>
    Metric.isOpen_iff.1 (hu i hi).1 _ (hu i hi).2
  choose! ε hε hεu using hball
  obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ > 0, ∀ i ∈ I, ε₀ ≤ ε i := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨i₀, hi₀, hmin⟩ := I.exists_min_image ε h
      exact ⟨ε i₀, hε i₀ hi₀, hmin⟩
  refine ⟨I.sup id, fun n hn => ⟨ε₀ / 2 ^ n, by positivity, fun y hy hyz => hIU ?_⟩⟩
  intro i hi
  apply hεu i hi
  rw [Metric.mem_ball, Real.dist_eq]
  have hin : i ≤ n := (Finset.le_sup (f := id) hi).trans hn
  rw [knaster_coord_of_le hy hin, knaster_coord_of_le hz hin]
  calc |tent^[n - i] (y n) - tent^[n - i] (z n)| ≤ 2 ^ (n - i) * |y n - z n| :=
        abs_tent_iterate_sub_le _ _ _
    _ ≤ 2 ^ n * |y n - z n| := by
        gcongr
        · norm_num
        · omega
    _ < 2 ^ n * (ε₀ / 2 ^ n) := by gcongr
    _ = ε₀ := by field_simp
    _ ≤ ε i := hε₀le i hi

/-- The Knaster continuum as a topological space. -/
abbrev KnasterSpace : Type := ↥Knaster

instance : CompactSpace KnasterSpace := isCompact_iff_compactSpace.1 isCompact_knaster

instance : ConnectedSpace KnasterSpace := isConnected_iff_connectedSpace.1 isConnected_knaster

/-- A subset of `K` all of whose coordinate projections from some index on are onto `[0,1]` is
dense. -/
theorem dense_of_coord_surj {A : Set KnasterSpace} {m : ℕ}
    (h : ∀ n, m ≤ n → ∀ t ∈ Icc (0 : ℝ) 1, ∃ a ∈ A, (a : ℕ → ℝ) n = t) : Dense A := by
  rw [dense_iff_inter_open]
  intro W hW ⟨w, hw⟩
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hW
  obtain ⟨n₀, hn₀⟩ := knaster_nhds w.2 hO hw
  obtain ⟨δ, hδ, hδO⟩ := hn₀ (max n₀ m) (le_max_left _ _)
  obtain ⟨a, haA, ha⟩ := h (max n₀ m) (le_max_right _ _) _ (w.2 _).1
  refine ⟨a, ?_, haA⟩
  apply hδO a a.2
  rw [ha, sub_self, abs_zero]
  exact hδ

/-- **Fact 2.4(a) for `K`.** A closed connected subset of `K` with nonempty interior is all
of `K`. Equivalently, every proper subcontinuum of `K` has empty interior. -/
theorem eq_univ_of_interior_nonempty {A : Set KnasterSpace} (hA : IsClosed A)
    (hconn : IsPreconnected A) (hint : (interior A).Nonempty) : A = univ := by
  obtain ⟨x, hx⟩ := hint
  obtain ⟨O, hO, hOA⟩ := isOpen_induced_iff.1 (isOpen_interior (s := A))
  have hxO : (x : ℕ → ℝ) ∈ O := by
    have : x ∈ (↑) ⁻¹' O := by rw [hOA]; exact hx
    exact this
  obtain ⟨m, hm⟩ := knaster_nhds x.2 hO hxO
  obtain ⟨δ, hδ, hδO⟩ := hm m le_rfl
  have hS : ∀ y : KnasterSpace, |(y : ℕ → ℝ) m - (x : ℕ → ℝ) m| < δ → y ∈ A := by
    intro y hy
    have : y ∈ (↑) ⁻¹' O := hδO y y.2 hy
    rw [hOA] at this
    exact interior_subset this
  -- an interior value `u ∈ (0,1)` of the `m`-th coordinate near `x m`
  set c := min (δ / 2) (1 / 4) with hc
  have hc0 : 0 < c := lt_min (by linarith) (by norm_num)
  have hcδ : c < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hc4 : c ≤ 1 / 4 := min_le_right _ _
  have hxm := (x.2 m).1
  obtain ⟨u, hu0, hu1, hux⟩ : ∃ u : ℝ, 0 < u ∧ u < 1 ∧ |u - (x : ℕ → ℝ) m| < δ := by
    by_cases hle : (x : ℕ → ℝ) m ≤ 1 / 2
    · refine ⟨(x : ℕ → ℝ) m + c, by linarith [hxm.1], by linarith, ?_⟩
      rw [show (x : ℕ → ℝ) m + c - (x : ℕ → ℝ) m = c by ring, abs_of_pos hc0]
      exact hcδ
    · push Not at hle
      refine ⟨(x : ℕ → ℝ) m - c, by linarith, by linarith [hxm.2], ?_⟩
      rw [show (x : ℕ → ℝ) m - c - (x : ℕ → ℝ) m = -c by ring, abs_neg, abs_of_pos hc0]
      exact hcδ
  -- the projections of `A` are intervals containing `u / 2^j` and `1 - u / 2^j`
  have hproj : ∀ j, 1 ≤ j → Icc (u / 2 ^ j) (1 - u / 2 ^ j) ⊆
      (fun y : KnasterSpace => (y : ℕ → ℝ) (m + j)) '' A := by
    intro j hj
    have hconnP : IsPreconnected ((fun y : KnasterSpace => (y : ℕ → ℝ) (m + j)) '' A) :=
      hconn.image _ ((continuous_apply (m + j)).comp continuous_subtype_val).continuousOn
    have hpos : (0 : ℝ) < 2 ^ j := by positivity
    have hsmall : u / 2 ^ j ≤ 1 / 2 ^ j := by gcongr
    have hle1 : u / 2 ^ j ≤ 1 := hsmall.trans (by rw [div_le_one hpos]; exact one_le_pow₀ (by norm_num))
    have hnn : 0 ≤ u / 2 ^ j := by positivity
    have hval : tent^[j] (u / 2 ^ j) = u := by
      rw [tent_iterate_small j hnn hsmall]
      field_simp
    have hmem : ∀ v ∈ ({u / 2 ^ j, 1 - u / 2 ^ j} : Set ℝ),
        v ∈ (fun y : KnasterSpace => (y : ℕ → ℝ) (m + j)) '' A := by
      intro v hv
      have hv01 : v ∈ Icc (0 : ℝ) 1 := by
        rcases hv with rfl | rfl
        · exact ⟨hnn, hle1⟩
        · exact ⟨by linarith, by linarith⟩
      obtain ⟨y, hy, hyv⟩ := exists_knaster_coord (m + j) hv01
      refine ⟨⟨y, hy⟩, hS _ ?_, hyv⟩
      have hym : y m = u := by
        rw [knaster_coord_of_le hy (by omega : m ≤ m + j), Nat.add_sub_cancel_left, hyv]
        rcases hv with rfl | rfl
        · exact hval
        · rw [tent_iterate_one_sub j hj, hval]
      simp only
      rw [hym]
      exact hux
    exact hconnP.Icc_subset (hmem _ (by simp)) (hmem _ (by simp))
  -- hence every coordinate `n ≥ m` of `A` is onto `[0,1]`
  have hsurj : ∀ n, m ≤ n → ∀ t ∈ Icc (0 : ℝ) 1, ∃ a ∈ A, (a : ℕ → ℝ) n = t := by
    intro n hn t ht
    set j := n - m + 2 with hj
    have hpos : (0 : ℝ) < 2 ^ j := by positivity
    have h4 : (4 : ℝ) ≤ 2 ^ j := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    have hq : u / 2 ^ j ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      nlinarith
    have hs : (2 - t) / 4 ∈ Icc (u / 2 ^ j) (1 - u / 2 ^ j) := by
      obtain ⟨ht0, ht1⟩ := ht
      constructor <;> linarith
    obtain ⟨a, haA, ha⟩ := hproj j (by omega) hs
    refine ⟨a, haA, ?_⟩
    have hN : m + j = n + 2 := by omega
    simp only at ha
    rw [hN] at ha
    rw [knaster_coord_of_le a.2 (by omega : n ≤ n + 2), show n + 2 - n = 2 by omega, ha,
      tent_two_quarter ht]
  have hd := dense_of_coord_surj hsurj
  rw [← hA.closure_eq, hd.closure_eq]

/-- `K` has no isolated points. -/
theorem knaster_not_isOpen_singleton (x : KnasterSpace) : ¬ IsOpen ({x} : Set KnasterSpace) := by
  intro h
  have := eq_univ_of_interior_nonempty isClosed_singleton isPreconnected_singleton
    (by rw [h.interior_eq]; exact singleton_nonempty x)
  obtain ⟨a, ha, b, hb, hab⟩ := knaster_nontrivial
  have h1 : (⟨a, ha⟩ : KnasterSpace) ∈ ({x} : Set KnasterSpace) := by rw [this]; trivial
  have h2 : (⟨b, hb⟩ : KnasterSpace) ∈ ({x} : Set KnasterSpace) := by rw [this]; trivial
  rw [mem_singleton_iff] at h1 h2
  exact hab (congrArg Subtype.val (h1.trans h2.symm))

instance : Nontrivial KnasterSpace := by
  obtain ⟨a, ha, b, hb, hab⟩ := knaster_nontrivial
  exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩⟩

end RegSub
