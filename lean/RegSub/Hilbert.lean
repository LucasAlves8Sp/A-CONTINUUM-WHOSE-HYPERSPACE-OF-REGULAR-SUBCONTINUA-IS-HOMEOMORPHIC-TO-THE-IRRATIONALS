import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import RegSub.Composant
import RegSub.Tree

/-!
# Hilbert space bookkeeping

The construction takes place in `ℓ² = lp (fun _ : ℕ => ℝ) 2`. Each piece `P` of the tree gets its
own infinite set of coordinates `{blk P n | n ∈ ℕ}` (pairwise disjoint for distinct pieces). The
copy of the template in the piece `P` uses these coordinates: `J P` sends the `n`-th coordinate of
`ℓ²` to the coordinate `blk P n`, and `C P` reads off the coordinates of `P`. (The paper gives each
piece its own two-dimensional plane, since it uses a plane template; we use an infinite-dimensional
block because our template, the inverse limit `K`, is embedded in `ℓ²` by `ι`.)

* `J P` is a linear isometry and `C P` is linear with norm `≤ 1`;
* `C Q (J P v) = v` if `Q = P` and `= 0` otherwise;
* `ι : K → ℓ²`, `ι z = (2^{-(n+1)} z n)ₙ`, is continuous and injective, with `‖ι z‖ ≤ 1` and
  `‖ι z - ι z'‖ ≤ 1`.
-/

open Set Filter Topology Function

namespace RegSub

/-- `ℓ²`. -/
abbrev L2 : Type := lp (fun _ : ℕ => ℝ) 2

theorem two_toReal : (2 : ENNReal).toReal = 2 := by norm_num

theorem two_toReal_pos : 0 < (2 : ENNReal).toReal := by norm_num

theorem L2.norm_sq_eq (v : L2) : ‖v‖ ^ (2 : ℝ) = ∑' n, |v n| ^ (2 : ℝ) := by
  have := lp.norm_rpow_eq_tsum two_toReal_pos v
  rw [two_toReal] at this
  simpa [Real.norm_eq_abs] using this

theorem L2.norm_le_of_tsum_le {v : L2} {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' n, |v n| ^ (2 : ℝ) ≤ C ^ (2 : ℝ)) : ‖v‖ ≤ C := by
  refine lp.norm_le_of_tsum_le two_toReal_pos hC ?_
  rw [two_toReal]
  simpa [Real.norm_eq_abs] using h

theorem L2.summable (v : L2) : Summable fun n => |v n| ^ (2 : ℝ) := by
  have := (lp.memℓp v).summable two_toReal_pos
  rw [two_toReal] at this
  simpa [Real.norm_eq_abs] using this

theorem L2.memℓp_of_summable {f : ℕ → ℝ} (h : Summable fun n => |f n| ^ (2 : ℝ)) :
    Memℓp f 2 := by
  rw [memℓp_gen_iff two_toReal_pos, two_toReal]
  simpa [Real.norm_eq_abs] using h

/-! ### Reindexing along an injection -/

section Reindex

variable (g : ℕ → ℕ) (hg : Injective g)
include hg

theorem memℓp_extend (v : L2) : Memℓp (extend g (v : ℕ → ℝ) 0) 2 := by
  refine L2.memℓp_of_summable ?_
  rw [← hg.summable_iff]
  · have : ((fun n => |extend g (v : ℕ → ℝ) 0 n| ^ (2 : ℝ)) ∘ g) = fun n => |v n| ^ (2 : ℝ) := by
      funext n
      simp [hg.extend_apply]
    rw [this]
    exact L2.summable v
  · intro k hk
    rw [extend_apply' _ _ _ (fun ⟨n, hn⟩ => hk ⟨n, hn⟩)]
    simp

/-- Extension by zero along `g`. -/
noncomputable def extL (v : L2) : L2 := ⟨extend g (v : ℕ → ℝ) 0, memℓp_extend g hg v⟩

theorem extL_apply_self (v : L2) (n : ℕ) : extL g hg v (g n) = v n :=
  hg.extend_apply _ _ n

theorem extL_apply_of_notMem (v : L2) {k : ℕ} (hk : k ∉ range g) : extL g hg v k = 0 := by
  show extend g (v : ℕ → ℝ) 0 k = 0
  rw [extend_apply' _ _ _ (fun ⟨n, hn⟩ => hk ⟨n, hn⟩)]
  rfl

theorem norm_extL (v : L2) : ‖extL g hg v‖ = ‖v‖ := by
  have h1 := L2.norm_sq_eq (extL g hg v)
  have h2 := L2.norm_sq_eq v
  have hsum : ∑' k, |extL g hg v k| ^ (2 : ℝ) = ∑' n, |v n| ^ (2 : ℝ) := by
    rw [← hg.tsum_eq]
    · simp [extL_apply_self]
    · intro k hk
      by_contra hkr
      apply hk
      simp [extL_apply_of_notMem g hg v hkr]
  rw [hsum, ← h2] at h1
  exact (Real.rpow_left_injOn (by norm_num : (2 : ℝ) ≠ 0)).eq_iff (norm_nonneg _)
    (norm_nonneg _) |>.1 h1

theorem extL_add (v w : L2) : extL g hg (v + w) = extL g hg v + extL g hg w := by
  ext k
  by_cases hk : k ∈ range g
  · obtain ⟨n, rfl⟩ := hk
    simp [extL_apply_self]
  · simp [extL_apply_of_notMem g hg _ hk]

theorem extL_smul (c : ℝ) (v : L2) : extL g hg (c • v) = c • extL g hg v := by
  ext k
  by_cases hk : k ∈ range g
  · obtain ⟨n, rfl⟩ := hk
    simp [extL_apply_self]
  · simp [extL_apply_of_notMem g hg _ hk]

/-- Extension by zero as a linear map. -/
noncomputable def extLin : L2 →ₗ[ℝ] L2 where
  toFun := extL g hg
  map_add' := extL_add g hg
  map_smul' := extL_smul g hg

theorem memℓp_comp (v : L2) : Memℓp ((v : ℕ → ℝ) ∘ g) 2 :=
  L2.memℓp_of_summable ((L2.summable v).comp_injective hg)

/-- Restriction along `g`. -/
noncomputable def resL (v : L2) : L2 := ⟨(v : ℕ → ℝ) ∘ g, memℓp_comp g hg v⟩

theorem resL_apply (v : L2) (n : ℕ) : resL g hg v n = v (g n) := rfl

theorem norm_resL_le (v : L2) : ‖resL g hg v‖ ≤ ‖v‖ := by
  refine L2.norm_le_of_tsum_le (norm_nonneg _) ?_
  rw [L2.norm_sq_eq v]
  exact tsum_comp_le_tsum_of_inj (f := fun k => |v k| ^ (2 : ℝ)) (L2.summable v)
    (fun _ => by positivity) hg

/-- Restriction as a linear map. -/
noncomputable def resLin : L2 →ₗ[ℝ] L2 where
  toFun := resL g hg
  map_add' v w := by ext n; simp [resL_apply]
  map_smul' c v := by ext n; simp [resL_apply]

end Reindex

/-! ### The coordinate blocks of the pieces -/

/-- An injection `Piece × ℕ → ℕ`. -/
noncomputable def pairInj : Piece × ℕ → ℕ := (Countable.exists_injective_nat (Piece × ℕ)).choose

theorem pairInj_injective : Injective pairInj :=
  (Countable.exists_injective_nat (Piece × ℕ)).choose_spec

/-- The coordinates of the piece `P`. -/
noncomputable def blk (P : Piece) (n : ℕ) : ℕ := pairInj (P, n)

theorem blk_injective (P : Piece) : Injective (blk P) := fun _ _ h =>
  (Prod.ext_iff.1 (pairInj_injective h)).2

theorem blk_ne {P Q : Piece} (h : Q ≠ P) (n m : ℕ) : blk Q n ≠ blk P m := fun e =>
  h (Prod.ext_iff.1 (pairInj_injective e)).1

/-- `J P` places a vector of `ℓ²` into the coordinate block of `P`. -/
noncomputable def J (P : Piece) : L2 →ₗ[ℝ] L2 := extLin (blk P) (blk_injective P)

/-- `C P` reads off the coordinate block of `P`. -/
noncomputable def C (P : Piece) : L2 →ₗ[ℝ] L2 := resLin (blk P) (blk_injective P)

theorem norm_J (P : Piece) (v : L2) : ‖J P v‖ = ‖v‖ := norm_extL (blk P) (blk_injective P) v

theorem norm_C_le (P : Piece) (v : L2) : ‖C P v‖ ≤ ‖v‖ :=
  norm_resL_le (blk P) (blk_injective P) v

theorem C_J_self (P : Piece) (v : L2) : C P (J P v) = v := by
  ext n
  exact extL_apply_self _ (blk_injective P) v n

theorem C_J_ne {P Q : Piece} (h : Q ≠ P) (v : L2) : C Q (J P v) = 0 := by
  ext n
  show extL (blk P) (blk_injective P) v (blk Q n) = 0
  exact extL_apply_of_notMem _ _ v fun ⟨m, hm⟩ => blk_ne h n m hm.symm

theorem J_injective (P : Piece) : Injective (J P) := fun v w h => by
  have := congrArg (C P) h
  rwa [C_J_self, C_J_self] at this

theorem dist_C_le (P : Piece) (x y : L2) : dist (C P x) (C P y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_C_le P _

theorem dist_J (P : Piece) (x y : L2) : dist (J P x) (J P y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_J]

theorem continuous_C (P : Piece) : Continuous (C P) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    simpa using dist_C_le P x y).continuous

theorem continuous_J (P : Piece) : Continuous (J P) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by simp [dist_J]).continuous

/-! ### The embedding of the template -/

theorem weight_sq_le (n : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |(1 / 2 : ℝ) ^ (n + 1) * t| ^ (2 : ℝ) ≤ (1 / 4) ^ (n + 1) := by
  rw [Real.rpow_two, abs_mul, mul_pow, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2) ^ (n + 1))]
  calc ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 * |t| ^ 2 ≤ ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 * 1 := by
        gcongr
        calc |t| ^ 2 ≤ 1 ^ 2 := by gcongr
          _ = 1 := by norm_num
    _ = (1 / 4) ^ (n + 1) := by rw [mul_one, ← pow_mul, mul_comm, pow_mul]; norm_num

theorem summable_quarter : Summable fun n : ℕ => ((1 : ℝ) / 4) ^ (n + 1) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
    (add_left_injective 1)

theorem tsum_quarter_le : ∑' n : ℕ, ((1 : ℝ) / 4) ^ (n + 1) ≤ 1 := by
  have h : ∑' n : ℕ, ((1 : ℝ) / 4) ^ (n + 1) = 1 / 4 * ∑' n : ℕ, ((1 : ℝ) / 4) ^ n := by
    rw [← tsum_mul_left]
    congr 1
    funext n
    ring
  rw [h, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem memℓp_weight (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) :
    Memℓp (fun n => (1 / 2 : ℝ) ^ (n + 1) * f n) 2 :=
  L2.memℓp_of_summable (Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => weight_sq_le n (hf n)) summable_quarter)

theorem abs_coord_le (z : KnasterSpace) (n : ℕ) : |(z : ℕ → ℝ) n| ≤ 1 := by
  obtain ⟨h0, h1⟩ := (z.2 n).1
  rw [abs_le]
  constructor <;> linarith

/-- The embedding `ι : K → ℓ²`, `ι z = (2^{-(n+1)} z n)ₙ`. -/
noncomputable def ι (z : KnasterSpace) : L2 :=
  ⟨fun n => (1 / 2 : ℝ) ^ (n + 1) * (z : ℕ → ℝ) n, memℓp_weight _ (abs_coord_le z)⟩

theorem ι_apply (z : KnasterSpace) (n : ℕ) : ι z n = (1 / 2 : ℝ) ^ (n + 1) * (z : ℕ → ℝ) n := rfl

theorem norm_le_one_of_weighted {v : L2} {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    (hv : ∀ n, v n = (1 / 2 : ℝ) ^ (n + 1) * f n) : ‖v‖ ≤ 1 := by
  refine L2.norm_le_of_tsum_le zero_le_one ?_
  rw [Real.one_rpow]
  refine le_trans (Summable.tsum_le_tsum (fun n => ?_) ?_ summable_quarter) tsum_quarter_le
  · rw [hv n]
    exact weight_sq_le n (hf n)
  · exact L2.summable v

theorem norm_ι_le (z : KnasterSpace) : ‖ι z‖ ≤ 1 :=
  norm_le_one_of_weighted (abs_coord_le z) fun _ => rfl

theorem norm_ι_sub_le (z z' : KnasterSpace) : ‖ι z - ι z'‖ ≤ 1 := by
  refine norm_le_one_of_weighted (f := fun n => (z : ℕ → ℝ) n - (z' : ℕ → ℝ) n) ?_ ?_
  · intro n
    obtain ⟨h0, h1⟩ := (z.2 n).1
    obtain ⟨h0', h1'⟩ := (z'.2 n).1
    rw [abs_le]
    constructor <;> linarith
  · intro n
    simp only [lp.coeFn_sub, Pi.sub_apply, ι_apply]
    ring

theorem ι_injective : Injective ι := by
  intro z z' h
  apply Subtype.ext
  funext n
  have := congrArg (fun v : L2 => v n) h
  simp only [ι_apply] at this
  exact mul_left_cancel₀ (by positivity) this

theorem continuous_ι : Continuous ι := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε ^ 2 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  set δ := ε / 2 with hδ
  have hev : ∀ᶠ z' : KnasterSpace in 𝓝 z, ∀ n ∈ Finset.range N,
      |(z' : ℕ → ℝ) n - (z : ℕ → ℝ) n| < δ := by
    rw [Filter.eventually_all_finset]
    intro n _
    have hc : Continuous fun z' : KnasterSpace => (z' : ℕ → ℝ) n :=
      (continuous_apply n).comp continuous_subtype_val
    have := Metric.tendsto_nhds.1 (hc.continuousAt (x := z)) δ (by positivity)
    simpa [Real.dist_eq] using this
  filter_upwards [hev] with z' hz'
  rw [dist_eq_norm]
  -- the squared norm is at most `δ² + 2^{-N} < ε²`
  have hterm : ∀ n, |(ι z' - ι z) n| ^ (2 : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1) * (δ ^ 2 + (1 / 2) ^ N) := by
    intro n
    have hd : |(z' : ℕ → ℝ) n - (z : ℕ → ℝ) n| ≤ 1 := by
      obtain ⟨h0, h1⟩ := (z.2 n).1
      obtain ⟨h0', h1'⟩ := (z'.2 n).1
      rw [abs_le]
      constructor <;> linarith
    have heq : (ι z' - ι z) n = (1 / 2 : ℝ) ^ (n + 1) * ((z' : ℕ → ℝ) n - (z : ℕ → ℝ) n) := by
      simp only [lp.coeFn_sub, Pi.sub_apply, ι_apply]
      ring
    rw [heq, Real.rpow_two, abs_mul, mul_pow, abs_of_pos (by positivity :
      (0 : ℝ) < (1 / 2) ^ (n + 1))]
    have hpow : ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 = (1 / 2) ^ (n + 1) * (1 / 2) ^ (n + 1) := by ring
    rw [hpow, mul_assoc]
    gcongr
    have hsq1 : |(z' : ℕ → ℝ) n - (z : ℕ → ℝ) n| ^ 2 ≤ 1 := by
      calc |(z' : ℕ → ℝ) n - (z : ℕ → ℝ) n| ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hd 2
        _ = 1 := by norm_num
    have hδ0 : (0 : ℝ) ≤ δ ^ 2 := sq_nonneg _
    have hN0 : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
    by_cases hn : n < N
    · have := hz' n (Finset.mem_range.2 hn)
      have h1 : |(z' : ℕ → ℝ) n - (z : ℕ → ℝ) n| ^ 2 ≤ δ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) this.le 2
      calc (1 / 2 : ℝ) ^ (n + 1) * |(z' : ℕ → ℝ) n - (z : ℕ → ℝ) n| ^ 2
          ≤ 1 * δ ^ 2 :=
            mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num)) h1 (sq_nonneg _) zero_le_one
        _ ≤ δ ^ 2 + (1 / 2) ^ N := by linarith
    · push Not at hn
      calc (1 / 2 : ℝ) ^ (n + 1) * |(z' : ℕ → ℝ) n - (z : ℕ → ℝ) n| ^ 2
          ≤ (1 / 2) ^ N * 1 :=
            mul_le_mul (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hsq1
              (sq_nonneg _) (by positivity)
        _ ≤ δ ^ 2 + (1 / 2) ^ N := by linarith
  have hsum : ∑' n, |(ι z' - ι z) n| ^ (2 : ℝ) ≤ δ ^ 2 + (1 / 2) ^ N := by
    have hs : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * (δ ^ 2 + (1 / 2) ^ N) :=
      ((summable_geometric_two).comp_injective (add_left_injective 1)).mul_right _
    calc ∑' n, |(ι z' - ι z) n| ^ (2 : ℝ)
        ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (δ ^ 2 + (1 / 2) ^ N) :=
          Summable.tsum_le_tsum hterm (L2.summable _) hs
      _ = δ ^ 2 + (1 / 2) ^ N := by
          rw [tsum_mul_right]
          have : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
            have h1 : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => 1 / 2 * (1 / 2) ^ n := by
              funext n
              ring
            rw [h1, tsum_mul_left, tsum_geometric_two]
            norm_num
          rw [this, one_mul]
  have hlt : δ ^ 2 + (1 / 2) ^ N < ε ^ 2 := by
    rw [hδ]
    nlinarith
  have hsq : ‖ι z' - ι z‖ ^ 2 < ε ^ 2 := by
    have := L2.norm_sq_eq (ι z' - ι z)
    rw [Real.rpow_two] at this
    rw [this]
    exact lt_of_le_of_lt hsum hlt
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

end RegSub
