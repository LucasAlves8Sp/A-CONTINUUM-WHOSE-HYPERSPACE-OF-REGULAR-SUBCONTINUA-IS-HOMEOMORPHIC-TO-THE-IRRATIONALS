import RegSub.Hilbert
import RegSub.CodeSpace

/-!
# The construction (Sections 3.2 and 3.3 of the paper)

* the children of a piece (`childOf`), the root `B_∅`;
* the scales `λ_P` (`lam`), with `λ_{child} ≤ λ_P / 4`;
* the template points of attachment `t_P` (`tpt`) and `o_P` (`opt`), taken from `tmpl`
  (Lemma 3.1);
* the attaching points `p_P` (`pt`) and the parametrizations `φ_P` (`phi`):
  `φ_P(z) = p_P + λ_P J_P(ι z - ι o_P)` with `p_P = φ_{par P}(t_P)`;
* Lemma 3.2 (coordinates) and Lemma 3.3(a),(b).

Indices start at `0` (the paper's start at `1`); accordingly the scale factors are
`2^{-(m+2)}` and `2^{-(k+2)}`, so that every child still has at most a quarter of the scale of
its parent. The root also carries an offset `o_{B_∅} = ρ`; this only translates the root copy
and plays no role (the paper uses `(0,0)`).
-/

open Set Filter Topology Function

namespace RegSub

open Piece

/-! ### Children and the root -/

/-- The root block `B_∅`. -/
def root : Piece := .block []

/-- The `n`-th child of a piece: `S_{β,n}` for `B_β`, and `B_{β⌢(m,n)}` for `S_{β,m}`. -/
def childOf : Piece → ℕ → Piece
  | block β, m => spine β m
  | spine β m, k => block ((m, k) :: β)

@[simp] theorem parent_childOf (P : Piece) (n : ℕ) : (childOf P n).parent = some P := by
  cases P <;> rfl

theorem childOf_injective (P : Piece) : Injective (childOf P) := by
  intro a b h
  cases P <;> simp_all [childOf]

theorem exists_childOf {c P : Piece} (h : c.parent = some P) : ∃ n, c = childOf P n := by
  cases c with
  | block β =>
    cases β with
    | nil => simp [parent] at h
    | cons p β =>
      obtain ⟨m, k⟩ := p
      simp only [parent, Option.some.injEq] at h
      subst h
      exact ⟨k, rfl⟩
  | spine β m =>
    simp only [parent, Option.some.injEq] at h
    subst h
    exact ⟨m, rfl⟩

theorem depth_childOf (P : Piece) (n : ℕ) : (childOf P n).depth = P.depth + 1 :=
  depth_of_parent (parent_childOf P n)

theorem eq_root_or_parent (M : Piece) : M = root ∨ ∃ Q, M.parent = some Q := by
  cases M with
  | block β =>
    cases β with
    | nil => exact Or.inl rfl
    | cons p β => exact Or.inr ⟨_, rfl⟩
  | spine β m => exact Or.inr ⟨_, rfl⟩

@[simp] theorem parent_root : root.parent = none := rfl

theorem isDesc_root_aux : ∀ n, ∀ M : Piece, M.depth = n → IsDesc M root := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hM
    rcases eq_root_or_parent M with rfl | ⟨Q, hQ⟩
    · exact .refl _
    · have hd := depth_of_parent hQ
      exact .step hQ (ih Q.depth (by omega) Q rfl)

theorem isDesc_root (M : Piece) : IsDesc M root := isDesc_root_aux _ M rfl

theorem root_isDesc_iff {M : Piece} : IsDesc root M ↔ M = root := by
  constructor
  · intro h
    exact (h.antisymm (isDesc_root M)).symm
  · rintro rfl
    exact .refl _

theorem depth_root : root.depth = 0 := rfl

/-- A descendant of `P` is `P` or lies below exactly one child of `P`. -/
theorem isDesc_iff_eq_or_child {M P : Piece} :
    IsDesc M P ↔ M = P ∨ ∃ n, IsDesc M (childOf P n) := by
  constructor
  · intro h
    by_cases hMP : M = P
    · exact Or.inl hMP
    · obtain ⟨c, hc, hMc⟩ := h.exists_child hMP
      obtain ⟨n, rfl⟩ := exists_childOf hc
      exact Or.inr ⟨n, hMc⟩
  · rintro (rfl | ⟨n, hn⟩)
    · exact .refl _
    · exact hn.trans (.of_parent (parent_childOf P n))

theorem not_isDesc_child_self (P : Piece) (n : ℕ) : ¬ IsDesc P (childOf P n) :=
  not_isDesc_of_depth_lt (by rw [depth_childOf]; omega)

theorem eq_of_isDesc_childOf {M P : Piece} {n n' : ℕ} (h : IsDesc M (childOf P n))
    (h' : IsDesc M (childOf P n')) : n = n' := by
  have key : childOf P n = childOf P n' := by
    rcases h.total h' with h₁ | h₁
    · exact h₁.eq_of_depth_le (by rw [depth_childOf, depth_childOf])
    · exact (h₁.eq_of_depth_le (by rw [depth_childOf, depth_childOf])).symm
  exact childOf_injective P key

theorem ne_of_isDesc_child {M P : Piece} {n : ℕ} (h : IsDesc M (childOf P n)) : M ≠ P := by
  rintro rfl
  exact not_isDesc_child_self M n h

/-! ### Scales -/

/-- Scales of blocks. -/
noncomputable def lamB : List (ℕ × ℕ) → ℝ
  | [] => 1
  | (m, k) :: β => lamB β / 2 ^ (m + 2) / 2 ^ (k + 2)

/-- The scale `λ_P`. -/
noncomputable def lam : Piece → ℝ
  | block β => lamB β
  | spine β m => lamB β / 2 ^ (m + 2)

theorem lam_childOf (P : Piece) (n : ℕ) : lam (childOf P n) = lam P / 2 ^ (n + 2) := by
  cases P <;> rfl

theorem lamB_pos : ∀ β : List (ℕ × ℕ), 0 < lamB β
  | [] => one_pos
  | (m, k) :: β => by
    simp only [lamB]
    have := lamB_pos β
    positivity

theorem lam_pos (P : Piece) : 0 < lam P := by
  cases P with
  | block β => exact lamB_pos β
  | spine β m =>
    simp only [lam]
    have := lamB_pos β
    positivity

theorem lam_ne_zero (P : Piece) : lam P ≠ 0 := (lam_pos P).ne'

theorem lam_childOf_le (P : Piece) (n : ℕ) : lam (childOf P n) ≤ lam P / 4 := by
  rw [lam_childOf]
  have hP := lam_pos P
  have h4 : (4 : ℝ) ≤ 2 ^ (n + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact div_le_div_of_nonneg_left hP.le (by norm_num) h4

theorem lam_le_of_parent {M Q : Piece} (h : M.parent = some Q) : lam M ≤ lam Q / 4 := by
  obtain ⟨n, rfl⟩ := exists_childOf h
  exact lam_childOf_le Q n

theorem lam_le_of_isDesc {M P : Piece} (h : IsDesc M P) : lam M ≤ lam P := by
  induction h with
  | refl => exact le_rfl
  | @step R Q P hp _ ih =>
    have := lam_le_of_parent hp
    have := lam_pos R
    linarith

theorem lam_root : lam root = 1 := rfl

theorem lam_le_one (P : Piece) : lam P ≤ 1 := lam_le_of_isDesc (isDesc_root P)

/-! ### Template points of attachment -/

/-- The template points (Lemma 3.1). -/
noncomputable abbrev T : Template KnasterSpace := tmpl

/-- `t_P`: the point of the parent's template at which `P` is attached. -/
noncomputable def tpt : Piece → KnasterSpace
  | block [] => T.ρ
  | block ((_, k) :: _) => T.a k
  | spine _ m => T.r m

/-- `o_P`: the point of `P`'s own template that is identified with `t_P`. -/
noncomputable def opt : Piece → KnasterSpace
  | block _ => T.ρ
  | spine _ _ => T.q

theorem tpt_childOf_block (β : List (ℕ × ℕ)) (m : ℕ) : tpt (childOf (block β) m) = T.r m := rfl

theorem tpt_childOf_spine (β : List (ℕ × ℕ)) (m k : ℕ) :
    tpt (childOf (spine β m) k) = T.a k := rfl

/-- Distinct children are attached at non-joinable template points. -/
theorem not_joinable_tpt (P : Piece) {n n' : ℕ} (h : n ≠ n') :
    ¬ Joinable (tpt (childOf P n)) (tpt (childOf P n')) := by
  cases P with
  | block β => exact T.r_r n n' h
  | spine β m => exact T.a_a n n' h

/-- The own attaching point of a non-root piece is not joinable with the attaching points of its
children. -/
theorem not_joinable_opt_tpt {P Q : Piece} (hP : P.parent = some Q) (n : ℕ) :
    ¬ Joinable (opt P) (tpt (childOf P n)) := by
  cases P with
  | block β =>
    cases β with
    | nil => simp [Piece.parent] at hP
    | cons p β => exact T.ρ_r n
  | spine β m => exact T.q_a n

/-! ### The realization -/

/-- Attaching points of blocks. -/
noncomputable def ptB : List (ℕ × ℕ) → L2
  | [] => 0
  | (m, k) :: β =>
    (ptB β + lamB β • J (block β) (ι (T.r m) - ι (opt (block β)))) +
      (lamB β / 2 ^ (m + 2)) • J (spine β m) (ι (T.a k) - ι (opt (spine β m)))

/-- The attaching point `p_P` (`p_{B_∅} = 0`). -/
noncomputable def pt : Piece → L2
  | block β => ptB β
  | spine β m => ptB β + lamB β • J (block β) (ι (T.r m) - ι (opt (block β)))

/-- The parametrization `φ_P(z) = p_P + λ_P J_P(ι z - ι o_P)` of the piece `P`. -/
noncomputable def phi (P : Piece) (z : KnasterSpace) : L2 :=
  pt P + lam P • J P (ι z - ι (opt P))

theorem pt_childOf (P : Piece) (n : ℕ) : pt (childOf P n) = phi P (tpt (childOf P n)) := by
  cases P <;> rfl

theorem pt_of_parent {M Q : Piece} (h : M.parent = some Q) : pt M = phi Q (tpt M) := by
  obtain ⟨n, rfl⟩ := exists_childOf h
  exact pt_childOf Q n

theorem pt_root : pt root = 0 := rfl

theorem phi_opt (P : Piece) : phi P (opt P) = pt P := by
  simp [phi]

theorem phi_sub_pt (P : Piece) (z : KnasterSpace) :
    phi P z - pt P = lam P • J P (ι z - ι (opt P)) := by
  simp [phi]

theorem continuous_phi (P : Piece) : Continuous (phi P) := by
  have h1 : Continuous fun z => ι z - ι (opt P) := continuous_ι.sub continuous_const
  have h2 : Continuous fun z => J P (ι z - ι (opt P)) := (continuous_J P).comp h1
  exact continuous_const.add (h2.const_smul (lam P))

theorem phi_injective (P : Piece) : Injective (phi P) := by
  intro z z' h
  simp only [phi, add_right_inj] at h
  have h1 := smul_right_injective L2 (lam_ne_zero P) h
  have h2 := J_injective P h1
  exact ι_injective (sub_left_injective h2)

theorem isClosedEmbedding_phi (P : Piece) : Topology.IsClosedEmbedding (phi P) :=
  (continuous_phi P).isClosedEmbedding (phi_injective P)

theorem dist_phi (P : Piece) (z z' : KnasterSpace) :
    dist (phi P z) (phi P z') = lam P * ‖ι z - ι z'‖ := by
  rw [dist_eq_norm]
  simp only [phi, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub, sub_sub_sub_cancel_right]
  rw [norm_smul, norm_J, Real.norm_eq_abs, abs_of_pos (lam_pos P)]

theorem dist_phi_le (P : Piece) (z z' : KnasterSpace) : dist (phi P z) (phi P z') ≤ lam P := by
  rw [dist_phi]
  exact (mul_le_of_le_one_right (lam_pos P).le (norm_ι_sub_le z z'))

theorem dist_phi_pt_le (P : Piece) (z : KnasterSpace) : dist (phi P z) (pt P) ≤ lam P := by
  rw [← phi_opt P]
  exact dist_phi_le P z _

/-! ### Lemma 3.2: coordinates -/

theorem C_phi (Q M : Piece) (z : KnasterSpace) :
    C Q (phi M z) = C Q (pt M) + lam M • C Q (J M (ι z - ι (opt M))) := by
  simp [phi]

theorem C_J_eq (Q M : Piece) (v : L2) (h : Q ≠ M) : C Q (J M v) = 0 := C_J_ne h v

/-- Coordinates vanish off the root path (Lemma 3.2, second formula). -/
theorem C_pt_of_not_isDesc_aux : ∀ n, ∀ M Q : Piece, M.depth = n → ¬ IsDesc M Q →
    C Q (pt M) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M Q hM hMQ
    rcases eq_root_or_parent M with rfl | ⟨Q', hQ'⟩
    · rw [pt_root, map_zero]
    · rw [pt_of_parent hQ', C_phi]
      have hQ'Q : ¬ IsDesc Q' Q := fun h => hMQ (.step hQ' h)
      have hne : Q ≠ Q' := fun h => hQ'Q (h ▸ .refl _)
      rw [ih Q'.depth (by rw [← hM, depth_of_parent hQ']; omega) Q' Q rfl hQ'Q,
        C_J_eq _ _ _ hne, smul_zero, add_zero]

theorem C_pt_of_not_isDesc {M Q : Piece} (h : ¬ IsDesc M Q) : C Q (pt M) = 0 :=
  C_pt_of_not_isDesc_aux _ M Q rfl h

theorem C_phi_of_not_isDesc {M Q : Piece} (h : ¬ IsDesc M Q) (z : KnasterSpace) :
    C Q (phi M z) = 0 := by
  have hne : Q ≠ M := fun e => h (e ▸ .refl _)
  rw [C_phi, C_pt_of_not_isDesc h, C_J_eq _ _ _ hne, smul_zero, add_zero]

/-- The coordinate of a point of `P` in its own plane (Lemma 3.2, `i = n`). -/
theorem C_phi_self (P : Piece) (z : KnasterSpace) :
    C P (phi P z) = lam P • (ι z - ι (opt P)) := by
  rw [C_phi, C_J_self]
  rcases eq_root_or_parent P with rfl | ⟨Q, hQ⟩
  · rw [pt_root, map_zero, zero_add]
  · rw [pt_of_parent hQ, C_phi_of_not_isDesc, zero_add]
    exact not_isDesc_of_depth_lt (by rw [depth_of_parent hQ]; omega)

/-- The coordinate of a point below the child `c` of `Q` in the plane of `Q` (Lemma 3.2, `i < n`;
this is also Lemma 3.3(d) before taking closures). -/
theorem C_phi_of_isDesc_child {Q c M : Piece} (hc : c.parent = some Q) (hM : IsDesc M c)
    (z : KnasterSpace) : C Q (phi M z) = lam Q • (ι (tpt c) - ι (opt Q)) := by
  induction hM generalizing z with
  | refl c' =>
    have hne : Q ≠ c' := fun e => by
      subst e
      have := depth_of_parent hc
      omega
    rw [C_phi, C_J_eq _ _ _ hne, smul_zero, add_zero, pt_of_parent hc, C_phi_self]
  | @step R Rp c' hp hdesc ih =>
    have hne : Q ≠ R := fun e => by
      subst e
      have h1 := hdesc.depth_le
      have h2 := depth_of_parent hp
      have h3 := depth_of_parent hc
      omega
    rw [C_phi, C_J_eq _ _ _ hne, smul_zero, add_zero, pt_of_parent hp, ih hc]

/-! ### Lemma 3.3(b): subtree estimates -/

theorem dist_phi_pt_of_isDesc {M P : Piece} (h : IsDesc M P) (z : KnasterSpace) :
    dist (phi M z) (pt P) ≤ 4 / 3 * lam P - 1 / 3 * lam M := by
  induction h generalizing z with
  | refl P0 =>
    have := dist_phi_pt_le P0 z
    linarith
  | @step R Q P0 hp hdesc ih =>
    have h1 := dist_phi_pt_le R z
    have h2 := ih (tpt R)
    rw [← pt_of_parent hp] at h2
    have h3 := lam_le_of_parent hp
    calc dist (phi R z) (pt P0) ≤ dist (phi R z) (pt R) + dist (pt R) (pt P0) :=
          dist_triangle _ _ _
      _ ≤ 4 / 3 * lam P0 - 1 / 3 * lam R := by linarith

theorem dist_phi_pt_le' {M P : Piece} (h : IsDesc M P) (z : KnasterSpace) :
    dist (phi M z) (pt P) ≤ 4 / 3 * lam P := by
  have := dist_phi_pt_of_isDesc h z
  have := lam_pos M
  linarith

/-! ### Lemma 3.3(a): finiteness of `𝒫_N` -/

theorem lamB_le_one : ∀ β : List (ℕ × ℕ), lamB β ≤ 1
  | [] => le_rfl
  | (m, k) :: β => by
    simp only [lamB]
    have h1 := lamB_le_one β
    have h0 := lamB_pos β
    have hm : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
    have hk : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
    calc lamB β / 2 ^ (m + 2) / 2 ^ (k + 2) ≤ lamB β / 1 / 1 := by gcongr
      _ ≤ 1 := by simpa using h1

theorem two_pow_le_of_half_pow_le {a b : ℕ} (h : (1 / 2 : ℝ) ^ a ≤ 1 / 2 ^ b) : b ≤ a := by
  by_contra hlt
  push Not at hlt
  have : (1 / 2 : ℝ) ^ a = 1 / 2 ^ a := by rw [one_div_pow]
  rw [this] at h
  have h2 : (2 : ℝ) ^ b ≤ 2 ^ a := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
    linarith
  have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
  omega

theorem finite_lamB_ge : ∀ n : ℕ, {β : List (ℕ × ℕ) | (1 / 2 : ℝ) ^ n ≤ lamB β}.Finite := by
  intro n
  induction n with
  | zero =>
    refine (finite_singleton []).subset ?_
    intro β hβ
    cases β with
    | nil => rfl
    | cons p β =>
      obtain ⟨m, k⟩ := p
      exfalso
      simp only [mem_ofPred_eq, pow_zero, lamB] at hβ
      have h0 := lamB_pos β
      have h1 := lamB_le_one β
      have hm : (2 : ℝ) ≤ 2 ^ (m + 2) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hk : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
      have : lamB β / 2 ^ (m + 2) / 2 ^ (k + 2) ≤ 1 / 2 / 1 := by gcongr
      linarith
  | succ n ih =>
    have hsub : {β : List (ℕ × ℕ) | (1 / 2 : ℝ) ^ (n + 1) ≤ lamB β} ⊆
        {[]} ∪ ⋃ m ∈ Finset.range (n + 1), ⋃ k ∈ Finset.range (n + 1),
          (fun β => (m, k) :: β) '' {β : List (ℕ × ℕ) | (1 / 2 : ℝ) ^ n ≤ lamB β} := by
      intro β hβ
      cases β with
      | nil => exact Or.inl rfl
      | cons p β =>
        obtain ⟨m, k⟩ := p
        right
        simp only [mem_ofPred_eq, lamB] at hβ
        have h0 := lamB_pos β
        have h1 := lamB_le_one β
        have hpm : (0 : ℝ) < 2 ^ (m + 2) := by positivity
        have hpk : (0 : ℝ) < 2 ^ (k + 2) := by positivity
        have hhalf : (0 : ℝ) < (1 / 2) ^ (n + 1) := by positivity
        -- bounds on `m` and `k`
        have hm : m + 2 ≤ n + 1 := by
          apply two_pow_le_of_half_pow_le
          calc (1 / 2 : ℝ) ^ (n + 1) ≤ lamB β / 2 ^ (m + 2) / 2 ^ (k + 2) := hβ
            _ ≤ 1 / 2 ^ (m + 2) / 1 := by gcongr; exact one_le_pow₀ (by norm_num)
            _ = 1 / 2 ^ (m + 2) := by ring
        have hk : k + 2 ≤ n + 1 := by
          apply two_pow_le_of_half_pow_le
          calc (1 / 2 : ℝ) ^ (n + 1) ≤ lamB β / 2 ^ (m + 2) / 2 ^ (k + 2) := hβ
            _ ≤ 1 / 1 / 2 ^ (k + 2) := by gcongr; exact one_le_pow₀ (by norm_num)
            _ = 1 / 2 ^ (k + 2) := by ring
        refine mem_biUnion (x := m) (Finset.mem_coe.2 (Finset.mem_range.2 (by omega))) ?_
        refine mem_biUnion (x := k) (Finset.mem_coe.2 (Finset.mem_range.2 (by omega))) ?_
        refine ⟨β, ?_, rfl⟩
        simp only [mem_ofPred_eq]
        have hprod : (1 / 2 : ℝ) ^ (n + 1) * (2 ^ (m + 2) * 2 ^ (k + 2)) ≤ lamB β := by
          rw [div_div, le_div_iff₀ (by positivity)] at hβ
          exact hβ
        have h16 : (2 : ℝ) ≤ 2 ^ (m + 2) * 2 ^ (k + 2) := by
          have : (2 : ℝ) ≤ 2 ^ (m + 2) := by
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k + 2)]
        calc (1 / 2 : ℝ) ^ n = (1 / 2) ^ (n + 1) * 2 := by rw [pow_succ]; ring
          _ ≤ (1 / 2) ^ (n + 1) * (2 ^ (m + 2) * 2 ^ (k + 2)) := by gcongr
          _ ≤ lamB β := hprod
    refine (Finite.union (finite_singleton _) ?_).subset hsub
    refine Finite.biUnion (Finset.finite_toSet _) fun m _ => ?_
    exact Finite.biUnion (Finset.finite_toSet _) fun k _ => ih.image _

/-- **Lemma 3.3(a).** Only finitely many pieces have scale at least `2^{-N}`. -/
theorem finite_lam_ge (N : ℕ) : {P : Piece | (1 / 2 : ℝ) ^ N ≤ lam P}.Finite := by
  have hB := finite_lamB_ge N
  have hsub : {P : Piece | (1 / 2 : ℝ) ^ N ≤ lam P} ⊆
      (block '' {β | (1 / 2 : ℝ) ^ N ≤ lamB β}) ∪
        ⋃ m ∈ Finset.range (N + 1), (fun β => spine β m) '' {β | (1 / 2 : ℝ) ^ N ≤ lamB β} := by
    intro P hP
    cases P with
    | block β => exact Or.inl ⟨β, hP, rfl⟩
    | spine β m =>
      right
      simp only [mem_ofPred_eq, lam] at hP
      have h0 := lamB_pos β
      have h1 := lamB_le_one β
      have hpm : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
      have hm : m + 2 ≤ N := by
        apply two_pow_le_of_half_pow_le
        calc (1 / 2 : ℝ) ^ N ≤ lamB β / 2 ^ (m + 2) := hP
          _ ≤ 1 / 2 ^ (m + 2) := by gcongr
      refine mem_biUnion (x := m) (Finset.mem_coe.2 (Finset.mem_range.2 (by omega))) ⟨β, ?_, rfl⟩
      simp only [mem_ofPred_eq]
      calc (1 / 2 : ℝ) ^ N ≤ lamB β / 2 ^ (m + 2) := hP
        _ ≤ lamB β / 1 := by gcongr
        _ = lamB β := by ring
  refine (Finite.union (hB.image _) ?_).subset hsub
  exact Finite.biUnion (Finset.finite_toSet _) fun m _ => hB.image _

/-- The first piece outside `𝒫_N` on the root path of a piece outside `𝒫_N`. -/
theorem exists_first_out (N : ℕ) : ∀ n, ∀ M : Piece, M.depth = n → lam M < (1 / 2 : ℝ) ^ N →
    ∃ P Q, IsDesc M P ∧ lam P < (1 / 2 : ℝ) ^ N ∧ P.parent = some Q ∧
      (1 / 2 : ℝ) ^ N ≤ lam Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hM hlt
    rcases eq_root_or_parent M with rfl | ⟨Q, hQ⟩
    · exfalso
      rw [lam_root] at hlt
      have : (1 / 2 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    · by_cases hQN : (1 / 2 : ℝ) ^ N ≤ lam Q
      · exact ⟨M, Q, .refl _, hlt, hQ, hQN⟩
      · push Not at hQN
        obtain ⟨P, Q', h1, h2, h3, h4⟩ := ih Q.depth
          (by rw [← hM, depth_of_parent hQ]; omega) Q rfl hQN
        exact ⟨P, Q', .step hQ h1, h2, h3, h4⟩

end RegSub
