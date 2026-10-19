import RegSub.CodeSpace
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.GDelta.Basic

/-!
# The code space

We identify a set of pieces with its indicator function, a point of the Cantor cube
`Piece → Bool` (product of discrete two-point spaces). The *code space* `codeSet N` is the set of
codes of admissible sets of pieces; this is the space `𝔇 ⊆ 2^𝒫` of Section 5 of the paper.

Main results (all fully proved):
* `codeSet_nonempty` : the code space is nonempty;
* `isGδ_codeSet` : it is a `G_δ` subset of the Cantor cube (Proposition 5.3);
* `instZeroDimensionalSpaceCodeSet` : it is zero-dimensional;
* `isCompact_interior_eq_empty` : every compact subset of it has empty interior, i.e. no point
  has a compact neighbourhood (Proposition 5.4, transported to the code space).
-/

open Filter Topology Set

namespace RegSub

open Piece

/-! ### Codes -/

/-- The code of a set of pieces, a point of the Cantor cube `Piece → Bool`. -/
noncomputable def toCode (s : Set Piece) : Piece → Bool := by
  classical exact fun P => decide (P ∈ s)

@[simp] theorem toCode_eq_true {s : Set Piece} {P : Piece} : toCode s P = true ↔ P ∈ s := by
  classical
  simp [toCode]

/-- The set of pieces coded by a point of the Cantor cube. -/
def ofCode (F : Piece → Bool) : Set Piece := {P | F P = true}

@[simp] theorem mem_ofCode {F : Piece → Bool} {P : Piece} : P ∈ ofCode F ↔ F P = true := Iff.rfl

@[simp] theorem ofCode_toCode (s : Set Piece) : ofCode (toCode s) = s := by
  ext P
  simp

theorem toCode_congr {s t : Set Piece} {P : Piece} (h : P ∈ s ↔ P ∈ t) :
    toCode s P = toCode t P :=
  Bool.eq_iff_iff.2 (by simpa using h)

theorem toCode_eq_of_iff {s : Set Piece} {F : Piece → Bool} {P : Piece} (h : P ∈ s ↔ F P = true) :
    toCode s P = F P :=
  Bool.eq_iff_iff.2 (by simpa using h)

/-- The code space `𝔇`: codes of admissible sets of pieces. -/
def codeSet (N : ℕ → Set ℕ) : Set (Piece → Bool) := {F | Admissible N (ofCode F)}

theorem toCode_mem_codeSet {N : ℕ → Set ℕ} {s : Set Piece} :
    toCode s ∈ codeSet N ↔ Admissible N s := by
  simp [codeSet]

variable {N : ℕ → Set ℕ}

theorem codeSet_nonempty (hN : ∀ j, (N j).Infinite) : (codeSet N).Nonempty :=
  ⟨toCode univ, toCode_mem_codeSet.2 (admissible_univ hN)⟩

/-! ### The code space is `G_δ` (Proposition 5.3) -/

theorem isOpen_setOf_three (a b c : Piece) (p : Bool → Bool → Bool → Prop) :
    IsOpen {F : Piece → Bool | p (F a) (F b) (F c)} := by
  have hcont : Continuous fun F : Piece → Bool => (F a, F b, F c) := by fun_prop
  exact (isOpen_discrete {x : Bool × Bool × Bool | p x.1 x.2.1 x.2.2}).preimage hcont

theorem isOpen_coord (P : Piece) (b : Bool) : IsOpen {F : Piece → Bool | F P = b} :=
  isOpen_setOf_three P P P (fun x _ _ => x = b)

theorem infinite_setOf_iff {p : ℕ → Prop} : {k | p k}.Infinite ↔ ∀ n, ∃ k, n ≤ k ∧ p k := by
  rw [← Nat.frequently_atTop_iff_infinite, frequently_atTop]

/-- Condition (a) as a set of codes. -/
def condA : Set (Piece → Bool) := ⋃ β : List (ℕ × ℕ), {F | F (block β) = true}

/-- Condition (b), one triple of pieces at a time. -/
def condB (t : Piece × Piece × Piece) : Set (Piece → Bool) :=
  {F | OnPath t.1 t.2.1 t.2.2 → F t.1 = true → F t.2.1 = true → F t.2.2 = true}

/-- Condition (c), one spine, one basic set and one threshold at a time. -/
def condC (N : ℕ → Set ℕ) (q : List (ℕ × ℕ) × ℕ × ℕ × ℕ) : Set (Piece → Bool) :=
  {F | F (spine q.1 q.2.1) = true →
    ∃ k, q.2.2.2 ≤ k ∧ k ∈ N q.2.2.1 ∧ F (child q.1 q.2.1 k) = true}

theorem isOpen_condA : IsOpen condA :=
  isOpen_iUnion fun β => isOpen_coord (block β) true

theorem isOpen_condB (t : Piece × Piece × Piece) : IsOpen (condB t) :=
  isOpen_setOf_three t.1 t.2.1 t.2.2
    (fun x y z => OnPath t.1 t.2.1 t.2.2 → x = true → y = true → z = true)

theorem isOpen_condC (q : List (ℕ × ℕ) × ℕ × ℕ × ℕ) : IsOpen (condC N q) := by
  have : condC N q = {F | F (spine q.1 q.2.1) = false} ∪
      ⋃ (k : ℕ) (_ : q.2.2.2 ≤ k ∧ k ∈ N q.2.2.1), {F | F (child q.1 q.2.1 k) = true} := by
    ext F
    simp only [condC, mem_ofPred_eq, mem_union, mem_iUnion, exists_prop]
    cases F (spine q.1 q.2.1) <;> simp [and_assoc]
  rw [this]
  exact (isOpen_coord _ false).union
    (isOpen_iUnion fun k => isOpen_iUnion fun _ => isOpen_coord _ true)

theorem codeSet_eq (N : ℕ → Set ℕ) :
    codeSet N = condA ∩ (⋂ t, condB t) ∩ ⋂ q, condC N q := by
  ext F
  simp only [codeSet, mem_ofPred_eq, mem_inter_iff, mem_iInter, condA, condB, condC, mem_iUnion,
    Prod.forall]
  constructor
  · intro h
    refine ⟨⟨h.hasBlock, fun P R Q hpath hP hR => h.convex P R Q hP hR hpath⟩, ?_⟩
    intro β m j n hS
    exact infinite_setOf_iff.1 (h.dense β m hS j) n |>.imp fun k hk => ⟨hk.1, hk.2.1, hk.2.2⟩
  · rintro ⟨⟨hA, hB⟩, hC⟩
    refine ⟨hA, fun P R Q hP hR hpath => hB P R Q hpath hP hR, ?_⟩
    intro β m hS j
    exact infinite_setOf_iff.2 fun n => (hC β m j n hS).imp fun k hk => ⟨hk.1, hk.2.1, hk.2.2⟩

theorem isGδ_codeSet (N : ℕ → Set ℕ) : IsGδ (codeSet N) := by
  rw [codeSet_eq]
  exact (isOpen_condA.isGδ.inter (IsGδ.iInter_of_isOpen isOpen_condB)).inter
    (IsGδ.iInter_of_isOpen isOpen_condC)

/-! ### Zero-dimensionality -/

instance : ZeroDimensionalSpace (Piece → Bool) := by
  refine ZeroDimensionalSpace.of_isTopologicalBasis ?_
    (isTopologicalBasis_pi fun _ => isTopologicalBasis_isClopen (X := Bool))
  rintro _ ⟨U, I, hU, rfl⟩
  exact ⟨isClosed_set_pi fun i hi => IsClopen.isClosed (hU i hi),
    isOpen_set_pi I.finite_toSet fun i hi => IsClopen.isOpen (hU i hi)⟩

theorem zeroDimensionalSpace_subtype {X : Type*} [TopologicalSpace X] [ZeroDimensionalSpace X]
    (p : X → Prop) : ZeroDimensionalSpace (Subtype p) := by
  refine ZeroDimensionalSpace.of_isTopologicalBasis ?_
    (isTopologicalBasis_subtype isTopologicalBasis_isClopen p)
  rintro _ ⟨V, hV, rfl⟩
  exact IsClopen.preimage hV continuous_subtype_val

instance instZeroDimensionalSpaceCodeSet (N : ℕ → Set ℕ) : ZeroDimensionalSpace (codeSet N) :=
  zeroDimensionalSpace_subtype _

/-- The Cantor cube `Piece → Bool` is a Polish space (a countable product of finite discrete
spaces). -/
instance instPolishSpaceCube : PolishSpace (Piece → Bool) := by
  have : TopologicalSpace.SeparableSpace (Piece → Bool) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (Piece → Bool) := inferInstance
  infer_instance

/-! ### No compact neighbourhoods (Proposition 5.4) -/

/-- Pointwise eventual agreement gives convergence in the Cantor cube. -/
theorem tendsto_of_eventually_eq {G : ℕ → Piece → Bool} {H : Piece → Bool}
    (h : ∀ P, ∀ᶠ k in atTop, G k P = H P) : Tendsto G atTop (𝓝 H) := by
  rw [tendsto_pi_nhds]
  intro P
  rw [nhds_discrete, tendsto_pure]
  exact h P

/-- Given finitely many pieces and a block `B_β`, some child spine `S_{β,m}` has none of these
pieces below it. -/
theorem exists_spine_avoiding (I : Finset Piece) (β : List (ℕ × ℕ)) :
    ∃ m, ∀ P ∈ I, ¬ IsDesc P (spine β m) := by
  have hfin : {m | ∃ P ∈ I, IsDesc P (spine β m)}.Finite := by
    have : {m | ∃ P ∈ I, IsDesc P (spine β m)} =
        ⋃ P ∈ (I : Set Piece), {m | IsDesc P (spine β m)} := by
      ext m
      simp
    rw [this]
    refine I.finite_toSet.biUnion fun P _ => Set.Subsingleton.finite ?_
    intro x hx y hy
    exact eq_of_isDesc_spine hx hy
  obtain ⟨m, hm⟩ := hfin.exists_notMem
  exact ⟨m, fun P hP hPm => hm ⟨P, hP, hPm⟩⟩

/-- **Code-space form of Proposition 5.4.** Every neighbourhood of a point of the code space
contains a sequence of points of the code space converging, in the Cantor cube, to a point
outside the code space. -/
theorem exists_escape (hN : ∀ j, (N j).Infinite) {U : Set (Piece → Bool)} (hU : IsOpen U)
    {F : Piece → Bool} (hFU : F ∈ U) (hF : F ∈ codeSet N) :
    ∃ (G : ℕ → Piece → Bool) (H : Piece → Bool),
      (∀ k, G k ∈ U ∩ codeSet N) ∧ Tendsto G atTop (𝓝 H) ∧ H ∉ codeSet N := by
  obtain ⟨I, u, hIu, hsub⟩ := isOpen_pi_iff.1 hU F hFU
  -- a code agreeing with `F` on the finite set `I` lies in `U`
  have hagree : ∀ G : Piece → Bool, (∀ P ∈ I, G P = F P) → G ∈ U := by
    intro G hG
    apply hsub
    intro P hP
    rw [hG P hP]
    exact (hIu P hP).2
  have hs : Admissible N (ofCode F) := hF
  obtain ⟨β, hb⟩ := hs.hasBlock
  obtain ⟨m, hm⟩ := exists_spine_avoiding I β
  have hI : ∀ P ∈ I, ∀ j, ¬ IsDesc P (child β m j) := fun P hP j h =>
    hm P hP (h.trans (.of_parent (parent_child β m j)))
  by_cases hS : spine β m ∈ ofCode F
  · -- Case 2: delete the subtrees below the first `k` children of `S_{β,m}`.
    refine ⟨fun k => toCode (cutHead (ofCode F) β m k),
      toCode (ofCode F \ {P | ∃ j, IsDesc P (child β m j)}), fun k => ⟨?_, ?_⟩, ?_, ?_⟩
    · refine hagree _ fun P hP => toCode_eq_of_iff ?_
      simp only [cutHead, Set.mem_sdiff, mem_ofPred_eq, mem_ofCode]
      exact ⟨fun h => h.1, fun h => ⟨h, fun ⟨j, _, hj⟩ => hI P hP j hj⟩⟩
    · exact toCode_mem_codeSet.2 (hs.cutHead hb k)
    · refine tendsto_of_eventually_eq fun P => ?_
      by_cases hP : ∃ j, IsDesc P (child β m j)
      · obtain ⟨j, hj⟩ := hP
        refine eventually_atTop.2 ⟨j + 1, fun k hk => toCode_congr ?_⟩
        simp only [cutHead, Set.mem_sdiff, mem_ofPred_eq]
        exact ⟨fun h => (h.2 ⟨j, by omega, hj⟩).elim, fun h => (h.2 ⟨j, hj⟩).elim⟩
      · refine Eventually.of_forall fun k => toCode_congr ?_
        simp only [cutHead, Set.mem_sdiff, mem_ofPred_eq]
        exact ⟨fun h => ⟨h.1, hP⟩, fun h => ⟨h.1, fun ⟨j, _, hj⟩ => hP ⟨j, hj⟩⟩⟩
    · rw [toCode_mem_codeSet]
      exact not_admissible_cutAll hS
  · -- Case 1: add the small spine `S_{β,m}` and a tail of its children.
    refine ⟨fun k => toCode (addTail (ofCode F) β m k), toCode (ofCode F ∪ {spine β m}),
      fun k => ⟨?_, ?_⟩, ?_, ?_⟩
    · refine hagree _ fun P hP => toCode_eq_of_iff ?_
      rw [mem_addTail, ← mem_ofCode]
      refine ⟨fun h => ?_, fun h => Or.inl h⟩
      rcases h with h | rfl | ⟨j, -, rfl⟩
      · exact h
      · exact absurd (IsDesc.refl _) (hm _ hP)
      · exact absurd (IsDesc.refl _) (hI _ hP j)
    · exact toCode_mem_codeSet.2 (hs.addTail hN hb k)
    · refine tendsto_of_eventually_eq fun P => ?_
      by_cases hP : ∃ j, P = child β m j
      · obtain ⟨j, rfl⟩ := hP
        refine eventually_atTop.2 ⟨j + 1, fun k hk => toCode_congr ?_⟩
        rw [mem_addTail, mem_union, mem_singleton_iff]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases h with h | h | ⟨j', hj', h⟩
          · exact Or.inl h
          · exact Or.inr h
          · obtain rfl : j = j' := by cases h; rfl
            omega
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
      · refine Eventually.of_forall fun k => toCode_congr ?_
        rw [mem_addTail, mem_union, mem_singleton_iff]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases h with h | h | ⟨j', -, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact (hP ⟨j', h⟩).elim
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
    · rw [toCode_mem_codeSet]
      exact hs.not_admissible_union_spine hb hS

/-- **No compact neighbourhoods.** Every compact subset of the code space has empty interior. -/
theorem isCompact_interior_eq_empty (hN : ∀ j, (N j).Infinite) (K : Set (codeSet N))
    (hK : IsCompact K) : interior K = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 (isOpen_interior (s := K))
  have hxU : (x : Piece → Bool) ∈ U := by
    have : x ∈ Subtype.val ⁻¹' U := by rw [hUeq]; exact hx
    exact this
  obtain ⟨G, H, hG, hGH, hH⟩ := exists_escape hN hU hxU x.2
  have hKc : IsClosed (Subtype.val '' K) := (hK.image continuous_subtype_val).isClosed
  have hGK : ∀ k, G k ∈ Subtype.val '' K := by
    intro k
    refine ⟨⟨G k, (hG k).2⟩, interior_subset ?_, rfl⟩
    rw [← hUeq]
    exact (hG k).1
  obtain ⟨y, -, rfl⟩ := hKc.mem_of_tendsto hGH (Eventually.of_forall hGK)
  exact hH y.2

end RegSub
