import RegSub.Tree

/-!
# Admissible piece sets

This file formalizes the combinatorial side of Theorem 4.6 and Proposition 5.4 of the paper.

A set `s` of pieces is *admissible* (`Admissible N s`) if
* (a) it contains a block;
* (b) it is convex in the tree (`PathConvex`);
* (c) for every spine `S_{β,m} ∈ s` and every `j`, infinitely many children `B_{β⌢(m,k)} ∈ s`
  have `k ∈ N j`.

Here `N j` stands for the set of indices `k` such that the template point `a_k` (the point of the
spine template at which the `k`-th child block is attached) lies in the `j`-th member `V_j` of a
countable base of the template continuum `K`. Since `K` has no isolated points and the `a_k` are
pairwise distinct, the set `{a_k : k ∈ Γ}` is dense in `K` if and only if every `V_j` contains
`a_k` for infinitely many `k ∈ Γ`; so (c) is the density condition of Theorem 4.6(c). (The paper's
indices start at `1`, Lean's at `0`; this is a relabelling of the tree.) All results
below hold for an arbitrary family `N` of infinite subsets of `ℕ`.

The two modification lemmas `Admissible.addTail` and `Admissible.cutHead` are the admissibility
checks in Cases 1 and 2 of the proof of Proposition 5.4.
-/

namespace RegSub

open Piece

/-- The block `B_{β⌢(m,k)}`, the `k`-th child of the spine `S_{β,m}`. -/
abbrev child (β : List (ℕ × ℕ)) (m k : ℕ) : Piece := .block ((m, k) :: β)

/-- Admissible sets of pieces: conditions (a)–(c) of Theorem 4.6. -/
structure Admissible (N : ℕ → Set ℕ) (s : Set Piece) : Prop where
  /-- (a) `s` contains a block. -/
  hasBlock : ∃ β, block β ∈ s
  /-- (b) `s` is convex in the tree. -/
  convex : PathConvex s
  /-- (c) density of included children at every included spine. -/
  dense : ∀ β m, spine β m ∈ s → ∀ j, {k | k ∈ N j ∧ child β m k ∈ s}.Infinite

variable {N : ℕ → Set ℕ}

/-- The set of all pieces is admissible; it is the code of `X` itself. -/
theorem admissible_univ (hN : ∀ j, (N j).Infinite) : Admissible N Set.univ where
  hasBlock := ⟨[], trivial⟩
  convex := fun _ _ _ _ _ _ => trivial
  dense := fun _ _ _ j => by simpa using hN j

theorem Admissible.parentClosed {s : Set Piece} (hs : Admissible N s) : ParentClosed s :=
  (pathConvex_iff_parentClosed s).1 hs.convex

/-- If a block `B_β` belongs to an admissible set but the child spine `S_{β,m}` does not, then no
piece below `S_{β,m}` belongs to the set. -/
theorem Admissible.notMem_of_isDesc_spine {s : Set Piece} (hs : Admissible N s)
    {β : List (ℕ × ℕ)} {m : ℕ} (hb : block β ∈ s) (hS : spine β m ∉ s) {R : Piece}
    (hR : IsDesc R (spine β m)) : R ∉ s := by
  intro hRs
  apply hS
  refine hs.convex R (block β) (spine β m) hRs hb ⟨Or.inl hR, ?_⟩
  rintro ⟨c, hc, -, hbc⟩
  have h1 := hbc.depth_le
  rw [depth_of_parent hc] at h1
  simp only [depth] at h1
  omega

/-- A set containing a spine but none of its children violates condition (c). -/
theorem not_admissible_of_childless {s : Set Piece} {β : List (ℕ × ℕ)} {m : ℕ}
    (hS : spine β m ∈ s) (hc : ∀ k, child β m k ∉ s) : ¬ Admissible N s := by
  intro hs
  apply hs.dense β m hS 0
  convert Set.finite_empty using 1
  ext k
  simp [hc k]

/-! ### Case 1 of Proposition 5.4: adding a small spine and a tail of its children -/

/-- `s ∪ {S_{β,m}} ∪ {B_{β⌢(m,j)} : j ≥ k}`. -/
def addTail (s : Set Piece) (β : List (ℕ × ℕ)) (m k : ℕ) : Set Piece :=
  s ∪ {spine β m} ∪ {P | ∃ j, k ≤ j ∧ P = child β m j}

theorem mem_addTail {s : Set Piece} {β : List (ℕ × ℕ)} {m k : ℕ} {P : Piece} :
    P ∈ addTail s β m k ↔ P ∈ s ∨ P = spine β m ∨ ∃ j, k ≤ j ∧ P = child β m j := by
  simp only [addTail, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, or_assoc]

theorem Admissible.addTail {s : Set Piece} (hs : Admissible N s) (hN : ∀ j, (N j).Infinite)
    {β : List (ℕ × ℕ)} {m : ℕ} (hb : block β ∈ s) (k : ℕ) :
    Admissible N (addTail s β m k) where
  hasBlock := ⟨β, mem_addTail.2 (Or.inl hb)⟩
  convex := by
    rw [pathConvex_iff_parentClosed]
    have hpc := hs.parentClosed
    -- every new piece lies below `B_β`
    have hnew : ∀ R, R ∈ RegSub.addTail s β m k → R ∉ s → IsDesc R (block β) := by
      intro R hR hRs
      rcases mem_addTail.1 hR with hR | rfl | ⟨j, -, rfl⟩
      · exact absurd hR hRs
      · exact .of_parent (parent_spine β m)
      · exact (IsDesc.of_parent (parent_child β m j)).trans (.of_parent (parent_spine β m))
    intro P R Q hP hR hRP hpar
    rcases mem_addTail.1 hP with hPs | rfl | ⟨j, -, rfl⟩
    · by_cases hRs : R ∈ s
      · exact mem_addTail.2 (Or.inl (hpc P R Q hPs hRs hRP hpar))
      · have hRb := hnew R hR hRs
        by_cases hbP : IsDesc (block β) P
        · exact absurd (hRb.trans hbP) hRP
        · exact mem_addTail.2 (Or.inl (hpc P (block β) Q hPs hb hbP hpar))
    · rw [parent_spine, Option.some.injEq] at hpar
      subst hpar
      exact mem_addTail.2 (Or.inl hb)
    · rw [parent_child, Option.some.injEq] at hpar
      subst hpar
      exact mem_addTail.2 (Or.inr (Or.inl rfl))
  dense := by
    intro β' m' hS j
    by_cases hβ : β' = β ∧ m' = m
    · obtain ⟨rfl, rfl⟩ := hβ
      refine ((hN j).sdiff (Set.finite_lt_nat k)).mono ?_
      rintro k' ⟨hk'N, hk'⟩
      exact ⟨hk'N, mem_addTail.2 (Or.inr (Or.inr ⟨k', Nat.not_lt.1 hk', rfl⟩))⟩
    · have hS' : spine β' m' ∈ s := by
        rcases mem_addTail.1 hS with h | h | ⟨j', -, h⟩
        · exact h
        · simp only [spine.injEq] at h
          exact absurd h hβ
        · simp at h
      refine (hs.dense β' m' hS' j).mono ?_
      rintro k' ⟨h1, h2⟩
      exact ⟨h1, mem_addTail.2 (Or.inl h2)⟩

/-- In Case 1 the limit `s ∪ {S_{β,m}}` is not admissible. -/
theorem Admissible.not_admissible_union_spine {s : Set Piece} (hs : Admissible N s)
    {β : List (ℕ × ℕ)} {m : ℕ} (hb : block β ∈ s) (hS : spine β m ∉ s) :
    ¬ Admissible N (s ∪ {spine β m}) := by
  refine not_admissible_of_childless (Or.inr rfl) fun k hk => ?_
  rcases hk with hk | hk
  · exact hs.notMem_of_isDesc_spine hb hS (.of_parent (parent_child β m k)) hk
  · simp at hk

/-! ### Case 2 of Proposition 5.4: deleting the subtrees below the first children of a spine -/

/-- `s` minus every piece lying below one of the children `B_{β⌢(m,j)}`, `j < k`.

In the paper (Proposition 5.4, Case 2) only the subtrees below the *selected* children
`B^{(j)} ∈ s`, `j < k`, are deleted. When `s` is convex and contains `S_{β,m}`, the subtree below an
unselected child contains no member of `s` (its path to `S_{β,m}` passes through that child), so the
two definitions give the same set. -/
def cutHead (s : Set Piece) (β : List (ℕ × ℕ)) (m k : ℕ) : Set Piece :=
  s \ {P | ∃ j, j < k ∧ IsDesc P (child β m j)}

theorem not_isDesc_block_child (β : List (ℕ × ℕ)) (m j : ℕ) :
    ¬ IsDesc (block β) (child β m j) :=
  not_isDesc_of_depth_lt (by simp [depth])

theorem not_isDesc_spine_child (β : List (ℕ × ℕ)) (m j : ℕ) :
    ¬ IsDesc (spine β m) (child β m j) :=
  not_isDesc_of_depth_lt (by simp only [depth, List.length_cons]; omega)

theorem Admissible.cutHead {s : Set Piece} (hs : Admissible N s) {β : List (ℕ × ℕ)} {m : ℕ}
    (hb : block β ∈ s) (k : ℕ) : Admissible N (cutHead s β m k) where
  hasBlock := ⟨β, hb, fun ⟨j, _, hj⟩ => not_isDesc_block_child β m j hj⟩
  convex := by
    rw [pathConvex_iff_parentClosed]
    have hpc := hs.parentClosed
    rintro P R Q ⟨hPs, hPn⟩ ⟨hRs, -⟩ hRP hpar
    refine ⟨hpc P R Q hPs hRs hRP hpar, ?_⟩
    rintro ⟨j, hj, hQj⟩
    exact hPn ⟨j, hj, (IsDesc.of_parent hpar).trans hQj⟩
  dense := by
    rintro β' m' ⟨hS, hSn⟩ i
    by_cases hβ : β' = β ∧ m' = m
    · obtain ⟨rfl, rfl⟩ := hβ
      refine ((hs.dense β' m' hS i).sdiff (Set.finite_lt_nat k)).mono ?_
      rintro k' ⟨⟨hk'N, hk's⟩, hk'⟩
      refine ⟨hk'N, hk's, ?_⟩
      rintro ⟨j, hj, hk'j⟩
      have hkj := eq_of_isDesc_child hk'j
      subst hkj
      exact hk' hj
    · refine (hs.dense β' m' hS i).mono ?_
      rintro k' ⟨hk'N, hk's⟩
      refine ⟨hk'N, hk's, ?_⟩
      rintro ⟨j, hj, hcj⟩
      apply hSn
      refine ⟨j, hj, hcj.parent_isDesc ?_ (parent_child β' m' k')⟩
      intro heq
      simp only [child, block.injEq, List.cons.injEq, Prod.mk.injEq] at heq
      exact hβ ⟨heq.2, heq.1.1⟩

/-- In Case 2 the limit, `s` minus everything strictly below `S_{β,m}`, is not admissible. -/
theorem not_admissible_cutAll {s : Set Piece} {β : List (ℕ × ℕ)} {m : ℕ}
    (hS : spine β m ∈ s) :
    ¬ Admissible N (s \ {P | ∃ j, IsDesc P (child β m j)}) := by
  refine not_admissible_of_childless ⟨hS, fun ⟨j, hj⟩ => not_isDesc_spine_child β m j hj⟩ ?_
  intro k hk
  exact hk.2 ⟨k, .refl _⟩

end RegSub
