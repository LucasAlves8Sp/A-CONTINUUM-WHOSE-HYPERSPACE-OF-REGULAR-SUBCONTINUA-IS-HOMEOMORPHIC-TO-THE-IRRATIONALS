import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.List

/-!
# The index tree of the construction

This file formalizes the index tree `𝒫` of Section 3.2 of the paper
"A continuum whose hyperspace of regular subcontinua is homeomorphic to the irrationals".

* `Piece.block β` is the block `B_β`, where `β` is a finite sequence of pairs of natural
  numbers. We store `β` with the *most recent* pair first, so the child `B_{β⌢(m,k)}` of the
  spine `S_{β,m}` is `Piece.block ((m, k) :: β)`.
* `Piece.spine β m` is the spine `S_{β,m}`, a child of `B_β`.

We define the parent map, the descendant relation `IsDesc R P` (written `R ⪯ P` in the
paper: `R` is a descendant of `P`, including `R = P`), and the notion of a vertex lying on the
tree path between two vertices. A set of pieces is *convex* (condition (b) of Theorem 4.6) if it
contains every vertex on the tree path between any two of its members. The main result of this
file, `pathConvex_iff_parentClosed`, is a parent-closure reformulation of convexity that is used
in all later proofs.
-/

namespace RegSub

/-- The pieces of the construction: blocks `B_β` and spines `S_{β,m}`. -/
inductive Piece : Type
  | block : List (ℕ × ℕ) → Piece
  | spine : List (ℕ × ℕ) → ℕ → Piece
  deriving DecidableEq

namespace Piece

/-- An injective encoding of pieces into a countable type. -/
def encode : Piece → List (ℕ × ℕ) ⊕ (List (ℕ × ℕ) × ℕ)
  | block β => Sum.inl β
  | spine β m => Sum.inr (β, m)

theorem encode_injective : Function.Injective encode := by
  intro a b h
  cases a <;> cases b <;> simp_all [encode]

instance : Countable Piece := encode_injective.countable

/-- The parent of a piece; the root block `B_∅` has no parent. -/
def parent : Piece → Option Piece
  | block [] => none
  | block ((m, _) :: β) => some (spine β m)
  | spine β _ => some (block β)

/-- The depth of a piece in the tree. -/
def depth : Piece → ℕ
  | block β => 2 * β.length
  | spine β _ => 2 * β.length + 1

theorem depth_of_parent {R Q : Piece} (h : R.parent = some Q) : R.depth = Q.depth + 1 := by
  cases R with
  | block β =>
    cases β with
    | nil => simp [parent] at h
    | cons p β =>
      obtain ⟨m, k⟩ := p
      simp only [parent, Option.some.injEq] at h
      subst h
      simp [depth]
      omega
  | spine β m =>
    simp only [parent, Option.some.injEq] at h
    subst h
    simp [depth]

@[simp] theorem parent_spine (β : List (ℕ × ℕ)) (m : ℕ) :
    (spine β m).parent = some (block β) := rfl

@[simp] theorem parent_child (β : List (ℕ × ℕ)) (m k : ℕ) :
    (block ((m, k) :: β)).parent = some (spine β m) := rfl

end Piece

open Piece

/-- `IsDesc R P` means that `R` is a descendant of `P`, including the case `R = P`.
In the paper this is written `R ⪯ P`. -/
inductive IsDesc : Piece → Piece → Prop
  | refl (P : Piece) : IsDesc P P
  | step {R Q P : Piece} : R.parent = some Q → IsDesc Q P → IsDesc R P

namespace IsDesc

theorem of_parent {R Q : Piece} (h : R.parent = some Q) : IsDesc R Q :=
  .step h (.refl Q)

theorem trans : ∀ {R Q P : Piece}, IsDesc R Q → IsDesc Q P → IsDesc R P
  | _, _, _, .refl _, h => h
  | _, _, _, .step hp h₁, h₂ => .step hp (trans h₁ h₂)

theorem depth_le : ∀ {R P : Piece}, IsDesc R P → P.depth ≤ R.depth
  | _, _, .refl _ => le_rfl
  | _, _, .step hp h => by
    have := depth_le h
    rw [depth_of_parent hp]
    omega

/-- A descendant of the same depth is the piece itself. -/
theorem eq_of_depth_le {R P : Piece} (h : IsDesc R P) (hd : R.depth ≤ P.depth) : R = P := by
  cases h with
  | refl => rfl
  | step hp hq =>
    have := hq.depth_le
    rw [depth_of_parent hp] at hd
    omega

theorem antisymm {R P : Piece} (h₁ : IsDesc R P) (h₂ : IsDesc P R) : R = P :=
  h₁.eq_of_depth_le h₂.depth_le

/-- If `R` is a proper descendant of `P`, then the parent of `R` is a descendant of `P`. -/
theorem parent_isDesc {R P Q : Piece} (h : IsDesc R P) (hne : R ≠ P) (hQ : R.parent = some Q) :
    IsDesc Q P := by
  cases h with
  | refl => exact absurd rfl hne
  | step hp hq =>
    rw [hQ, Option.some.injEq] at hp
    subst hp
    exact hq

/-- A proper descendant of `P` lies below a unique child of `P`; here we only need existence. -/
theorem exists_child : ∀ {R P : Piece}, IsDesc R P → R ≠ P →
    ∃ c, c.parent = some P ∧ IsDesc R c
  | _, _, .refl _, hne => absurd rfl hne
  | R, P, .step (Q := Q) hp hq, _ => by
    by_cases hQP : Q = P
    · subst hQP
      exact ⟨R, hp, .refl R⟩
    · obtain ⟨c, hc, hQc⟩ := exists_child hq hQP
      exact ⟨c, hc, .step hp hQc⟩

/-- The ancestors of a piece are linearly ordered. -/
theorem total : ∀ {R P P' : Piece}, IsDesc R P → IsDesc R P' → IsDesc P P' ∨ IsDesc P' P
  | _, _, _, .refl _, h' => Or.inl h'
  | R, P, P', .step (Q := Q) hp hq, h' => by
    cases h' with
    | refl => exact Or.inr (.step hp hq)
    | step hp' hq' =>
      rw [hp, Option.some.injEq] at hp'
      subst hp'
      exact total hq hq'

end IsDesc

theorem not_isDesc_of_depth_lt {R P : Piece} (h : R.depth < P.depth) : ¬ IsDesc R P :=
  fun hd => absurd hd.depth_le (Nat.not_le.2 h)

/-- A piece lies below at most one of the spines `S_{β,m}`, `m ∈ ℕ`. -/
theorem eq_of_isDesc_spine {P : Piece} {β : List (ℕ × ℕ)} {m m' : ℕ}
    (h : IsDesc P (spine β m)) (h' : IsDesc P (spine β m')) : m = m' := by
  have key : spine β m = spine β m' := by
    rcases h.total h' with h₁ | h₁
    · exact h₁.eq_of_depth_le (by simp [depth])
    · exact (h₁.eq_of_depth_le (by simp [depth])).symm
  simpa using key

/-- Two children of the same spine that are comparable are equal. -/
theorem eq_of_isDesc_child {β : List (ℕ × ℕ)} {m k k' : ℕ}
    (h : IsDesc (block ((m, k) :: β)) (block ((m, k') :: β))) : k = k' := by
  have := h.eq_of_depth_le (by simp [depth])
  simpa using this

/-! ### Tree paths and convexity -/

/-- `OnPath P R Q`: the piece `Q` lies on the tree path between `P` and `R`. Equivalently,
`Q` is an ancestor (or equal) of `P` or of `R`, and `P`, `R` do not both lie below a single
child of `Q`. -/
def OnPath (P R Q : Piece) : Prop :=
  (IsDesc P Q ∨ IsDesc R Q) ∧ ¬ ∃ c, c.parent = some Q ∧ IsDesc P c ∧ IsDesc R c

theorem OnPath.symm {P R Q : Piece} (h : OnPath P R Q) : OnPath R P Q :=
  ⟨h.1.symm, fun ⟨c, hc, h₁, h₂⟩ => h.2 ⟨c, hc, h₂, h₁⟩⟩

/-- Condition (b) of Theorem 4.6: `s` contains the tree path between any two of its members. -/
def PathConvex (s : Set Piece) : Prop :=
  ∀ P R Q, P ∈ s → R ∈ s → OnPath P R Q → Q ∈ s

/-- Parent-closure form of convexity: if `P ∈ s` and some `R ∈ s` is not below `P`, then the
parent of `P` lies in `s`. -/
def ParentClosed (s : Set Piece) : Prop :=
  ∀ P R Q, P ∈ s → R ∈ s → ¬ IsDesc R P → P.parent = some Q → Q ∈ s

theorem ParentClosed.mem_of_isDesc {s : Set Piece} (hs : ParentClosed s) {R Q : Piece}
    (hR : R ∈ s) : ∀ {P : Piece}, IsDesc P Q → P ∈ s →
      (¬ ∃ c, c.parent = some Q ∧ IsDesc P c ∧ IsDesc R c) → Q ∈ s
  | _, .refl _, hP, _ => hP
  | P, .step (Q := Q₁) hp hq, hP, hno => by
    have hQ₁ : Q₁ ∈ s := by
      refine hs P R Q₁ hP hR (fun hRP => hno ?_) hp
      have hPQ : IsDesc P Q := .step hp hq
      have hne : P ≠ Q := by
        intro h
        subst h
        have h1 := hq.depth_le
        rw [depth_of_parent hp] at h1
        omega
      obtain ⟨c, hc, hPc⟩ := hPQ.exists_child hne
      exact ⟨c, hc, hPc, hRP.trans hPc⟩
    refine ParentClosed.mem_of_isDesc hs hR hq hQ₁ ?_
    rintro ⟨c, hc, hQ₁c, hRc⟩
    exact hno ⟨c, hc, (IsDesc.of_parent hp).trans hQ₁c, hRc⟩

theorem pathConvex_iff_parentClosed (s : Set Piece) : PathConvex s ↔ ParentClosed s := by
  constructor
  · intro hs P R Q hP hR hRP hpar
    refine hs P R Q hP hR ⟨Or.inl (.of_parent hpar), ?_⟩
    rintro ⟨c, hc, hPc, hRc⟩
    have hPc' : P = c := hPc.eq_of_depth_le (by rw [depth_of_parent hpar, depth_of_parent hc])
    subst hPc'
    exact hRP hRc
  · intro hs P R Q hP hR hQ
    rcases hQ.1 with hPQ | hRQ
    · exact hs.mem_of_isDesc hR hPQ hP hQ.2
    · exact hs.mem_of_isDesc hP hRQ hR hQ.symm.2

end RegSub
