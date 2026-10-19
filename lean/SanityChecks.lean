import RegSub

/-!
# Sanity checks on the translation

Run `lake env lean SanityChecks.lean`. These checks are not used by the main development; they
confirm that the Lean definitions say what the paper says.
-/

open RegSub Piece TopologicalSpace

/-! ### Main statements, as elaborated -/

#check @RegSub.Admissible
#check @RegSub.codeSet
#check @RegSub.isGδ_codeSet
#check @RegSub.instZeroDimensionalSpaceCodeSet
#check @RegSub.isCompact_interior_eq_empty
#check @RegSub.isGδ_polishSpace
#check @RegSub.codeSet_homeomorph_baire
#check @RegSub.theoremA
#print RegSub.AlexandrovUrysohnStatement
#print RegSub.GeometricIdentification
#print RegSub.regularSubcontinua

/-! ### The tree of Section 3.2 -/

-- `S_{∅,1}` is a child of the root and `B_{(1,2)}` is a child of `S_{∅,1}`.
example : (spine [] 1).parent = some (block []) := rfl
example : (block [(1, 2)]).parent = some (spine [] 1) := rfl
example : (block []).parent = none := rfl

/-- Siblings `B_{(1,1)}` and `B_{(1,2)}`: the tree path between them passes through their parent
spine `S_{∅,1}` but not through the root `B_∅`. -/
example : OnPath (block [(1, 1)]) (block [(1, 2)]) (spine [] 1) := by
  refine ⟨Or.inl (.of_parent rfl), ?_⟩
  rintro ⟨c, hc, h1, h2⟩
  -- `c` would be a child of `S_{∅,1}` lying above both blocks, hence equal to both
  have e1 := h1.eq_of_depth_le (by rw [depth_of_parent hc]; simp [depth])
  have e2 := h2.eq_of_depth_le (by rw [depth_of_parent hc]; simp [depth])
  rw [← e1] at e2
  simp at e2

example : ¬ OnPath (block [(1, 1)]) (block [(1, 2)]) (block []) := by
  rintro ⟨-, h⟩
  exact h ⟨spine [] 1, rfl, .of_parent rfl, .of_parent rfl⟩

/-- Endpoints lie on the path between them. -/
theorem onPath_left (P R : Piece) : OnPath P R P := by
  refine ⟨Or.inl (.refl P), ?_⟩
  rintro ⟨c, hc, hPc, -⟩
  have := hPc.depth_le
  rw [depth_of_parent hc] at this
  omega

/-! ### Admissible sets and the code space -/

variable {N : ℕ → Set ℕ}

-- The empty set is not admissible (it contains no block), but the whole tree is.
example : ¬ Admissible N ∅ := fun h => by
  obtain ⟨β, hβ⟩ := h.hasBlock
  exact hβ
example (hN : ∀ j, (N j).Infinite) : Admissible N Set.univ := admissible_univ hN

-- A single block is admissible: it contains no spine, so (c) is vacuous.
example : Admissible N {block []} where
  hasBlock := ⟨[], rfl⟩
  convex := by
    intro P R Q hP hR hQ
    simp only [Set.mem_singleton_iff] at hP hR ⊢
    subst hP hR
    rcases hQ.1 with h | h <;>
      exact (h.eq_of_depth_le (by simp only [depth, List.length_nil]; omega)).symm
  dense := fun β m h => by simp at h

-- The root block together with one of its spines but no child of that spine is not admissible.
example : ¬ Admissible N {block [], spine [] 1} :=
  not_admissible_of_childless (β := []) (m := 1) (by simp) (fun k => by simp [child])

/-! ### The topology on the hyperspace is the Hausdorff-metric topology -/

-- The topology on `NonemptyCompacts X` used in `regularSubcontinua` (the Vietoris topology) is
-- definitionally the topology of the Hausdorff metric instance.
example (X : Type) [MetricSpace X] :
    (NonemptyCompacts.topology : TopologicalSpace (NonemptyCompacts X)) =
      (inferInstance : MetricSpace (NonemptyCompacts X)).toUniformSpace.toTopologicalSpace :=
  rfl

-- The distance on `NonemptyCompacts X` is the Hausdorff distance.
example (X : Type) [MetricSpace X] (A B : NonemptyCompacts X) :
    dist A B = Metric.hausdorffDist (A : Set X) (B : Set X) := rfl
