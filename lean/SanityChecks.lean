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

/-! ### The unconditional Theorem A -/

#check @RegSub.theoremA_l2
#check @RegSub.theoremA_unconditional
#check @RegSub.alexandrovUrysohn
#check @RegSub.baire_homeomorph_irr
#check @RegSub.PhiHomeo

-- the abstract statements of `RegSub.TheoremA` are now theorems
example : AlexandrovUrysohnStatement := alexandrovUrysohnStatement
example : GeometricIdentification := geometricIdentification

/-! ### The Knaster continuum (Section 2) -/

example : tent (1 / 4) = 1 / 2 := by norm_num [tent]
example : tent (3 / 4) = 1 / 2 := by norm_num [tent]
example : tent 1 = 0 := by norm_num [tent]
example : (0 : ℕ → ℝ) ∈ Knaster := zero_mem_knaster
#print RegSub.Knaster

/-- The Knaster continuum is indecomposable: it is not the union of two proper subcontinua.
This follows from Fact 2.4(a) (`eq_univ_of_interior_nonempty`) and is recorded here as a check
that the formal Fact 2.4(a) has its intended strength. -/
theorem knaster_indecomposable {A B : Set KnasterSpace} (hA : IsClosed A) (hB : IsClosed B)
    (hAc : IsPreconnected A) (hAB : A ∪ B = Set.univ) : A = Set.univ ∨ B = Set.univ := by
  by_cases h : (interior A).Nonempty
  · exact Or.inl (eq_univ_of_interior_nonempty hA hAc h)
  · right
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hsub : Bᶜ ⊆ interior A := interior_maximal
      (fun x hx => ((Set.eq_univ_iff_forall.mp hAB x).resolve_right hx)) hB.isOpen_compl
    rw [h] at hsub
    exact Set.eq_univ_of_forall fun x => by_contra fun hx => hsub hx

-- Lemma 3.1: the template points, with the properties used in the construction
#print RegSub.Template
#check @RegSub.exists_template

/-! ### The construction (Section 3) -/

-- the tree, with `childOf` as in the paper (0-indexed)
example : childOf root 3 = spine [] 3 := rfl
example : childOf (spine [] 3) 5 = block [(3, 5)] := rfl
example : (childOf (spine [] 3) 5).parent = some (spine [] 3) := parent_childOf _ _
-- scales: `λ(child n of P) = λ(P) / 2^(n+2)`
example (P : Piece) (n : ℕ) : lam (childOf P n) = lam P / 2 ^ (n + 2) := lam_childOf P n
-- the realization: the piece of `P` is `pt P + λ(P) · J_P (ι z - ι o_P)`, passing through `pt P`
#print RegSub.phi
example (P : Piece) : phi P (opt P) = pt P := phi_opt P
#print RegSub.X
example : X.Nontrivial := nontrivial_X

/-! ### Regularity, Theorem 4.6 and Proposition 5.2 -/

#print RegSub.relInt
#print RegSub.Reg
-- the Lean notion of regular subcontinuum of `X` agrees with `Reg` on subsets of `ℓ²`
#check @RegSub.reg_iff
-- the encoded density condition (c) is the paper's density condition
#check @RegSub.dense_iff_infinite
#check @RegSub.pcs_admissible
#check @RegSub.pcs_Psi
#check @RegSub.Psi_pcs
#check @RegSub.hausdorffDist_Psi_le
