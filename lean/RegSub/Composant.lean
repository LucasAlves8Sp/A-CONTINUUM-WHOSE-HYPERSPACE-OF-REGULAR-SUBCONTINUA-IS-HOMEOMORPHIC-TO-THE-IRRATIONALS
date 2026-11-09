import RegSub.Knaster
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.CountablyGenerated

/-!
# Composants and the template points (Fact 2.4 and Lemma 3.1)

Let `K` be a nondegenerate continuum in which every closed connected set with nonempty interior is
all of `K` (Fact 2.4(a)). Two points are *joinable* if some proper subcontinuum contains both; this
is the relation "lie in the same composant". We prove, by the Baire category theorem, that the
points joinable with a given point form a meagre set. Consequently every nonempty open set contains
points that are not joinable with any of finitely many given points, which is all that the
construction of Lemma 3.1 uses. We also prove the parts of Fact 2.4(d) that are used.

All results are first proved for an abstract space `K` with these properties and then specialized
to the Knaster continuum `KnasterSpace`.
-/

open Set Filter Topology TopologicalSpace

namespace RegSub

section General

variable {K : Type*} [TopologicalSpace K]

/-- `x` and `y` lie in a common proper subcontinuum (the same composant). -/
def Joinable (x y : K) : Prop :=
  ∃ C : Set K, IsClosed C ∧ IsPreconnected C ∧ C ≠ univ ∧ x ∈ C ∧ y ∈ C

theorem Joinable.symm {x y : K} (h : Joinable x y) : Joinable y x := by
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := h
  exact ⟨C, h1, h2, h3, h5, h4⟩

theorem Joinable.refl [T1Space K] [Nontrivial K] (x : K) : Joinable x x := by
  refine ⟨{x}, isClosed_singleton, isPreconnected_singleton, ?_, rfl, rfl⟩
  intro h
  obtain ⟨y, hy⟩ := exists_ne x
  have : y ∈ ({x} : Set K) := by rw [h]; trivial
  exact hy this

theorem ne_of_not_joinable [T1Space K] [Nontrivial K] {x y : K} (h : ¬ Joinable x y) : x ≠ y := by
  rintro rfl
  exact h (Joinable.refl x)

/-- A closed connected set containing two non-joinable points is everything. -/
theorem eq_univ_of_not_joinable {x y : K} (hxy : ¬ Joinable x y) {C : Set K} (hC : IsClosed C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) : C = univ := by
  by_contra hne
  exact hxy ⟨C, hC, hconn, hne, hx, hy⟩

variable [SecondCountableTopology K]

/-- **The composant of a point is meagre.** -/
theorem isMeagre_joinable
    (hP2 : ∀ A : Set K, IsClosed A → IsPreconnected A → (interior A).Nonempty → A = univ)
    (x : K) : IsMeagre {y | Joinable x y} := by
  obtain ⟨b, hbc, hb0, hb⟩ := exists_countable_basis K
  let S : Set K → Set K := fun U => closure (connectedComponentIn Uᶜ x)
  have hsub : {y | Joinable x y} ⊆ ⋃ U ∈ b, S U := by
    rintro y ⟨C, hC, hconn, hne, hxC, hyC⟩
    obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem C).1 hne
    obtain ⟨U, hUb, hzU, hUC⟩ := hb.exists_subset_of_mem_open hz hC.isOpen_compl
    refine mem_biUnion hUb (subset_closure ?_)
    have hCU : C ⊆ Uᶜ := by
      intro w hw hwU
      exact hUC hwU hw
    exact hconn.subset_connectedComponentIn hxC hCU hyC
  refine IsMeagre.mono hsub (isMeagre_biUnion hbc fun U hU => IsNowhereDense.isMeagre ?_)
  rw [isClosed_closure.isNowhereDense_iff]
  by_contra hint
  have huniv := hP2 _ isClosed_closure isPreconnected_connectedComponentIn.closure
    (nonempty_iff_ne_empty.2 hint)
  have hUsub : S U ⊆ Uᶜ := closure_minimal (connectedComponentIn_subset _ _)
    (hb.isOpen hU).isClosed_compl
  obtain ⟨w, hw⟩ := nonempty_iff_ne_empty.2 (fun h => hb0 (h ▸ hU))
  have hwS : w ∈ S U := by
    change w ∈ closure (connectedComponentIn Uᶜ x)
    rw [huniv]
    trivial
  exact hUsub hwS hw

variable [BaireSpace K]

/-- Every nonempty open set contains a point joinable with none of finitely many given points. -/
theorem exists_not_joinable
    (hP2 : ∀ A : Set K, IsClosed A → IsPreconnected A → (interior A).Nonempty → A = univ)
    {V : Set K} (hV : IsOpen V) (hVne : V.Nonempty) (Z : Finset K) :
    ∃ y ∈ V, ∀ z ∈ Z, ¬ Joinable z y := by
  have hm : IsMeagre (⋃ z ∈ (Z : Set K), {y | Joinable z y}) :=
    isMeagre_biUnion Z.countable_toSet fun z _ => isMeagre_joinable hP2 z
  by_contra hcon
  push Not at hcon
  apply not_isMeagre_of_isOpen hV hVne
  refine hm.mono fun y hy => ?_
  obtain ⟨z, hz, hj⟩ := hcon y hy
  exact mem_biUnion hz hj

/-- Choosing a sequence of points in prescribed nonempty open sets, pairwise non-joinable and
non-joinable with a given finite set. -/
theorem exists_seq_not_joinable
    (hP2 : ∀ A : Set K, IsClosed A → IsPreconnected A → (interior A).Nonempty → A = univ)
    (V : ℕ → Set K) (hV : ∀ k, IsOpen (V k)) (hVne : ∀ k, (V k).Nonempty) (Z : Finset K) :
    ∃ a : ℕ → K, (∀ k, a k ∈ V k) ∧ (∀ k, ∀ z ∈ Z, ¬ Joinable z (a k)) ∧
      ∀ i j, i < j → ¬ Joinable (a i) (a j) := by
  classical
  have hpick : ∀ (k : ℕ) (l : List K), ∃ y ∈ V k, ∀ z ∈ Z ∪ l.toFinset, ¬ Joinable z y :=
    fun k l => exists_not_joinable hP2 (hV k) (hVne k) _
  choose pick hpickV hpickJ using hpick
  let L : ℕ → List K := fun k => Nat.rec [] (fun k l => l ++ [pick k l]) k
  have hL : ∀ k, L (k + 1) = L k ++ [pick k (L k)] := fun k => rfl
  let a : ℕ → K := fun k => pick k (L k)
  have hLa : ∀ k, L k = (List.range k).map a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [hL, List.range_succ, List.map_append, ← ih]; rfl
  refine ⟨a, fun k => hpickV k (L k), fun k z hz => hpickJ k (L k) z (Finset.mem_union_left _ hz),
    fun i j hij => ?_⟩
  apply hpickJ j (L j) (a i)
  refine Finset.mem_union_right _ (List.mem_toFinset.2 ?_)
  rw [hLa j]
  exact List.mem_map.2 ⟨i, List.mem_range.2 hij, rfl⟩

omit [SecondCountableTopology K] [BaireSpace K] in
/-- In a Baire space without isolated points, a countable set is meagre. -/
theorem isMeagre_of_countable [T1Space K]
    (hiso : ∀ x : K, ¬ IsOpen ({x} : Set K)) {C : Set K} (hC : C.Countable) : IsMeagre C := by
  have : C = ⋃ x ∈ C, ({x} : Set K) := by simp
  rw [this]
  refine isMeagre_biUnion hC fun x _ => IsNowhereDense.isMeagre ?_
  rw [isClosed_singleton.isNowhereDense_iff]
  by_contra h
  obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 h
  have hyx : y = x := interior_subset hy
  subst hyx
  have : interior ({y} : Set K) = {y} :=
    Subset.antisymm interior_subset (singleton_subset_iff.2 hy)
  exact hiso y (this ▸ isOpen_interior)

omit [SecondCountableTopology K] in
/-- **Fact 2.4(d).** The complement of a countable set is dense. -/
theorem dense_compl_of_countable [T1Space K] (hiso : ∀ x : K, ¬ IsOpen ({x} : Set K))
    {C : Set K} (hC : C.Countable) : Dense Cᶜ :=
  dense_of_mem_residual (isMeagre_of_countable hiso hC)

omit [SecondCountableTopology K] in
/-- **Fact 2.4(d).** A dense set stays dense after removing a countable set. -/
theorem dense_diff_countable [T1Space K] (hiso : ∀ x : K, ¬ IsOpen ({x} : Set K)) {E C : Set K}
    (hE : Dense E) (hC : C.Countable) (hCcl : IsClosed C) : Dense (E \ C) := by
  rw [dense_iff_inter_open] at hE ⊢
  intro U hU hUne
  have h1 : (U \ C).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    obtain ⟨u, hu⟩ := hUne
    obtain ⟨v, hvU, hvC⟩ := dense_iff_inter_open.1 (dense_compl_of_countable hiso hC) U hU ⟨u, hu⟩
    exact hvC (h hvU)
  obtain ⟨y, hyU, hyE⟩ := hE (U \ C) (hU.sdiff hCcl) h1
  exact ⟨y, hyU.1, hyE, hyU.2⟩

omit [SecondCountableTopology K] in
/-- **Fact 2.4(d).** A dense set stays dense after removing finitely many points. -/
theorem dense_diff_finite [T1Space K] (hiso : ∀ x : K, ¬ IsOpen ({x} : Set K)) {E F : Set K}
    (hE : Dense E) (hF : F.Finite) : Dense (E \ F) :=
  dense_diff_countable hiso hE hF.countable hF.isClosed

end General

/-! ### The template points of Lemma 3.1 -/

/-- The data of Lemma 3.1. The paper's indices start at `1`; here they start at `0`. -/
structure Template (K : Type*) [TopologicalSpace K] where
  ρ : K
  rinf : K
  r : ℕ → K
  q : K
  a : ℕ → K
  r_tendsto : Tendsto r atTop (𝓝 rinf)
  ρ_r : ∀ m, ¬ Joinable ρ (r m)
  r_r : ∀ m m', m ≠ m' → ¬ Joinable (r m) (r m')
  q_a : ∀ k, ¬ Joinable q (a k)
  a_a : ∀ k k', k ≠ k' → ¬ Joinable (a k) (a k')
  /-- every tail of `(a k)` is dense -/
  a_dense : ∀ U : Set K, IsOpen U → U.Nonempty → ∀ k₀, ∃ k, k₀ ≤ k ∧ a k ∈ U

section TemplateExistence

variable {K : Type*} [TopologicalSpace K] [SecondCountableTopology K] [BaireSpace K] [T1Space K]
  [Nonempty K]

omit [TopologicalSpace K] [SecondCountableTopology K] [BaireSpace K] [T1Space K] [Nonempty K] in
theorem symm_of_lt {R : K → K → Prop} (hR : ∀ x y, R x y → R y x) {f : ℕ → K}
    (h : ∀ i j, i < j → ¬ R (f i) (f j)) : ∀ i j, i ≠ j → ¬ R (f i) (f j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact h i j hlt
  · exact fun hR' => h j i hlt (hR _ _ hR')

omit [T1Space K] in
/-- **Lemma 3.1.** -/
theorem exists_template
    (hP2 : ∀ A : Set K, IsClosed A → IsPreconnected A → (interior A).Nonempty → A = univ) :
    Nonempty (Template K) := by
  classical
  obtain ⟨ρ⟩ := ‹Nonempty K›
  obtain ⟨rinf, -, -⟩ := exists_not_joinable hP2 isOpen_univ univ_nonempty {ρ}
  -- neighbourhoods of `rinf`
  obtain ⟨u, hu⟩ := (𝓝 rinf).exists_antitone_basis
  have hVo : ∀ m, IsOpen (interior (u m)) := fun _ => isOpen_interior
  have hVne : ∀ m, (interior (u m)).Nonempty :=
    fun m => ⟨rinf, mem_interior_iff_mem_nhds.2 (hu.mem m)⟩
  obtain ⟨r, hrV, hrZ, hrr⟩ := exists_seq_not_joinable hP2 _ hVo hVne {ρ, rinf}
  have hr_tendsto : Tendsto r atTop (𝓝 rinf) :=
    hu.tendsto fun m => interior_subset (hrV m)
  -- a sequence of basic open sets in which every basic set occurs infinitely often
  obtain ⟨b, hbc, hb0, hb⟩ := exists_countable_basis K
  have hbne : b.Nonempty := by
    obtain ⟨U, hUb, -, -⟩ := hb.exists_subset_of_mem_open (mem_univ ρ) isOpen_univ
    exact ⟨U, hUb⟩
  obtain ⟨e, he⟩ := hbc.exists_eq_range hbne
  let V : ℕ → Set K := fun k => e k.unpair.1
  have hVmem : ∀ k, V k ∈ b := fun k => he ▸ mem_range_self _
  have hVo' : ∀ k, IsOpen (V k) := fun k => hb.isOpen (hVmem k)
  have hVne' : ∀ k, (V k).Nonempty := fun k =>
    nonempty_iff_ne_empty.2 fun h => hb0 (h ▸ hVmem k)
  obtain ⟨a, haV, haZ, haa⟩ := exists_seq_not_joinable hP2 V hVo' hVne' {ρ}
  refine ⟨⟨ρ, rinf, r, ρ, a, hr_tendsto, fun m => hrZ m ρ (by simp),
    symm_of_lt (fun _ _ h => h.symm) hrr, fun k => haZ k ρ (by simp),
    symm_of_lt (fun _ _ h => h.symm) haa, ?_⟩⟩
  intro U hU hUne k₀
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨W, hWb, hxW, hWU⟩ := hb.exists_subset_of_mem_open hx hU
  obtain ⟨i, rfl⟩ : ∃ i, e i = W := by rw [he] at hWb; exact hWb
  refine ⟨Nat.pair i k₀, Nat.right_le_pair _ _, hWU ?_⟩
  have := haV (Nat.pair i k₀)
  simp only [V, Nat.unpair_pair] at this
  exact this

end TemplateExistence

/-! ### Specialization to the Knaster continuum -/

instance : SecondCountableTopology KnasterSpace := inferInstance

instance : BaireSpace KnasterSpace := inferInstance

theorem knaster_P2 : ∀ A : Set KnasterSpace, IsClosed A → IsPreconnected A →
    (interior A).Nonempty → A = univ :=
  fun _ hA hc hi => eq_univ_of_interior_nonempty hA hc hi

/-- The template points on the Knaster continuum, fixed once and for all. -/
noncomputable def tmpl : Template KnasterSpace :=
  Classical.choice (exists_template knaster_P2)

end RegSub
