module

public import SparseMonotiles.KeyCompanionFeatureMatchingPlanes
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! # Extend actual key support coverage through closed sets
Proper carrier-plane restrictions disappear by affine genericity and closedness.
A connected face in a finite disjoint closed key union belongs to its apex key.
-/
namespace SparseMonotiles
open Set

theorem affine_patch_closed_cover_remove_planes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {κ : Type*} [Countable κ] (P : AffineSubspace ℝ E)
    {O : Set P} (hO : IsOpen O) (K : Set E) (hK : IsClosed K)
    (H : κ → AffineSubspace ℝ E) (hproper : ∀ a, ¬ P ≤ H a)
    (hcover : ∀ x ∈ O, (x : E) ∈ K ∨ ∃ a, (x : E) ∈ H a) :
    Subtype.val '' closure O ⊆ K := by
  have hsub : O ⊆ Subtype.val ⁻¹' K := by
    intro x hx
    by_contra hxK
    have hopen : IsOpen (O ∩ Subtype.val ⁻¹' Kᶜ) :=
      hO.inter (hK.isOpen_compl.preimage continuous_subtype_val)
    obtain ⟨y,hy,hgeneric⟩ := exists_genericRidgePoint_in_open P ⟨x,x.property⟩ H hopen ⟨x,hx,hxK⟩
    rcases hcover y hy.1 with hyK | ⟨a,ha⟩
    · exact hy.2 hyK
    · exact hproper a (hgeneric a ha)
  rintro x ⟨y,hy,rfl⟩
  exact closure_minimal hsub (hK.preimage continuous_subtype_val) hy

theorem preconnected_subset_closed_member_of_finite_disjoint_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {S : Set X} (hS : IsPreconnected S) (K : ι → Set X)
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hcover : S ⊆ ⋃ i, K i) (i₀ : ι) {p : X} (hp : p ∈ S) (hpi : p ∈ K i₀) :
    S ⊆ K i₀ := by
  classical
  let V : Set X := ⋃ j : {j : ι // j ≠ i₀}, K j
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun j => hclosed j)
  have hcov : S ⊆ K i₀ ∪ V := by
    intro x hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hcover hx)
    by_cases heq : j=i₀
    · exact Or.inl (heq ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j,heq⟩,hj⟩)
  have hdis : S ∩ (K i₀ ∩ V)=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨_,hxK,hxV⟩
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxV
    exact Set.disjoint_left.mp (hdisjoint i₀ j (Ne.symm j.property)) hxK hj
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS (K i₀) V (hclosed i₀) hV hcov hdis with h | h
  · exact h
  · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (h hp)
    exact False.elim (Set.disjoint_left.mp (hdisjoint i₀ j (Ne.symm j.property)) hpi hj)

#print axioms affine_patch_closed_cover_remove_planes
#print axioms preconnected_subset_closed_member_of_finite_disjoint_cover
end SparseMonotiles
