module

public import SparseMonotiles.LocalBoundaryPlanes
public import SparseMonotiles.KeyGenuineHalfspaces
public import SparseMonotiles.TwoPlaneWedgeModels

@[expose] public section

/-! A non-apex point of an isolated actual key has at most d active boundary
planes. The complete material Boolean formula, including dent closure, is used;
no transverse genericity or supplied facet-count bound is assumed. -/
namespace SparseMonotiles
open Set Filter
open scoped Topology Classical

theorem mergedKeyRegion_as_signed_truth {X ι : Type*}
    (f : ι → X → ℝ) (base : ι) (b : Bool) :
    mergedKeyRegion f base b = {x |
      (if b then
        (fun v : (ι × Bool) → Prop => v (base,false) ∨ ∀ j, j ≠ base → v (j,true))
       else
        (fun v : (ι × Bool) → Prop => v (base,true) ∧ ¬ ∀ j, j ≠ base → v (j,true)))
      (fun j => 0 ≤ signedFields f j x)} := by
  cases b <;> ext x <;> simp [mergedKeyRegion,nonbaseHalfspaces,signedFields]

theorem eventually_frontier_merged_active {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (f : ι → X → ℝ) (hf : ∀ j, Continuous (f j)) (base : ι) (b : Bool)
    {p : X} {T : Set X} (hT : LocalSetEq p T (closure (mergedKeyRegion f base b))) :
    ∀ᶠ x in 𝓝 p, x ∈ frontier T → ∃ j, f j p=0 ∧ f j x=0 := by
  rw [mergedKeyRegion_as_signed_truth] at hT
  exact hT.eventually_frontier_signed_active f hf _

theorem key_facet_zero_iff_normal_equal {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b) (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (a : PyramidFacetIndex n) {p : Point (n+1)}
    (hp : keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e p)=0)
    (x : Point (n+1)) :
    keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x)=0 ↔
      inner (𝕜 := ℝ) (keyWorldInwardNormal k e a) x =
        inner (𝕜 := ℝ) (keyWorldInwardNormal k e a) p := by
  rw [key_facet_world_slack_difference k hd e a x p,hp,zero_add,inner_sub_right]
  rw [mul_eq_zero]
  simp only [ne_of_gt (keyFacetScale_pos k hd a),false_or,sub_eq_zero]

theorem card_active_key_facet_fields_le {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    {p : Point (n+1)} (hp : p ∈ keySolid k) (hne : p ≠ rationalPoint k.apex) :
    (Finset.univ.filter (fun a : PyramidFacetIndex n =>
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) p=0)).card ≤ n+1 := by
  have heq : Finset.univ.filter (fun a : PyramidFacetIndex n =>
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) p=0) =
      pyramidActiveFacets (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k)
        (keyPyramidHeight k) (pointPyramidEquiv n p) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_pyramidActiveFacets,
      mem_pyramidFacetPlane_iff]
    change keyPyramidHalfspaceBound k (pyramidFacetHalfspaceIndex a) -
      keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex a) p=0 ↔
      keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex a) p =
        keyPyramidHalfspaceBound k (pyramidFacetHalfspaceIndex a)
    exact sub_eq_zero.trans eq_comm
  rw [heq]
  exact card_pyramidActiveFacets_le_of_height_lt _ _ _ hw
    (key_height_lt_of_ne_apex k hc hr hh hp hne)

/-- Full generic non-apex bound in arbitrary world coordinates. -/
theorem key_nonapex_local_boundary_plane_cover {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (b : Bool)
    {p : Point (n+1)} {T : Set (Point (n+1))}
    (hp : e p ∈ keySolid k) (hne : e p ≠ rationalPoint k.apex)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) b))) :
    HasLocalBoundaryPlaneCover T p (n+1) := by
  have hall := eventually_frontier_merged_active
    (fun j x => keyPyramidHalfspaceSlack k j (e x))
    (fun j => (continuous_keyPyramidHalfspaceSlack k j).comp e.continuous) (.inl false) b hT
  have hcover : ∀ᶠ x in 𝓝 p, x ∈ frontier T → ∃ a : PyramidFacetIndex n,
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e p)=0 ∧
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x)=0 := by
    filter_upwards [hall] with x hx hfront
    obtain ⟨j,hjp,hjx⟩ := hx hfront
    obtain ⟨a,ha,_⟩ := active_key_halfspace_is_facet k hc hr hh hp hne j hjp
    exact ⟨a,by simpa only [ha] using hjp,by simpa only [ha] using hjx⟩
  exact localBoundaryPlaneCover_of_finite_active_fields p (n+1)
    (fun a x => keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x))
    (keyWorldInwardNormal k e) (keyWorldInwardNormal_ne_zero k e)
    (card_active_key_facet_fields_le k hc hr hh hw hp hne)
    (fun a ha x => key_facet_zero_iff_normal_equal k hd e a ha x) hcover

#print axioms key_nonapex_local_boundary_plane_cover
end SparseMonotiles
