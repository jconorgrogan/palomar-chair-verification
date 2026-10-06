module

public import SparseMonotiles.KeyNonapexBoundaryPlaneCover

@[expose] public section

/-! A boundary point outside the isolated key has only the aligned carrier/base
plane locally. Negative-height material is constant and cannot be a boundary. -/
namespace SparseMonotiles
open Set Filter
open scoped Topology Classical

theorem key_base_halfspace_local_boundary_plane_cover {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (b : Bool)
    {p : Point (n+1)} {T : Set (Point (n+1))} (hp : p ∈ frontier T)
    (hT : LocalSetEq p T (if b then {x | keyPyramidHalfspaceSlack k (.inl false) (e x) ≤ 0}
      else {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) (e x)})) :
    HasLocalBoundaryPlaneCover T p (n+1) := by
  let H : Set (Point (n+1)) := if b then {x | keyPyramidHalfspaceSlack k (.inl false) (e x) ≤ 0}
      else {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) (e x)}
  have hf : Continuous (fun x => keyPyramidHalfspaceSlack k (.inl false) (e x)) :=
    (continuous_keyPyramidHalfspaceSlack k _).comp e.continuous
  have hz : ∀ x, x ∈ frontier H → keyPyramidHalfspaceSlack k (.inl false) (e x)=0 := by
    intro x hx
    cases b
    · exact (frontier_le_subset_eq continuous_const hf hx).symm
    · exact frontier_le_subset_eq hf continuous_const hx
  have hzp := hz p (hT.frontier.mem_iff.mp hp)
  apply localBoundaryPlaneCover_of_finite_active_fields (ι := Fin 1) p (n+1)
    (fun _ x => keyPyramidHalfspaceSlack k (.inl false) (e x))
    (fun _ => keyWorldInwardNormal k e none) (fun _ => keyWorldInwardNormal_ne_zero k e none)
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · intro a ha x
    exact key_facet_zero_iff_normal_equal k hd e none ha x
  · filter_upwards [hT.frontier] with x hx hfront
    exact ⟨0,hzp,hz x (hx.mp hfront)⟩

theorem key_outside_local_boundary_plane_cover {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (b : Bool)
    {p : Point (n+1)} {T : Set (Point (n+1))}
    (hp : e p ∉ keySolid k) (hboundary : p ∈ frontier T)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) b))) :
    HasLocalBoundaryPlaneCover T p (n+1) := by
  have hnot : ¬ ∀ j, 0 ≤ keyPyramidHalfspaceSlack k j (e p) :=
    fun h => hp ((mem_keySolid_iff_nonneg_slacks k hc hr hh _).mpr h)
  push_neg at hnot
  obtain ⟨j,hj⟩ := hnot
  have hf (j) : Continuous (fun x => keyPyramidHalfspaceSlack k j (e x)) :=
    (continuous_keyPyramidHalfspaceSlack k j).comp e.continuous
  by_cases hb : j = .inl false
  · subst j
    exact (not_mem_frontier_of_localSetEq_merged_base_negative
      (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) b (hf _) hj hT hboundary).elim
  · exact key_base_halfspace_local_boundary_plane_cover k hd e b hboundary
      (hT.trans (localSetEq_closure_merged_of_nonbase_negative
        (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) j b p hb hf hj))

#print axioms key_base_halfspace_local_boundary_plane_cover
#print axioms key_outside_local_boundary_plane_cover
end SparseMonotiles
