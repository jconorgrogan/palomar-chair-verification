module

public import SparseMonotiles.CarrierBoundaryPlaneCover
public import SparseMonotiles.KeyApexBoundaryPlaneCover
public import SparseMonotiles.KeyOutsideBoundaryPlaneCover
public import SparseMonotiles.Tile5MergedModels
public import SparseMonotiles.Tile7MergedModels

@[expose] public section

/-! At every actual boundary point, either at most d proper active planes
cover the frontier locally, or the point is the apex of one actual literal
key and its 2(d-1) side planes cover the frontier locally. No generic-ridge
or preselected-feature hypothesis is used. -/
namespace SparseMonotiles
open Set Filter Canonical
open scoped Topology

theorem T5_boundary_local_small_or_key_apex {p : Point 5} (hp : p ∈ frontier T5) :
    HasLocalBoundaryPlaneCover T5 p 5 ∨
      ∃ k ∈ keys5, ∃ q : Contact.Pose 5,
        keySolid k = q.euclidean '' referenceSolid5 ∧
        p = q.euclidean (rationalPoint ((referenceBox5 true).toKeyData 19200).apex) ∧
        (∀ᶠ x in 𝓝 p, x ∈ frontier T5 →
          ∃ i : Fin 4, ∃ b : Bool, posedHalfspaceSlack5 q (.inr (i,b)) x=0) := by
  rcases T5_local_merged_key_inventory p with hcarrier | ⟨k,hk,q,hq,hlocal⟩
  · exact Or.inl (carrier_local_boundary_plane_cover p hcarrier)
  · let k₀ := (referenceBox5 true).toKeyData 19200
    have hc : k₀.centre (Fin.last 4)=0 := by simp [k₀,Fin.last]
    have hr : k₀.radius (Fin.last 4)=0 := by simp [k₀,Fin.last]
    have hh : 0 < keyPyramidHeight k₀ := by
      change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
      exact_mod_cast referenceBox5_height_pos true
    have hw (i : Fin 4) : keyPyramidLo k₀ i < keyPyramidHi k₀ i := by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox5_base_interval_pos true i
    have hd : ∀ i b, 0 < keySideDistance k₀ i b := referenceSideDistance5_pos
    by_cases ha : q.euclidean.symm p = rationalPoint k₀.apex
    · right
      refine ⟨k,hk,q,hq,?_,?_⟩
      · have h := congrArg q.euclidean ha
        simpa only [q.euclidean.apply_symm_apply] using h
      · exact key_apex_eventually_frontier_side_planes k₀ hh 0 (hw 0)
          q.euclidean.symm k.bump ha hlocal
    · left
      by_cases hm : q.euclidean.symm p ∈ keySolid k₀
      · exact key_nonapex_local_boundary_plane_cover k₀ hc hr hh hw hd
          q.euclidean.symm k.bump hm ha hlocal
      · exact key_outside_local_boundary_plane_cover k₀ hc hr hh hd
          q.euclidean.symm k.bump hm hp hlocal

#print axioms T5_boundary_local_small_or_key_apex

theorem T7_boundary_local_small_or_key_apex {p : Point 7} (hp : p ∈ frontier T7) :
    HasLocalBoundaryPlaneCover T7 p 7 ∨
      ∃ k ∈ keys7, ∃ q : Contact.Pose 7,
        keySolid k = q.euclidean '' referenceSolid7 ∧
        p = q.euclidean (rationalPoint ((referenceBox7 true).toKeyData 188160).apex) ∧
        (∀ᶠ x in 𝓝 p, x ∈ frontier T7 →
          ∃ i : Fin 6, ∃ b : Bool, posedHalfspaceSlack7 q (.inr (i,b)) x=0) := by
  rcases T7_local_merged_key_inventory p with hcarrier | ⟨k,hk,q,hq,hlocal⟩
  · exact Or.inl (carrier_local_boundary_plane_cover p hcarrier)
  · let k₀ := (referenceBox7 true).toKeyData 188160
    have hc : k₀.centre (Fin.last 6)=0 := by simp [k₀,Fin.last]
    have hr : k₀.radius (Fin.last 6)=0 := by simp [k₀,Fin.last]
    have hh : 0 < keyPyramidHeight k₀ := by
      change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
      exact_mod_cast referenceBox7_height_pos true
    have hw (i : Fin 6) : keyPyramidLo k₀ i < keyPyramidHi k₀ i := by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox7_base_interval_pos true i
    have hd : ∀ i b, 0 < keySideDistance k₀ i b := referenceSideDistance7_pos
    by_cases ha : q.euclidean.symm p = rationalPoint k₀.apex
    · right
      refine ⟨k,hk,q,hq,?_,?_⟩
      · have h := congrArg q.euclidean ha
        simpa only [q.euclidean.apply_symm_apply] using h
      · exact key_apex_eventually_frontier_side_planes k₀ hh 0 (hw 0)
          q.euclidean.symm k.bump ha hlocal
    · left
      by_cases hm : q.euclidean.symm p ∈ keySolid k₀
      · exact key_nonapex_local_boundary_plane_cover k₀ hc hr hh hw hd
          q.euclidean.symm k.bump hm ha hlocal
      · exact key_outside_local_boundary_plane_cover k₀ hc hr hh hd
          q.euclidean.symm k.bump hm hp hlocal

#print axioms T7_boundary_local_small_or_key_apex
end SparseMonotiles
