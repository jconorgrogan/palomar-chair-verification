module

public import PhysicalRegistration.RegisteredTubeGeometry

@[expose] public section

/-! Different lattice facet data separate actual registered tube images.
Intersection therefore forces exact common facet-center coordinates. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
open Set RegisteredPrime

 theorem registered_closedTube_disjoint_of_enclosures {m J : ℕ}
    (q : Pose (m+1)) (u v : Site m)
    (hs : _root_.Disjoint
      (coordinateTube (normalIndex u.1) (fun i => siteCenter u i) (eta m) (rho m))
      (coordinateTube (registeredFacetAxis q v.1) (fun i => poseIsometry q (siteCenter v) i)
        (eta m) (rho m))) :
    _root_.Disjoint (closedTube J u) (poseIsometry q '' closedTube J v) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp hs (closedTube_mem_coordinateTube u x hx)
    (registered_tube_coordinate_enclosure q v hy)

 theorem registered_closedTube_disjoint_normals {m J : ℕ} (hm : 2 ≤ m)
    (q : Pose (m+1)) (u v : Site m) (hn : normalIndex u.1 ≠ registeredFacetAxis q v.1) :
    _root_.Disjoint (closedTube J u) (poseIsometry q '' closedTube J v) := by
  apply registered_closedTube_disjoint_of_enclosures q u v
  exact native_coordinateTube_disjoint_of_different_normals ((m : ℝ)+1)
    (by exact_mod_cast Nat.succ_le_succ hm) _ _ _ _ hn
    (registeredFacetPlane q v.1) (registered_siteCenter_normal q v)
    (facetCellCoordinate u.1 (registeredFacetAxis q v.1)) (siteOffset u (registeredFacetAxis q v.1))
    (siteCenter_tangent u _ hn.symm) (siteOffset_coordinate_bound u _)

 theorem registered_closedTube_disjoint_planes {m J : ℕ} (hm : 2 ≤ m)
    (q : Pose (m+1)) (u v : Site m) (hn : normalIndex u.1 = registeredFacetAxis q v.1)
    (hp : facetPlane u.1 ≠ registeredFacetPlane q v.1) :
    _root_.Disjoint (closedTube J u) (poseIsometry q '' closedTube J v) := by
  apply registered_closedTube_disjoint_of_enclosures q u v
  have hv : poseIsometry q (siteCenter v) (normalIndex u.1) = (registeredFacetPlane q v.1 : ℝ) := by
    rw [hn]; exact registered_siteCenter_normal q v
  simpa only [hn,eta,rho] using native_coordinateTube_disjoint_of_distinct_integer_planes
    ((m : ℝ)+1) (by exact_mod_cast Nat.succ_le_succ hm) (normalIndex u.1)
    (fun i => siteCenter u i) (fun i => poseIsometry q (siteCenter v) i)
    (facetPlane u.1) (registeredFacetPlane q v.1) (siteCenter_normal u) hv hp

 theorem registered_closedTube_disjoint_tangentCells {m J : ℕ} (hm : 2 ≤ m)
    (q : Pose (m+1)) (u v : Site m) (hn : normalIndex u.1 = registeredFacetAxis q v.1)
    (i : Fin (m+1)) (hi : i ≠ normalIndex u.1)
    (hc : facetCellCoordinate u.1 i ≠ registeredFacetCell q v.1 i) :
    _root_.Disjoint (closedTube J u) (poseIsometry q '' closedTube J v) := by
  apply registered_closedTube_disjoint_of_enclosures q u v
  have hi' : i ≠ registeredFacetAxis q v.1 := by simpa only [← hn] using hi
  simpa only [hn,eta,rho] using native_coordinateTube_disjoint_of_distinct_tangent_cells
    ((m : ℝ)+1) (by exact_mod_cast Nat.succ_le_succ hm) (normalIndex u.1) i
    (fun k => siteCenter u k) (fun k => poseIsometry q (siteCenter v) k) hi
    (facetCellCoordinate u.1 i) (registeredFacetCell q v.1 i)
    (siteOffset u i) (registeredSiteOffset q v i)
    (siteCenter_tangent u i hi) (registered_siteCenter_tangent q v i hi') hc
    (siteOffset_coordinate_bound u i) (registeredSiteOffset_bound q v i)

/-- Intersecting registered tubes lie on exactly the same lattice facet.
This conclusion retains the integer plane and every tangent unit-cell index. -/
 theorem registered_closedTube_intersection_facet_data {m J : ℕ} (hm : 2 ≤ m)
    (q : Pose (m+1)) (u v : Site m)
    (hx : (closedTube J u ∩ poseIsometry q '' closedTube J v).Nonempty) :
    normalIndex u.1 = registeredFacetAxis q v.1 ∧ facetPlane u.1 = registeredFacetPlane q v.1 ∧
      ∀ i, i ≠ normalIndex u.1 → facetCellCoordinate u.1 i = registeredFacetCell q v.1 i := by
  have hnd : ¬ _root_.Disjoint (closedTube J u) (poseIsometry q '' closedTube J v) := by
    intro h
    obtain ⟨x,hx,hy⟩ := hx
    exact Set.disjoint_left.mp h hx hy
  have hn : normalIndex u.1 = registeredFacetAxis q v.1 := by
    by_contra h
    exact hnd (registered_closedTube_disjoint_normals hm q u v h)
  refine ⟨hn,?_,fun i hi => ?_⟩
  · by_contra h
    exact hnd (registered_closedTube_disjoint_planes hm q u v hn h)
  · by_contra h
    exact hnd (registered_closedTube_disjoint_tangentCells hm q u v hn i hi h)

 theorem registered_closedTube_intersection_facetCenter {m J : ℕ} (hm : 2 ≤ m)
    (q : Pose (m+1)) (u v : Site m)
    (hx : (closedTube J u ∩ poseIsometry q '' closedTube J v).Nonempty) :
    poseIsometry q (facetCenter v.1) = facetCenter u.1 := by
  obtain ⟨hn,hp,hc⟩ := registered_closedTube_intersection_facet_data hm q u v hx
  ext i
  by_cases hi : i=normalIndex u.1
  · rw [hi,hn,registered_facetCenter_normal,←hp,←facetCenter_normal u.1,←hn]
  · have hi' : i ≠ registeredFacetAxis q v.1 := by simpa only [←hn] using hi
    rw [registered_facetCenter_tangent q v.1 i hi',facetCenter_tangent u.1 i hi,hc i hi]

#print axioms registered_closedTube_intersection_facet_data
#print axioms registered_closedTube_intersection_facetCenter
end
end PhysicalRegistration.NativeChair
