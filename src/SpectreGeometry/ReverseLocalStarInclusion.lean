module

public import SpectreGeometry.ReverseLocalStarCommonFaces
public import SpectreGeometry.ReverseClusterTriangulationCarriers
public import SpectreGeometry.ReversePlacedClusterCharts

@[expose] public section


/-! Actual incident target triangles, after their declared rotation and scale,
lie in the corresponding placed closed cluster carrier. -/
namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseExistence

/-- Recentered integer rotation agrees exactly with an ambient affine motion. -/
theorem integerHull_centeredRotation (r : Fin 6) (center : Point) (vs : List Point) :
    integerHull (vs.map (fun p => SpectreClusters.rotate r (SpectreClusters.sub p center))) =
      gridMotion r (-gridRotation r (integerPoint center)) '' integerHull vs := by
  apply integerHull_map_affine
  intro p
  rw [integerPoint_rotate,gridMotion_apply]
  have hsub : integerPoint (SpectreClusters.sub p center) =
      integerPoint p - integerPoint center := by
    apply Prod.ext <;> simp [integerPoint,SpectreClusters.sub]
  rw [hsub]
  change (gridRotationLinear r) (integerPoint p-integerPoint center) =
    -(gridRotationLinear r) (integerPoint center)+(gridRotationLinear r) (integerPoint p)
  rw [map_sub]
  abel

/-- Every actually indexed target triangle is contained in the certified mesh carrier. -/
theorem target_triangle_hull_subset_family (k : Fin 9) (i : Nat)
    (hi : i < (meshTriangles k).length) :
    integerHull (triangleVertexList (targetVertices k) ((meshTriangles k).getD i (0,0,0))) ⊆
      familyBody (targetFamily k) := by
  intro q hq
  rw [←starBody_vertices,all_target_family_vertices_bound]
  exact ⟨_,List.mem_map.mpr ⟨_,getD_mem_of_lt (meshTriangles k) i (0,0,0) hi,rfl⟩,hq⟩

/-- Transport the cached incident-triangle star into the genuine placed carrier.
The bounds premise is the only finite indexing obligation; no source-vertex
correspondence or unproved fast-star equality is used. -/
theorem localStar_image_subset_placedClusterCarrier
    (k : Fin 9) (r : Fin 6) (v : Nat) (anchor : RealPoint)
    (hids : ∀ i ∈ incidentIds k v, i < (meshTriangles k).length) :
    (fun q : RealPoint => anchor + gridRotation r ((1/6 : ℝ) • integerPoint (targetVertex k v)) +
      (1/6 : ℝ) • q) '' starBody (localStar (k,r) v) ⊆
        placedClusterCarrier r anchor (SpectreClusters.ReverseExistence.clusterOfMark k) := by
  rintro p ⟨q,⟨t,ht,hq⟩,rfl⟩
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
  rw [integerHull_centeredRotation] at hq
  obtain ⟨y,hy,rfl⟩ := hq
  have hyfam : y ∈ familyBody (targetFamily k) :=
    target_triangle_hull_subset_family k i (hids i hi) hy
  have hynorm : (1/6 : ℝ) • y ∈
      rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) := by
    rw [←all_normalized_target_carriers_exact k]
    exact ⟨y,hyfam,rfl⟩
  refine ⟨(1/6 : ℝ) • y,hynorm,?_⟩
  simp only [axialMotionHomeomorph_apply,gridMotion_apply]
  change anchor + (gridRotationLinear r) ((1/6 : ℝ) • y) =
    anchor + (gridRotationLinear r) ((1/6 : ℝ) • integerPoint (targetVertex k v)) +
      (1/6 : ℝ) • (-(gridRotationLinear r) (integerPoint (targetVertex k v)) +
        (gridRotationLinear r) y)
  simp only [map_smul,smul_add,smul_neg]
  abel

end
end SpectreGeometry.ReverseLocalStarOccurrences
