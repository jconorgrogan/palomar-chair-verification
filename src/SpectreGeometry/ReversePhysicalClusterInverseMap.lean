module

public import SpectreGeometry.ReversePhysicalClusterInverseCompatibility
public import SpectreGeometry.ReversePolygonalPathParameter

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters Deformation ReverseExistence ReversePhysicalCluster
open ReverseClusterTriangulation

def rawClusterInverseMap (big : Bool) (x : RealPoint) : EPlane := by
  classical
  exact if h : ∃ z : Fin (chartFamily big).length,
      x ∈ integerHull ((chartFamily big).getD z.val default).vertices
    then indexedRawInverseAffine big (Classical.choose h) x else 0

theorem rawClusterInverseMap_on
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) (z : Fin (chartFamily big).length) (x : RealPoint)
    (hx : x ∈ integerHull ((chartFamily big).getD z.val default).vertices) :
    rawClusterInverseMap big x = indexedRawInverseAffine big z x := by
  have hex : ∃ z : Fin (chartFamily big).length,
      x ∈ integerHull ((chartFamily big).getD z.val default).vertices := ⟨z,hx⟩
  simp only [rawClusterInverseMap,dif_pos hex]
  exact indexedRawInverseAffine_agree hbinding hfaces big _ z x (Classical.choose_spec hex) hx

/-- On every segment between two actual vertices of a single raw chart, the
assembled inverse is exactly the affine interpolation of the physical vertex
values. This includes whole cluster boundary subsegments once their owner is
supplied by the finite table. -/
theorem rawClusterInverseMap_lineMap
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) (z : Fin (chartFamily big).length) (a b : SpectreClusters.Point)
    (ha : a ∈ ((chartFamily big).getD z.val default).vertices)
    (hb : b ∈ ((chartFamily big).getD z.val default).vertices)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    rawClusterInverseMap big (AffineMap.lineMap (integerPoint a) (integerPoint b) t) =
      AffineMap.lineMap (euclideanCoordinates (quarterPoint (vertexImage4 big a)))
        (euclideanCoordinates (quarterPoint (vertexImage4 big b))) t := by
  have haHull : integerPoint a ∈ integerHull ((chartFamily big).getD z.val default).vertices :=
    subset_convexHull ℝ _ ⟨a,ha,rfl⟩
  have hbHull : integerPoint b ∈ integerHull ((chartFamily big).getD z.val default).vertices :=
    subset_convexHull ℝ _ ⟨b,hb,rfl⟩
  have hx : AffineMap.lineMap (integerPoint a) (integerPoint b) t ∈
      integerHull ((chartFamily big).getD z.val default).vertices :=
    (convex_convexHull ℝ _).lineMap_mem haHull hbHull ht
  rw [rawClusterInverseMap_on hbinding hfaces big z _ hx,
    (indexedRawInverseAffine big z).apply_lineMap,
    indexedRawInverseAffine_vertex hbinding big z a ha,
    indexedRawInverseAffine_vertex hbinding big z b hb]

/-- The exact whole-path parameter survives the inverse cluster map whenever
every literal path edge has a verified raw-triangle owner. -/
theorem rawClusterInverseMap_pathParameter
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) (ps : List SpectreClusters.Point)
    (howner : ∀ j, j < ps.length-1 → ∃ z : Fin (chartFamily big).length,
      ps.getD j (0,0) ∈ ((chartFamily big).getD z.val default).vertices ∧
      ps.getD (j+1) (0,0) ∈ ((chartFamily big).getD z.val default).vertices)
    (t : ℝ) (x : RealPoint) (hx : PathParameter (ps.map integerPoint) t x) :
    PathParameter (ps.map (fun p => quarterPoint (vertexImage4 big p)))
      t (euclideanCoordinates.symm (rawClusterInverseMap big x)) := by
  obtain ⟨j,hj,u,hu,hparam,hx⟩ := hx
  simp only [List.length_map] at hj hparam
  obtain ⟨z,hza,hzb⟩ := howner j hj
  have hget (g : SpectreClusters.Point → RealPoint) (d : RealPoint)
      (n : Nat) (hn : n < ps.length) : (ps.map g).getD n d = g (ps.getD n (0,0)) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hn,
      Option.map_some,Option.getD_some]
  refine ⟨j,by simpa only [List.length_map] using hj,u,hu,
    by simpa only [List.length_map] using hparam,?_⟩
  rw [hget integerPoint 0 j (by omega),hget integerPoint 0 (j+1) (by omega)] at hx
  rw [hget (fun p => quarterPoint (vertexImage4 big p)) 0 j (by omega),
    hget (fun p => quarterPoint (vertexImage4 big p)) 0 (j+1) (by omega)]
  rw [hx]
  apply euclideanCoordinates.injective
  rw [euclideanCoordinates.apply_symm_apply]
  change _ = coordinateLinearEquiv.toAffineMap (AffineMap.lineMap _ _ u)
  rw [coordinateLinearEquiv.toAffineMap.apply_lineMap]
  exact rawClusterInverseMap_lineMap hbinding hfaces big z _ _ hza hzb u hu

end
end SpectreGeometry.ReversePhysicalClusterCharts
