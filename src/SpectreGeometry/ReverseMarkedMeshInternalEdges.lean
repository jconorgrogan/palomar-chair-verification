module

public import SpectreGeometry.ReverseMarkedMeshInteriorDisjoint
public import SpectreGeometry.ReverseMeshEdgeNeighborhood

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL.MarkedMeshCertificate
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseExistence
variable {k : Fin 9} (C : MarkedMeshCertificate k)
include C

/-- Every genuine internal mesh edge has an ambient neighborhood inside the
literal raw target cluster. The second triangle and its distinct index come
from the checked finite edge-incidence table. -/
theorem internal_edge_interior
    (i j : Fin (meshTriangles k).length) (hij : i ≠ j)
    (n m : Fin (sourceVertices k).length) (hnm : n ≠ m)
    (hni : n.val ∈ triangleIndices ((meshTriangles k).get i))
    (hmi : m.val ∈ triangleIndices ((meshTriangles k).get i))
    (hnj : n.val ∈ triangleIndices ((meshTriangles k).get j))
    (hmj : m.val ∈ triangleIndices ((meshTriangles k).get j))
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    AffineMap.lineMap ((1/6:ℝ) • integerPoint (targetVertex k n.val))
      ((1/6:ℝ) • integerPoint (targetVertex k m.val)) t ∈
        interior (rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k)) := by
  let D := C.markedIntegerMesh
  obtain ⟨v,hv⟩ := (mem_triangleIndices _ n.val).mp hni
  obtain ⟨w,hw⟩ := (mem_triangleIndices _ m.val).mp hmi
  obtain ⟨v',hv'⟩ := (mem_triangleIndices _ n.val).mp hnj
  obtain ⟨w',hw'⟩ := (mem_triangleIndices _ m.val).mp hmj
  have hvn : D.meshIndex i v = n := Fin.ext hv
  have hwm : D.meshIndex i w = m := Fin.ext hw
  have hvn' : D.meshIndex j v' = n := Fin.ext hv'
  have hwm' : D.meshIndex j w' = m := Fin.ext hw'
  have hvw : v ≠ w := by
    intro he
    apply hnm
    rw [←hvn,←hwm,he]
  have hvw' : v' ≠ w' := by
    intro he
    apply hnm
    rw [←hvn',←hwm',he]
  have hi := D.meshPair.target_shared_edge_interior i j v w v' w' hvw hvw'
    (hvn.trans hvn'.symm) (hwm.trans hwm'.symm)
    (C.target_triangle_interiors_disjoint i j hij) t ht
  have hsub : D.meshPair.closedCharts.target i ∪ D.meshPair.closedCharts.target j ⊆
      D.meshPair.closedCharts.targetCarrier := by
    rintro y (hy | hy)
    · exact mem_iUnion.mpr ⟨i,hy⟩
    · exact mem_iUnion.mpr ⟨j,hy⟩
  have hi' := interior_mono hsub hi
  change AffineMap.lineMap (D.targetVertex (D.meshIndex i v))
    (D.targetVertex (D.meshIndex i w)) t ∈ interior D.meshPair.closedCharts.targetCarrier at hi'
  rw [hvn,hwm] at hi'
  let H := scalarHomeomorph (1/6:ℝ) (by norm_num)
  have himg : H (AffineMap.lineMap (D.targetVertex n) (D.targetVertex m) t) ∈
      interior (H '' D.meshPair.closedCharts.targetCarrier) := by
    rw [←H.image_interior]
    exact ⟨_,hi',rfl⟩
  have hcarrier : H '' D.meshPair.closedCharts.targetCarrier =
      rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) := C.markedNormalizedTarget
  rw [hcarrier] at himg
  have he : H (AffineMap.lineMap (D.targetVertex n) (D.targetVertex m) t) =
      AffineMap.lineMap ((1/6:ℝ) • integerPoint (targetVertex k n.val))
        ((1/6:ℝ) • integerPoint (targetVertex k m.val)) t := by
    change (1/6:ℝ) • AffineMap.lineMap (integerPoint (targetVertex k n.val))
      (integerPoint (targetVertex k m.val)) t = _
    ext <;> simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,Prod.smul_fst,
      Prod.smul_snd,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,smul_eq_mul] <;> ring
  rwa [he] at himg

end
end SpectreGeometry.ReverseFinitePL.MarkedMeshCertificate
