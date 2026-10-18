module

public import SpectreGeometry.ReverseFinitePLScaledMesh
public import SpectreGeometry.ReverseMarkedBoundaryParameters

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseExistence

/-- The marked boundary formula is independent of how the finite mesh's
carrier and common-face certificates were obtained. -/
theorem scaledMarkedMesh_boundary_edge (D : IntegerMeshPair) (k : Fin 9)
    (hsource : D.source = sourceVertices k) (htarget : D.target = targetVertices k)
    (htriangles : D.triangles = meshTriangles k)
    (d : Fin 6) (j : Nat) (hj : j < (boundaryIndices k d).length-1)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1)
    (ha : (1/(3*(sourceScale k:ℝ))) ≠ 0)
    (x : ((fun p : Plane => (1/(3*(sourceScale k:ℝ))) • p) '' D.meshPair.closedCharts.sourceCarrier))
    (hx : x.val = AffineMap.lineMap (sourceHexCorner d) (sourceHexCorner (d+1))
      (((j:ℝ)+u)/((boundaryIndices k d).length-1))) :
    (D.scaledHomeomorph (1/(3*(sourceScale k:ℝ))) (1/6) ha (by norm_num) x).val =
      AffineMap.lineMap
        ((1/6:ℝ) • integerPoint (targetVertex k ((boundaryIndices k d).getD j 0)))
        ((1/6:ℝ) • integerPoint (targetVertex k ((boundaryIndices k d).getD (j+1) 0))) u := by
  have ho := all_boundary_edge_owners k d j (List.mem_range.mpr hj)
  dsimp only at ho
  have ht : boundaryEdgeOwner k d j < D.triangles.length := by simpa only [htriangles] using ho.1
  let ti : Fin D.triangles.length := ⟨boundaryEdgeOwner k d j,ht⟩
  have he : D.triangles.get ti = (meshTriangles k).getD (boundaryEdgeOwner k d j) (0,0,0) := by
    have hh := congrArg (fun ts : List TriangleCode =>
      ts.getD (boundaryEdgeOwner k d j) (0,0,0)) htriangles
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht,
      List.getElem?_eq_getElem ho.1,Option.getD_some,List.get_eq_getElem,ti] using hh
  have hn0 : (boundaryIndices k d).getD j 0 ∈ triangleIndices (D.triangles.get ti) := by
    rw [he]; exact ho.2.1
  have hm0 : (boundaryIndices k d).getD (j+1) 0 ∈ triangleIndices (D.triangles.get ti) := by
    rw [he]; exact ho.2.2
  let n : Fin D.source.length := ⟨(boundaryIndices k d).getD j 0,
    D.index_bound _ (List.get_mem _ ti) _ hn0⟩
  let m : Fin D.source.length := ⟨(boundaryIndices k d).getD (j+1) 0,
    D.index_bound _ (List.get_mem _ ti) _ hm0⟩
  have hj0 : j < (boundaryIndices k d).length := by omega
  have hj1 : j+1 < (boundaryIndices k d).length := by omega
  have hy : x.val = AffineMap.lineMap ((1/(3*(sourceScale k:ℝ))) • D.sourceVertex n)
      ((1/(3*(sourceScale k:ℝ))) • D.sourceVertex m) u := by
    simp only [IntegerMeshPair.sourceVertex,hsource]
    change x.val = AffineMap.lineMap
      ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k ((boundaryIndices k d).getD j 0)))
      ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k ((boundaryIndices k d).getD (j+1) 0))) u
    rw [normalized_boundary_vertex k d j hj0,normalized_boundary_vertex k d (j+1) hj1,hx]
    ext <;> simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,Prod.smul_fst,Prod.smul_snd,
      Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Nat.cast_add,Nat.cast_one,smul_eq_mul] <;> ring
  have h := D.scaledHomeomorph_edge (1/(3*(sourceScale k:ℝ))) (1/6) ha (by norm_num) ti n m hn0 hm0 u hu x hy
  simpa only [IntegerMeshPair.targetVertex,htarget,targetVertex,n,m] using h

end
end SpectreGeometry.ReverseFinitePL
