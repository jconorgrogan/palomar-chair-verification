module

public import SpectreGeometry.ReverseMarkedNeighborInteriors
public import SpectreGeometry.ReverseMarkedPathVertexCenters
public import SpectreGeometry.ReverseTrianglePlacedGeometry
public import SpectreGeometry.ReverseIndependentTriangleEdges
public import SpectreGeometry.ReverseLocalStarBoundaryIndexNodup

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseLocalStarOccurrences ReverseFinitePL
open ReverseClusterNeighborCells ReverseClusterNeighborBinding

private theorem boundary_adjacent_distinct (k : Fin 9) (d : Fin 6) (j : Nat)
    (hj : j < (boundaryIndices k d).length-1) :
    (boundaryIndices k d).getD j 0 ≠ (boundaryIndices k d).getD (j+1) 0 := by
  intro he
  have hj0 : j < (boundaryIndices k d).length := by omega
  have hj1 : j+1 < (boundaryIndices k d).length := by omega
  have hh : (⟨j,hj0⟩ : Fin (boundaryIndices k d).length) = ⟨j+1,hj1⟩ :=
    (all_boundary_indices_distinct k d).injective_get (by
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj0,
        List.getElem?_eq_getElem hj1,Option.getD_some,List.get_eq_getElem] using he)
  have hn := congrArg Fin.val hh
  change j = j+1 at hn
  omega

private theorem boundary_edge_triangle (k : Fin 9) (d : Fin 6) (j : Nat)
    (hj : j < (boundaryIndices k d).length-1) :
    ∃ i : Fin (meshTriangles k).length, ∃ v w : Fin 3, v ≠ w ∧
      codeIndex ((meshTriangles k).get i) v = (boundaryIndices k d).getD j 0 ∧
      codeIndex ((meshTriangles k).get i) w = (boundaryIndices k d).getD (j+1) 0 := by
  have ho := all_boundary_edge_owners k d j (List.mem_range.mpr hj)
  dsimp only at ho
  let i : Fin (meshTriangles k).length := ⟨boundaryEdgeOwner k d j,ho.1⟩
  have hget : (meshTriangles k).getD (boundaryEdgeOwner k d j) (0,0,0) =
      (meshTriangles k).get i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ho.1,
      Option.getD_some,List.get_eq_getElem,i]
  rw [hget] at ho
  obtain ⟨v,hv⟩ := (mem_triangleIndices _ _).mp ho.2.1
  obtain ⟨w,hw⟩ := (mem_triangleIndices _ _).mp ho.2.2
  refine ⟨i,v,w,?_,hv,hw⟩
  intro he
  apply boundary_adjacent_distinct k d j hj
  rw [←hv,←hw,he]

private theorem actual_target_triangle_nondegenerate (k : Fin 9)
    (i : Fin (meshTriangles k).length) :
    triangleDet (codeTriangle (targetVertices k) ((meshTriangles k).get i)) ≠ 0 :=
  codeTriangle_nondegenerate _ _
    (packet_binding_positive (targetVertices k) (meshTriangles k) (targetFamily k)
      (all_target_family_vertices_bound k) (all_target_family_checked k)
      _ (List.get_mem _ i))

/-- Every actual nonvertex boundary subsegment has a neighborhood in its two
neighboring target carriers. The two triangles are taken from their checked
boundary owners; exact path reversal identifies both shared endpoints. -/
theorem marked_boundary_open_edge_interior
    (hchecked : ∀ i : Fin 35, configurationCheckedB (configuration i) = true)
    (hbinding : ∀ k r, MarkedConfigurationCertificate k r)
    (f : Position → State) (hf : GloballyLegal f) (c : Position) (d : Fin 6)
    (j : Nat) (hj : j < (stateBoundaryIds (f c) d).length-1)
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    AffineMap.lineMap ((realDevelopedPath f hf c d).getD j 0)
      ((realDevelopedPath f hf c d).getD (j+1) 0) t ∈
      interior (markedTargetCarrier f hf c ∪
        markedTargetCarrier f hf (sourceHexNeighbor c d)) := by
  let b := sourceHexNeighbor c d
  let idsA := stateBoundaryIds (f c) d
  let idsB := stateBoundaryIds (f b) (opposite d)
  let q := idsB.length-2-j
  have hlen : idsA.length=idsB.length := stateBoundaryIds_neighbor_length f hf c d
  have hj0 : j < idsA.length := by dsimp [idsA]; omega
  have hj1 : j+1 < idsA.length := by dsimp [idsA]; omega
  have hq : q < idsB.length-1 := by dsimp [q,idsA,idsB] at *; omega
  have hq0 : q < idsB.length := by omega
  have hq1 : q+1 < idsB.length := by omega
  have hqj : idsB.length-1-j = q+1 := by dsimp [q,idsA,idsB] at *; omega
  have hqj1 : idsB.length-1-(j+1) = q := by dsimp [q]; omega
  obtain ⟨i,v,w,hvw,hv,hw⟩ := boundary_edge_triangle (f c).1 (sideTurn (f c).2 d) j hj
  obtain ⟨i',v',w',hvw',hv',hw'⟩ :=
    boundary_edge_triangle (f b).1 (sideTurn (f b).2 (opposite d)) q hq
  let V := placedTriangleVertices (f c).2 (markedAnchor f hf c) (1/6)
    (codeTriangle (targetVertices (f c).1) ((meshTriangles (f c).1).get i))
  let W := placedTriangleVertices (f b).2 (markedAnchor f hf b) (1/6)
    (codeTriangle (targetVertices (f b).1) ((meshTriangles (f b).1).get i'))
  have hV : triangleDet V ≠ 0 := triangleDet_placed_ne_zero _ _ _ (by norm_num) _
    (actual_target_triangle_nondegenerate (f c).1 i)
  have hW : triangleDet W ≠ 0 := triangleDet_placed_ne_zero _ _ _ (by norm_num) _
    (actual_target_triangle_nondegenerate (f b).1 i')
  have hv0 : V v = (realDevelopedPath f hf c d).getD j 0 := by
    rw [realDevelopedPath_vertex f hf c d j hj0]
    change _ + gridRotation _ ((1/6:ℝ) • integerPoint
      (targetVertex (f c).1 (codeIndex ((meshTriangles (f c).1).get i) v))) = _
    rw [hv]
    rfl
  have hw0 : V w = (realDevelopedPath f hf c d).getD (j+1) 0 := by
    rw [realDevelopedPath_vertex f hf c d (j+1) hj1]
    change _ + gridRotation _ ((1/6:ℝ) • integerPoint
      (targetVertex (f c).1 (codeIndex ((meshTriangles (f c).1).get i) w))) = _
    rw [hw]
    rfl
  have hv1 : W v' = (realDevelopedPath f hf b (opposite d)).getD q 0 := by
    rw [realDevelopedPath_vertex f hf b (opposite d) q hq0]
    change _ + gridRotation _ ((1/6:ℝ) • integerPoint
      (targetVertex (f b).1 (codeIndex ((meshTriangles (f b).1).get i') v'))) = _
    rw [hv']
    rfl
  have hw1 : W w' = (realDevelopedPath f hf b (opposite d)).getD (q+1) 0 := by
    rw [realDevelopedPath_vertex f hf b (opposite d) (q+1) hq1]
    change _ + gridRotation _ ((1/6:ℝ) • integerPoint
      (targetVertex (f b).1 (codeIndex ((meshTriangles (f b).1).get i') w'))) = _
    rw [hw']
    rfl
  have hreverse (n : Nat) (hn : n < idsB.length) :
      (realDevelopedPath f hf c d).getD n 0 =
      (realDevelopedPath f hf b (opposite d)).getD (idsB.length-1-n) 0 := by
    rw [realDevelopedPath_glue]
    have hn' : n < (realDevelopedPath f hf b (opposite d)).length := by
      rwa [realDevelopedPath_length]
    change ((realDevelopedPath f hf b (opposite d)).reverse).getD n 0 = _
    simpa only [List.getD_eq_getElem?_getD,realDevelopedPath_length,idsB] using
      congrArg (fun o : Option RealPoint => o.getD 0) (List.getElem?_reverse hn')
  have hstart : V v = W w' := by
    rw [hv0,hw1,hreverse j (by omega),hqj]
  have hend : V w = W v' := by
    rw [hw0,hv1,hreverse (j+1) (by omega),hqj1]
  have hsV : triangleHull V ⊆ markedTargetCarrier f hf c :=
    placed_target_triangle_subset_carrier (f c).1 (f c).2 (markedAnchor f hf c) i
  have hsW : triangleHull W ⊆ markedTargetCarrier f hf b :=
    placed_target_triangle_subset_carrier (f b).1 (f b).2 (markedAnchor f hf b) i'
  have hd := (marked_neighbor_interiors_disjoint_of_certificates hchecked hbinding f hf c d).mono
    (interior_mono hsV) (interior_mono hsW)
  have hi := triangles_shared_edge_interior V W hV hW v w w' v' hvw (Ne.symm hvw')
    hstart hend hd t ht
  rw [hv0,hw0] at hi
  apply interior_mono (s := triangleHull V ∪ triangleHull W) (t := markedTargetCarrier f hf c ∪
    markedTargetCarrier f hf b) ?_ hi
  rintro y (hy | hy)
  · exact Or.inl (hsV hy)
  · exact Or.inr (hsW hy)

end
end SpectreGeometry.ReverseExistence
