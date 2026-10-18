module

public import SpectreGeometry.ReversePhysicalClusterInverseMap
public import SpectreGeometry.ReverseRawChartCoverage

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters Deformation ReverseExistence ReversePhysicalCluster
open ReverseClusterTriangulation

def physicalPieceAffine (big : Bool) (n : Nat) : RealPoint →ᵃ[ℝ] EPlane :=
  coordinateLinearEquiv.toAffineMap.comp
    ((AffineEquiv.constVAdd ℝ RealPoint (physicalOrigin big n)).toAffineMap.comp
      (rotationLinearMap (physicalTurn (rawPiece big n))).toAffineMap)

@[simp] theorem physicalPieceAffine_apply (big : Bool) (n : Nat) (x : RealPoint) :
    physicalPieceAffine big n x = euclideanCoordinates
      (physicalOrigin big n + SpectreGeometry.rotate (physicalTurn (rawPiece big n)) x) := rfl

private theorem raw_vertices_range (big : Bool) (n : Nat) (i : Fin 12) :
    integerVertexSet (rawChartVertices big n i) =
      range (fun v : Fin 3 => integerPoint (rawPlacedVertex (rawPiece big n)
        (physicalIndex (rawPiece big n).kind (triangleIndex i v)))) := by
  ext x
  simp only [integerVertexSet,mem_image,mem_setOf_eq,rawChartVertices,
    List.mem_cons,List.not_mem_nil,or_false,mem_range,
    Fin.exists_fin_succ,Fin.exists_fin_zero]
  change (∃ a, (a = _ ∨ a = _ ∨ a = _) ∧ integerPoint a = x) ↔ _
  simp only [or_and_right,exists_or,exists_eq_left]
  simp [triangleIndex,rawPiece,or_comm,or_left_comm,or_assoc]

/-- Each inverse affine chart maps its entire raw triangle onto the
corresponding translated, properly rotated source-P triangle. -/
theorem rawClusterInverseAffine_image_triangle (big : Bool) (n : Fin 9)
    (hn : n.val < (pieces big).length) (i : Fin 12) :
    rawClusterInverseAffine big n.val i '' integerHull (rawChartVertices big n.val i) =
      physicalPieceAffine big n.val '' sourceTriangle i := by
  change rawClusterInverseAffine big n.val i ''
    convexHull ℝ (integerVertexSet (rawChartVertices big n.val i)) = _
  rw [AffineMap.image_convexHull,sourceTriangle_eq_hull,AffineMap.image_convexHull]
  congr 1
  rw [raw_vertices_range,sourceVertices,←Set.range_comp',←Set.range_comp']
  congr 1
  funext v
  have hv := rawPieceInverseChart_vertex big n hn i v
  rw [rawClusterInverseAffine_apply]
  rw [hv]
  have hw := literal_piece_vertex_real big n hn
    (physicalIndex (rawPiece big n.val).kind (triangleIndex i v))
  change quarterPoint (vertexImage4 big (rawPlacedVertex (rawPiece big n.val)
      (physicalIndex (rawPiece big n.val).kind (triangleIndex i v)))) =
    physicalOrigin big n.val + SpectreGeometry.rotate (physicalTurn (rawPiece big n.val))
      (realVertex (physicalIndex (rawPiece big n.val).kind
        (physicalIndex (rawPiece big n.val).kind (triangleIndex i v)))) at hw
  rw [physicalIndex_involutive] at hw
  rw [hw]
  rfl

/-- Exact image of one whole raw H/T piece under the assembled inverse map.
The only local compatibility inputs are the finite chart bindings and faces. -/
theorem rawClusterInverseMap_image_piece
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) (n : Fin 9) (hn : n.val < (pieces big).length) :
    rawClusterInverseMap big '' placementKiteBody (rawPiece big n.val) =
      physicalPieceAffine big n.val '' polygonBody := by
  rw [show placementKiteBody (rawPiece big n.val) =
      ⋃ i : Fin 12, integerHull (rawChartVertices big n.val i) from
        raw_piece_covered_by_chart_triangles big n.val,
    sourceTriangles_cover_polygonBody,image_iUnion,image_iUnion]
  apply iUnion_congr
  intro i
  rw [←rawClusterInverseAffine_image_triangle big n hn i]
  apply Set.image_congr
  intro x hx
  have hz : 12*n.val+i.val < (chartFamily big).length := by
    rw [chartFamily_length]
    omega
  let z : Fin (chartFamily big).length := ⟨12*n.val+i.val,hz⟩
  have hdiv : z.val/12=n.val := by dsimp [z]; omega
  have hmod : (⟨z.val%12,Nat.mod_lt _ (by decide)⟩ : Fin 12)=i := by
    apply Fin.ext
    dsimp [z]
    omega
  have hvertices := (hbinding big z.val z.isLt).2
  rw [hdiv,hmod] at hvertices
  have hxon : x ∈ integerHull ((chartFamily big).getD z.val default).vertices := by
    rw [hvertices]
    exact hx
  rw [rawClusterInverseMap_on hbinding hfaces big z x hxon,indexedRawInverseAffine,
    hdiv,hmod]

end
end SpectreGeometry.ReversePhysicalClusterCharts
