module

public import SpectreGeometry.ReverseRawInverseChartValues
public import SpectreGeometry.ReversePhysicalClusterChartFacesData
public import SpectreGeometry.ReverseClusterTriangulationFacesAssemblyReal
public import SpectreGeometry.ReverseFinitePLInteger

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters Deformation ReverseExistence ReversePhysicalCluster
open ReverseClusterTriangulation

/-- Each physical inverse chart, pulled back to literal raw coordinates, is
an affine map. This makes exact vertex agreement sufficient on a common face. -/
def rawClusterInverseAffine (big : Bool) (n : Nat) (i : Fin 12) :
    RealPoint →ᵃ[ℝ] EPlane :=
  (inverseChartAffine (physicalTurn (rawPiece big n)) i
    (rawInverseSourceAnchor big n i) (rawInverseTargetAnchor big n i)).comp
      (coordinateLinearEquiv.toAffineMap.comp rawFrame.toAffineMap)

@[simp] theorem rawClusterInverseAffine_apply (big : Bool) (n : Nat) (i : Fin 12)
    (p : RealPoint) :
    rawClusterInverseAffine big n i p =
      rawPieceInverseChart big n i (euclideanCoordinates (rawFrame p)) := by
  simp only [rawClusterInverseAffine,AffineMap.comp_apply,inverseChartAffine_apply]
  rfl

theorem rawClusterInverseAffine_vertex (big : Bool) (n : Fin 9)
    (hn : n.val < (pieces big).length) (i : Fin 12) (p : SpectreClusters.Point)
    (hp : p ∈ rawChartVertices big n.val i) :
    rawClusterInverseAffine big n.val i (integerPoint p) =
      euclideanCoordinates (quarterPoint (vertexImage4 big p)) := by
  rw [rawClusterInverseAffine_apply]
  change p ∈ [rawPlacedVertex (rawPiece big n.val)
      (physicalIndex (rawPiece big n.val).kind (triangle i).1),
    rawPlacedVertex (rawPiece big n.val)
      (physicalIndex (rawPiece big n.val).kind (triangle i).2.2),
    rawPlacedVertex (rawPiece big n.val)
      (physicalIndex (rawPiece big n.val).kind (triangle i).2.1)] at hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact rawPieceInverseChart_vertex big n hn i 0
  · exact rawPieceInverseChart_vertex big n hn i 2
  · exact rawPieceInverseChart_vertex big n hn i 1

def indexedRawInverseAffine (big : Bool) (z : Fin (chartFamily big).length) :
    RealPoint →ᵃ[ℝ] EPlane :=
  rawClusterInverseAffine big (z.val/12) ⟨z.val%12,Nat.mod_lt _ (by decide)⟩

theorem indexedRawInverseAffine_vertex
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (big : Bool) (z : Fin (chartFamily big).length) (p : SpectreClusters.Point)
    (hp : p ∈ ((chartFamily big).getD z.val default).vertices) :
    indexedRawInverseAffine big z (integerPoint p) =
      euclideanCoordinates (quarterPoint (vertexImage4 big p)) := by
  have hn : z.val/12 < (pieces big).length := by
    have h := lt_of_lt_of_eq z.isLt (chartFamily_length big)
    omega
  have hlen : (pieces big).length ≤ 9 := by cases big <;> decide
  rw [(hbinding big z.val z.isLt).2] at hp
  exact rawClusterInverseAffine_vertex big ⟨z.val/12,by omega⟩ hn _ p hp

theorem physical_chart_family_has_faces
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) : FamilyHasFaces (chartFamily big) :=
  familyHasFaces_of_rows (chartFamily big) (fun z => (chartFaceRows big).getD z [])
    (fun z => hfaces big z.val z.isLt)

/-- Actual inverse charts from different literal pieces of the same cluster
agree on their entire raw triangle overlap. The finite common-face binding and
single physical vertex-value table are the only compatibility inputs. -/
theorem indexedRawInverseAffine_agree
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) (z w : Fin (chartFamily big).length) (x : RealPoint)
    (hx : x ∈ integerHull ((chartFamily big).getD z.val default).vertices)
    (hy : x ∈ integerHull ((chartFamily big).getD w.val default).vertices) :
    indexedRawInverseAffine big z x = indexedRawInverseAffine big w x := by
  by_cases he : z=w
  · subst w
    rfl
  have hface : x ∈ convexHull ℝ
      (integerVertexSet ((chartFamily big).getD z.val default).vertices ∩
        integerVertexSet ((chartFamily big).getD w.val default).vertices) := by
    rw [←(physical_chart_family_has_faces hfaces big z w he).1]
    exact ⟨hx,hy⟩
  have hv : Set.EqOn (indexedRawInverseAffine big z) (indexedRawInverseAffine big w)
      (integerVertexSet ((chartFamily big).getD z.val default).vertices ∩
        integerVertexSet ((chartFamily big).getD w.val default).vertices) := by
    rintro p ⟨⟨a,ha,hae⟩,⟨b,hb,hbe⟩⟩
    have hab : a=b := ReverseFinitePL.integerPoint_injective (hae.trans hbe.symm)
    subst b
    rw [←hae,indexedRawInverseAffine_vertex hbinding big z a ha,
      indexedRawInverseAffine_vertex hbinding big w a hb]
  exact AffineMap.eqOn_affineSpan hv (convexHull_subset_affineSpan _ hface)

end
end SpectreGeometry.ReversePhysicalClusterCharts
