module

public import SpectreGeometry.ReversePhysicalFieldCompatibility
public import SpectreGeometry.ReverseRawChartFamilyCoverage

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence Deformation ReverseExistence
open ReversePhysicalCluster ReverseClusterTriangulation SpectreFinite SpectreFinite.HexSearch
open scoped NNReal

abbrev PhysicalTriangleIndex (f : Position → State) :=
  (c : Position) × Fin (chartFamily ((f c).1.val != 0)).length

def fieldTriangle (f : Position → State) (hf : GloballyLegal f)
    (i : PhysicalTriangleIndex f) : Set EPlane :=
  placedRawTriangle ((f i.1).1.val != 0) i.2 (f i.1).2 (markedAnchor f hf i.1)

def fieldClusterFrame (f : Position → State) (hf : GloballyLegal f)
    (c : Position) : Set EPlane := rawEuclideanFrame '' markedTargetCarrier f hf c

def fieldChartInverse (f : Position → State) (hf : GloballyLegal f)
    (B : Position → RealPoint) (i : PhysicalTriangleIndex f) : EPlane → EPlane :=
  placedRawChartInverse ((f i.1).1.val != 0) i.2 (f i.1).2 (markedAnchor f hf i.1) (B i.1)

theorem fieldClusterFrame_eq_triangles
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (f : Position → State) (hf : GloballyLegal f) (c : Position) :
    fieldClusterFrame f hf c = ⋃ z, fieldTriangle f hf ⟨c,z⟩ := by
  unfold fieldClusterFrame markedTargetCarrier placedClusterCarrier
  rw [chartFamily_covers_markedCluster hbinding (f c).1,image_iUnion,image_iUnion]
  apply iUnion_congr
  intro z
  exact (placedRawTriangle_eq_frame_image _ z _ _).symm

theorem fieldTriangle_subset_cluster
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (f : Position → State) (hf : GloballyLegal f) (i : PhysicalTriangleIndex f) :
    fieldTriangle f hf i ⊆ fieldClusterFrame f hf i.1 := by
  rcases i with ⟨c,z⟩
  rw [fieldClusterFrame_eq_triangles hbinding]
  exact subset_iUnion (fun w => fieldTriangle f hf ⟨c,w⟩) z

theorem fieldTriangle_isClosed (f : Position → State) (hf : GloballyLegal f)
    (i : PhysicalTriangleIndex f) : IsClosed (fieldTriangle f hf i) := by
  unfold fieldTriangle
  rw [placedRawTriangle_eq_frame_image]
  exact (((integerHull_isCompact _).image (axialMotionHomeomorph _ _).continuous).image
    rawEuclideanFrame.continuous).isClosed

theorem fieldTriangle_cover (C : MarkedAtlasFiniteInputs)
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (f : Position → State) (hf : GloballyLegal f) (x : EPlane) :
    ∃ i : PhysicalTriangleIndex f, x ∈ fieldTriangle f hf i := by
  obtain ⟨p,rfl⟩ := rawEuclideanFrame.surjective x
  obtain ⟨c,hc⟩ := C.marked_carriers_cover f hf p
  have hx : rawEuclideanFrame p ∈ fieldClusterFrame f hf c := ⟨p,hc,rfl⟩
  rw [fieldClusterFrame_eq_triangles hbinding] at hx
  obtain ⟨z,hz⟩ := mem_iUnion.mp hx
  exact ⟨⟨c,z⟩,hz⟩

theorem fieldTriangle_locallyFinite (C : MarkedAtlasFiniteInputs)
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (f : Position → State) (hf : GloballyLegal f) : LocallyFinite (fieldTriangle f hf) := by
  have hc : LocallyFinite (fieldClusterFrame f hf) :=
    homeomorph_images_locallyFinite rawEuclideanFrame (markedTargetCarrier f hf)
      (C.marked_carriers_locallyFinite f hf)
  exact locallyFinite_sigma_refinement (fieldClusterFrame f hf)
    (fun c z => fieldTriangle f hf ⟨c,z⟩) hc
    (fun c z => fieldTriangle_subset_cluster hbinding f hf ⟨c,z⟩)

theorem fieldChartInverse_residual_lipschitz
    (f : Position → State) (hf : GloballyLegal f) (B : Position → RealPoint)
    (i : PhysicalTriangleIndex f) :
    LipschitzWith (15/16 : ℝ≥0)
      (fun x => x-(31/32:ℝ) • fieldChartInverse f hf B i x) :=
  placedRawChartInverse_residual_lipschitz _ _ _ _ _

theorem fieldChartInverse_agree (C : MarkedAtlasFiniteInputs)
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (f : Position → State) (hf : GloballyLegal f) (B : Position → RealPoint)
    (hB : ∀ c d, (physicalPathReal (f c) d).map (fun p => B c+p) =
      ((physicalPathReal (f (sourceHexNeighbor c d)) (opposite d)).map
        (fun p => B (sourceHexNeighbor c d)+p)).reverse)
    (i j : PhysicalTriangleIndex f) (x : EPlane)
    (hi : x ∈ fieldTriangle f hf i) (hj : x ∈ fieldTriangle f hf j) :
    fieldChartInverse f hf B i x = fieldChartInverse f hf B j x := by
  obtain ⟨p,hp,hpx⟩ := fieldTriangle_subset_cluster hbinding f hf i hi
  obtain ⟨q,hq,hqx⟩ := fieldTriangle_subset_cluster hbinding f hf j hj
  have hqp : q=p := rawEuclideanFrame.injective (hqx.trans hpx.symm)
  subst q
  subst x
  rw [fieldChartInverse,fieldChartInverse,
    ←placedClusterInverse_on hbinding hfaces _ i.2 _ _ _ _ hi,
    ←placedClusterInverse_on hbinding hfaces _ j.2 _ _ _ _ hj,
    ←placedRawCoordinateInverse_frame,←placedRawCoordinateInverse_frame]
  exact congrArg euclideanCoordinates (fieldRawInverse_agree C hbinding hfaces f hf B hB
    i.1 j.1 p hp hq)

/-- The actual placed finite triangle cover and its compatible inverse charts
produce a whole-plane physical homeomorphism. There is no global P coverage,
injectivity or target-tiling hypothesis. -/
def physicalFieldHomeomorph (C : MarkedAtlasFiniteInputs)
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (f : Position → State) (hf : GloballyLegal f) (B : Position → RealPoint)
    (hB : ∀ c d, (physicalPathReal (f c) d).map (fun p => B c+p) =
      ((physicalPathReal (f (sourceHexNeighbor c d)) (opposite d)).map
        (fun p => B (sourceHexNeighbor c d)+p)).reverse) : EPlane ≃ₜ EPlane :=
  placedInverseCoverHomeomorph (fieldTriangle f hf)
    (fieldTriangle_locallyFinite C hbinding f hf) (fieldTriangle_isClosed f hf)
    (fieldTriangle_cover C hbinding f hf) (fieldChartInverse f hf B)
    (fieldChartInverse_agree C hbinding hfaces f hf B hB)
    (fieldChartInverse_residual_lipschitz f hf B)

/-- On each whole actual cluster, the plane homeomorphism is its exact placed
physical inverse map. -/
theorem physicalFieldHomeomorph_on_cluster (C : MarkedAtlasFiniteInputs)
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (f : Position → State) (hf : GloballyLegal f) (B : Position → RealPoint)
    (hB : ∀ c d, (physicalPathReal (f c) d).map (fun p => B c+p) =
      ((physicalPathReal (f (sourceHexNeighbor c d)) (opposite d)).map
        (fun p => B (sourceHexNeighbor c d)+p)).reverse)
    (c : Position) (x : EPlane) (hx : x ∈ fieldClusterFrame f hf c) :
    physicalFieldHomeomorph C hbinding hfaces f hf B hB x =
      placedClusterInverse ((f c).1.val != 0) (f c).2 (markedAnchor f hf c) (B c) x := by
  rw [fieldClusterFrame_eq_triangles hbinding] at hx
  obtain ⟨z,hz⟩ := mem_iUnion.mp hx
  unfold physicalFieldHomeomorph
  rw [placedInverseCoverHomeomorph_on _ _ _ _ _ _ _ ⟨c,z⟩ x hz]
  exact (placedClusterInverse_on hbinding hfaces _ z _ _ _ x hz).symm

end
end SpectreGeometry.ReversePhysicalClusterCharts
