module

public import SpectreGeometry.ReversePlacedPhysicalBoundary
public import SpectreGeometry.ReverseMarkedWholePlaneHomeomorphism

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence Deformation ReverseExistence
open ReversePhysicalCluster ReverseClusterTriangulation SpectreFinite SpectreFinite.HexSearch

/-- The raw-coordinate inverse attached to one actual cluster in the marked field. -/
def fieldRawInverse (f : Position → State) (hf : GloballyLegal f)
    (B : Position → RealPoint) (c : Position) (p : RealPoint) : RealPoint :=
  placedRawCoordinateInverse ((f c).1.val != 0) (f c).2 (markedAnchor f hf c) (B c) p

/-- Whole-plane marked inversion implies that distinct overlapping target
clusters correspond to adjacent source hexagons. -/
theorem marked_target_overlap_neighbor (C : MarkedAtlasFiniteInputs)
    (f : Position → State) (hf : GloballyLegal f) (c c' : Position) (hcc : c' ≠ c)
    (p : RealPoint) (hc : p ∈ markedTargetCarrier f hf c)
    (hc' : p ∈ markedTargetCarrier f hf c') :
    ∃ d, c' = sourceHexNeighbor c d := by
  have h1 : p ∈ C.wholePlaneHomeomorph f hf '' sourceHexCarrier c := by
    rwa [C.wholePlaneHomeomorph_image_source f hf c]
  have h2 : p ∈ C.wholePlaneHomeomorph f hf '' sourceHexCarrier c' := by
    rwa [C.wholePlaneHomeomorph_image_source f hf c']
  obtain ⟨x,hx,hxp⟩ := h1
  obtain ⟨y,hy,hyp⟩ := h2
  have hyx : y=x := (C.wholePlaneHomeomorph f hf).injective (hyp.trans hxp.symm)
  subst y
  exact sourceHex_intersection_neighbor hcc ⟨x,hx,hy⟩

/-- The complete raw and physical path laws give inverse agreement on every
actual overlap of neighboring placed clusters. -/
theorem fieldRawInverse_neighbor_agree
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (f : Position → State) (hf : GloballyLegal f)
    (hinter : MarkedNeighborIntersection f hf) (B : Position → RealPoint)
    (hB : ∀ c d, (physicalPathReal (f c) d).map (fun p => B c+p) =
      ((physicalPathReal (f (sourceHexNeighbor c d)) (opposite d)).map
        (fun p => B (sourceHexNeighbor c d)+p)).reverse)
    (c : Position) (d : Fin 6) (p : RealPoint)
    (hc : p ∈ markedTargetCarrier f hf c)
    (hc' : p ∈ markedTargetCarrier f hf (sourceHexNeighbor c d)) :
    fieldRawInverse f hf B c p = fieldRawInverse f hf B (sourceHexNeighbor c d) p := by
  obtain ⟨t,ht,hpath⟩ := hinter c d p hc hc'
  have hreverse := hpath.reverse
  rw [realDevelopedPath_glue,List.reverse_reverse] at hreverse
  rw [realDevelopedPath_eq] at hpath hreverse
  have hA := placedRawCoordinateInverse_boundary hbinding hfaces (f c).1 (f c).2 d
    (markedAnchor f hf c) (B c) t p hpath
  have hB' := placedRawCoordinateInverse_boundary hbinding hfaces
    (f (sourceHexNeighbor c d)).1 (f (sourceHexNeighbor c d)).2 (opposite d)
    (markedAnchor f hf (sourceHexNeighbor c d)) (B (sourceHexNeighbor c d)) (1-t) p hreverse
  have hB'' := hB'.reverse
  rw [←hB c d,show 1-(1-t)=t by ring] at hB''
  exact hA.unique hB''

/-- No inverse-overlap premise is assumed: it follows from the actual marked
whole-plane homeomorphism and the independently integrated physical paths. -/
theorem fieldRawInverse_agree (C : MarkedAtlasFiniteInputs)
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (f : Position → State) (hf : GloballyLegal f) (B : Position → RealPoint)
    (hB : ∀ c d, (physicalPathReal (f c) d).map (fun p => B c+p) =
      ((physicalPathReal (f (sourceHexNeighbor c d)) (opposite d)).map
        (fun p => B (sourceHexNeighbor c d)+p)).reverse)
    (c c' : Position) (p : RealPoint)
    (hc : p ∈ markedTargetCarrier f hf c) (hc' : p ∈ markedTargetCarrier f hf c') :
    fieldRawInverse f hf B c p = fieldRawInverse f hf B c' p := by
  by_cases he : c'=c
  · subst c'; rfl
  obtain ⟨d,rfl⟩ := marked_target_overlap_neighbor C f hf c c' he p hc hc'
  exact fieldRawInverse_neighbor_agree hbinding hfaces f hf
    (marked_neighbor_intersection_of_certificates C.neighborChecked C.neighborBinding f hf)
    B hB c d p hc hc'

end
end SpectreGeometry.ReversePhysicalClusterCharts
