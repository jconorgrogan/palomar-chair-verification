module

public import SpectreGeometry.ReversePhysicalPieceImage
public import SpectreGeometry.ReversePhysicalWholePlaneInverse
public import SpectreGeometry.ReverseProperPPlacements
public import SpectreGeometry.ReverseMarkedPieceTiling
public import SpectreGeometry.SectorRotations

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence Deformation ReverseExistence
open ReversePhysicalCluster ReverseClusterTriangulation SpectreFinite SpectreFinite.HexSearch

/-- The exact proper physical pose of a raw piece inside a placed cluster. -/
def placedPiecePose (big : Bool) (n : Nat) (r : Fin 6) (b : RealPoint) : EPlane ≃ᵢ EPlane :=
  properPPlacement (directionAdd (physicalRootTurn r) (physicalTurn (rawPiece big n)))
    (b + SpectreGeometry.rotate (physicalRootTurn r) (physicalOrigin big n))

theorem placedPiecePose_direct (big : Bool) (n : Nat) (r : Fin 6) (b : RealPoint) :
    DirectPlacement (placedPiecePose big n r b) := properPPlacement_direct _ _

private theorem rawFrame_axialMotion (r : Fin 6) (a p : RealPoint) :
    rawEuclideanFrame (axialMotionHomeomorph r a p) =
      rawEuclideanFrame a + physicalRotation r (rawEuclideanFrame p) := by
  change coordinateLinearEquiv (rawFrame (a+gridRotation r p)) =
    coordinateLinearEquiv (rawFrame a) + physicalRotation r (euclideanCoordinates (rawFrame p))
  rw [rawFrame.map_add,coordinateLinearEquiv.map_add,physicalRotation_coordinates,rawFrame_gridRotation]
  rfl

/-- An entire placed raw piece maps onto one explicitly proper P placement. -/
theorem placedClusterInverse_image_piece
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (big : Bool) (n : Fin 9) (hn : n.val < (pieces big).length)
    (r : Fin 6) (a b : RealPoint) :
    placedClusterInverse big r a b ''
      (rawEuclideanFrame '' (axialMotionHomeomorph r a '' placementKiteBody (rawPiece big n.val))) =
        placedPiecePose big n.val r b '' euclideanBody := by
  have hpoint (x : RealPoint) : placedClusterInverse big r a b
      (rawEuclideanFrame (axialMotionHomeomorph r a x)) =
      euclideanCoordinates b + physicalRotation r (rawClusterInverseMap big x) := by
    rw [rawFrame_axialMotion]
    simp only [placedClusterInverse,_root_.add_sub_cancel_left,
      LinearIsometryEquiv.symm_apply_apply,Homeomorph.symm_apply_apply]
  rw [image_image,image_image]
  have himg : (fun x => placedClusterInverse big r a b
      (rawEuclideanFrame (axialMotionHomeomorph r a x))) '' placementKiteBody (rawPiece big n.val) =
      (fun x => euclideanCoordinates b + physicalRotation r x) ''
        (rawClusterInverseMap big '' placementKiteBody (rawPiece big n.val)) := by
    rw [image_image]
    apply Set.image_congr
    intro x hx
    exact hpoint x
  rw [himg,rawClusterInverseMap_image_piece hbinding hfaces big n hn,image_image]
  change _ = placedPiecePose big n.val r b '' (euclideanCoordinates '' polygonBody)
  rw [image_image]
  apply Set.image_congr
  intro x hx
  rw [physicalPieceAffine_apply,physicalRotation_coordinates,placedPiecePose,
    properPPlacement_apply]
  change coordinateLinearEquiv b + coordinateLinearEquiv
    (SpectreGeometry.rotate (physicalRootTurn r)
      (physicalOrigin big n.val + SpectreGeometry.rotate (physicalTurn (rawPiece big n.val)) x)) =
    coordinateLinearEquiv ((b + SpectreGeometry.rotate (physicalRootTurn r) (physicalOrigin big n.val)) +
      SpectreGeometry.rotate (directionAdd (physicalRootTurn r) (physicalTurn (rawPiece big n.val))) x)
  rw [←coordinateLinearEquiv.map_add,rotate_add_vector,SpectreGeometry.rotate_add]
  congr 1
  exact (_root_.add_assoc _ _ _).symm


def markedPiecePose (f : Position → State) (B : Position → RealPoint)
    (i : MarkedPieceIndex f) : EPlane ≃ᵢ EPlane :=
  placedPiecePose ((f i.1).1.val != 0) i.2.val (f i.1).2 (B i.1)

theorem markedPiecePose_direct (f : Position → State) (B : Position → RealPoint)
    (i : MarkedPieceIndex f) : DirectPlacement (markedPiecePose f B i) :=
  placedPiecePose_direct _ _ _ _

/-- The whole-plane physical map sends each actual raw piece exactly onto
its explicit proper P pose. Global coverage and disjointness are separate
consequences of transporting the already constructed raw-piece tiling. -/
theorem physicalFieldHomeomorph_image_piece (C : MarkedAtlasFiniteInputs)
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (f : Position → State) (hf : GloballyLegal f) (B : Position → RealPoint)
    (hB : ∀ c d, (physicalPathReal (f c) d).map (fun p => B c+p) =
      ((physicalPathReal (f (sourceHexNeighbor c d)) (opposite d)).map
        (fun p => B (sourceHexNeighbor c d)+p)).reverse)
    (i : MarkedPieceIndex f) :
    physicalFieldHomeomorph C hbinding hfaces f hf B hB ''
      (rawEuclideanFrame '' markedPieceCarrier f hf i) =
        markedPiecePose f B i '' euclideanBody := by
  have he : pieces ((f i.1).1.val != 0) = clusterPieces (clusterOfMark (f i.1).1) := by
    by_cases h : (f i.1).1.val=0 <;> simp [pieces,clusterOfMark,h]
  have hn : i.2.val < (pieces ((f i.1).1.val != 0)).length := by
    rw [he]
    exact i.2.isLt
  have hlen : (pieces ((f i.1).1.val != 0)).length ≤ 9 := by
    generalize ((f i.1).1.val != 0) = big
    cases big <;> decide
  have hcarrier : markedPieceCarrier f hf i =
      axialMotionHomeomorph (f i.1).2 (markedAnchor f hf i.1) ''
        placementKiteBody (rawPiece ((f i.1).1.val != 0) i.2.val) := by
    simp only [markedPieceCarrier,placedClusterPiece,rawPiece,he,
      List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.2.isLt,
      Option.getD_some,List.get_eq_getElem]
  have hmap : physicalFieldHomeomorph C hbinding hfaces f hf B hB ''
      (rawEuclideanFrame '' markedPieceCarrier f hf i) =
      placedClusterInverse ((f i.1).1.val != 0) (f i.1).2
        (markedAnchor f hf i.1) (B i.1) ''
          (rawEuclideanFrame '' markedPieceCarrier f hf i) := by
    apply Set.image_congr
    rintro x ⟨q,hq,rfl⟩
    apply physicalFieldHomeomorph_on_cluster C hbinding hfaces f hf B hB i.1
    refine ⟨q,?_,rfl⟩
    exact placedClusterPiece_subset _ _ _ i.2 hq
  rw [hmap,hcarrier]
  exact placedClusterInverse_image_piece hbinding hfaces _ ⟨i.2.val,by omega⟩ hn _ _ _

end
end SpectreGeometry.ReversePhysicalClusterCharts
