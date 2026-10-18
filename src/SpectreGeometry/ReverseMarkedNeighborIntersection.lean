module

public import SpectreGeometry.ReverseMarkedInverseAgreement
public import SpectreGeometry.ReverseClusterNeighborBindingData
public import SpectreGeometry.ReverseNeighborCarrierMotion
public import SpectreGeometry.ReverseIntegerPathCarrier

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseClusterNeighborCells ReverseClusterNeighborBinding
open ReverseClusterVertexIntersections

/-- The finite 35-placement carrier certificates and the actual marked-pair
lookup binding imply the required whole-neighbor path intersection statement. -/
theorem marked_neighbor_intersection_of_certificates
    (hchecked : ∀ i : Fin 35, configurationCheckedB (configuration i) = true)
    (hbinding : ∀ k r, MarkedConfigurationCertificate k r)
    (f : Position → State) (hf : GloballyLegal f) : MarkedNeighborIntersection f hf := by
  intro c d y hy hy'
  let a := f c
  let b := f (sourceHexNeighbor c d)
  have hm : sideMatch a b d := field_sideMatch f hf c d
  obtain ⟨hcode,hbind⟩ := hbinding a.1 a.2 b.1 b.2 d hm
  let i : Fin 35 := ⟨classCode a b d,hcode⟩
  let cfg := configuration i
  change cfg.rootKind = clusterOfMark a.1 ∧ cfg.neighborKind = clusterOfMark b.1 ∧
    cfg.turn = sideTurn a.2 b.2 ∧
    lattice cfg.centerShift = SpectreClusters.rotate (inverseTurn a.2) (vertexDelta a b d) ∧
    cfg.sharedPath = (statePath a d).map (SpectreClusters.rotate (inverseTurn a.2)) at hbind
  obtain ⟨hk,hk',hr,hs,hpath⟩ := hbind
  let H := axialMotionHomeomorph a.2 (markedAnchor f hf c)
  have hroot : H '' rootCarrier cfg = markedTargetCarrier f hf c := by
    rw [rootCarrier_eq_rawClusterBody,hk]
    rfl
  have hshift : gridRotation a.2 (integerPoint (lattice cfg.centerShift)) =
      integerPoint (vertexDelta a b d) := by
    rw [hs,integerPoint_rotate,gridRotation_inverse_cancel]
  have hturn : rotateTurn a.2 (sideTurn a.2 b.2) = b.2 := by
    have hall : ∀ r s : Fin 6, rotateTurn r (sideTurn r s) = s := by decide
    exact hall a.2 b.2
  have hanchor : markedAnchor f hf (sourceHexNeighbor c d) =
      markedAnchor f hf c+integerPoint (vertexDelta a b d) := markedAnchor_step f hf c d
  have hneighbor : H '' neighborCarrier cfg = markedTargetCarrier f hf (sourceHexNeighbor c d) := by
    rw [neighborCarrier_eq_motion_image,hk',Set.image_image]
    change (fun q => H (gridMotion cfg.turn (integerPoint (lattice cfg.centerShift)) q)) ''
        rawClusterBody (clusterOfMark b.1) =
      (fun q => markedAnchor f hf (sourceHexNeighbor c d)+gridRotation b.2 q) ''
        rawClusterBody (clusterOfMark b.1)
    congr 1
    funext q
    change axialMotionHomeomorph a.2 (markedAnchor f hf c)
      (gridMotion cfg.turn (integerPoint (lattice cfg.centerShift)) q) = _
    rw [axialMotionHomeomorph_gridMotion,hr,hshift,hturn,←hanchor]
  have hyroot : y ∈ H '' rootCarrier cfg := by rwa [hroot]
  have hyneighbor : y ∈ H '' neighborCarrier cfg := by rwa [hneighbor]
  obtain ⟨z,hz,hzy⟩ := hyroot
  obtain ⟨z',hz',hz'y⟩ := hyneighbor
  have hzz : z'=z := H.injective (hz'y.trans hzy.symm)
  subst z'
  have hp := configurationCheckedB_carriers_inter_subset cfg (hchecked i) ⟨hz,hz'⟩
  rw [pathCarrier_eq_polygonalPathCarrier] at hp
  obtain ⟨t,ht,hparam⟩ := (mem_polygonalPathCarrier_iff (cfg.sharedPath.map integerPoint) z).mp hp
  have himage := hparam.affineMap (gridMotion a.2 (markedAnchor f hf c))
  have hpathImage : (cfg.sharedPath.map integerPoint).map (gridMotion a.2 (markedAnchor f hf c)) =
      realDevelopedPath f hf c d := by
    rw [realDevelopedPath_eq,hpath]
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply,gridMotion_apply,integerPoint_rotate,gridRotation_inverse_cancel]
  rw [hpathImage] at himage
  change PathParameter (realDevelopedPath f hf c d) t (H z) at himage
  rw [hzy] at himage
  exact ⟨t,ht,himage⟩

end
end SpectreGeometry.ReverseExistence
