module

public import SpectreGeometry.ReverseMarkedNeighborIntersection
public import SpectreGeometry.ReverseNeighborCarrierInteriors

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseClusterNeighborCells ReverseClusterNeighborBinding
open ReverseClusterVertexIntersections

/-- Every actual neighboring pair has disjoint ambient carrier interiors,
by the same finite placement and rotation binding used for inverse agreement. -/
theorem marked_neighbor_interiors_disjoint_of_certificates
    (hchecked : ∀ i : Fin 35, configurationCheckedB (configuration i) = true)
    (hbinding : ∀ k r, MarkedConfigurationCertificate k r)
    (f : Position → State) (hf : GloballyLegal f) (c : Position) (d : Fin 6) :
    Disjoint (interior (markedTargetCarrier f hf c))
      (interior (markedTargetCarrier f hf (sourceHexNeighbor c d))) := by
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
  have hd := configurationCheckedB_carrier_interiors_disjoint cfg (hchecked i)
  rw [←hroot,←hneighbor,←H.image_interior,←H.image_interior]
  exact Set.disjoint_image_of_injective H.injective hd

end
end SpectreGeometry.ReverseExistence
