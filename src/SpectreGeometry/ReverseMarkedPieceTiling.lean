module

public import SpectreGeometry.ReverseMarkedWholePlaneHomeomorphism
public import SpectreGeometry.ReversePlacedClusterPieces

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch

abbrev MarkedPieceIndex (f : Position → State) :=
  (c : Position) × ClusterPieceIndex (clusterOfMark (f c).1)

def markedPieceCarrier (f : Position → State) (hf : GloballyLegal f)
    (i : MarkedPieceIndex f) : Set RealPoint :=
  placedClusterPiece (clusterOfMark (f i.1).1) (f i.1).2 (markedAnchor f hf i.1) i.2

namespace MarkedAtlasFiniteInputs
variable (C : MarkedAtlasFiniteInputs) (f : Position → State) (hf : GloballyLegal f)
include C

theorem marked_pieces_cover (x : RealPoint) :
    ∃ i : MarkedPieceIndex f, x ∈ markedPieceCarrier f hf i := by
  exact carrier_refinement_covers (markedTargetCarrier f hf)
    (fun c i => placedClusterPiece (clusterOfMark (f c).1) (f c).2 (markedAnchor f hf c) i)
    (C.marked_carriers_cover f hf)
    (fun c => placedClusterCarrier_eq_pieces _ _ _) x

theorem marked_pieces_interiors_disjoint :
    Pairwise (fun i j : MarkedPieceIndex f => Disjoint
      (interior (markedPieceCarrier f hf i)) (interior (markedPieceCarrier f hf j))) :=
  carrier_refinement_interiors_disjoint (markedTargetCarrier f hf)
    (fun c i => placedClusterPiece (clusterOfMark (f c).1) (f c).2 (markedAnchor f hf c) i)
    (C.marked_carriers_interiors_disjoint f hf)
    (fun c i => placedClusterPiece_subset _ _ _ i)
    (fun c => placedClusterPiece_interiors_disjoint _ _ _)

theorem marked_pieces_locallyFinite : LocallyFinite (markedPieceCarrier f hf) :=
  locallyFinite_sigma_refinement (markedTargetCarrier f hf)
    (fun c i => placedClusterPiece (clusterOfMark (f c).1) (f c).2 (markedAnchor f hf c) i)
    (C.marked_carriers_locallyFinite f hf)
    (fun c i => placedClusterPiece_subset _ _ _ i)

end MarkedAtlasFiniteInputs
end
end SpectreGeometry.ReverseExistence
