module

public import SpectreClusters.StageDFinalModel
public import SpectreClusters.StageDHaloData

@[expose] public section


namespace SpectreClusters.StageD

def rowBasicsB (i : Row) : Bool :=
  decide (LegalClusterKind (rowKind i)) && ((rowNeighbors i).length == 6) &&
  (rowNeighbors i).all (fun p => decide (LegalClusterKind p.kind) &&
    !(clusterPoseEqB p (canonical (rowKind i)))) &&
  (haloOrder (rowKind i)).all (fun c => (rowNeighbors i).any
    (fun p => (clusterPlacementCells p).any (cellEqB c)))

end SpectreClusters.StageD
