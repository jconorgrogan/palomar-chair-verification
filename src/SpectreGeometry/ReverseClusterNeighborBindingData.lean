module

public import SpectreGeometry.ReverseClusterVertexIntersectionsData
public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreClusters.ReverseClusterBoundaryGlueData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterVertexIntersections ReverseClusterNeighborCells
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def MarkedConfigurationCertificate (k : Fin 9) (r : Fin 6) : Prop :=
  ∀ (bk : Fin 9) (br d : Fin 6), sideMatch (k,r) (bk,br) d →
    classCode (k,r) (bk,br) d < 35 ∧
    let c := configurations.getD (classCode (k,r) (bk,br) d) ⟨.t7h,.t7h,0,(0,0),[]⟩
    c.rootKind = clusterOfMark k ∧ c.neighborKind = clusterOfMark bk ∧
    c.turn = sideTurn r br ∧
    lattice c.centerShift = SpectreClusters.rotate (inverseTurn r) (vertexDelta (k,r) (bk,br) d) ∧
    c.sharedPath = (statePath (k,r) d).map (SpectreClusters.rotate (inverseTurn r))
end SpectreGeometry.ReverseClusterNeighborBinding
