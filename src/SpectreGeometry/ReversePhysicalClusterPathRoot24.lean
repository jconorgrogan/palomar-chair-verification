module

public import SpectreGeometry.ReversePhysicalClusterPathsData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
open SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem physical_boundary_root_2_4 :
    ∀ (j : Fin 9) (t : Fin 6) (d : Fin 6), sideMatch (2,4) (j,t) d →
    physicalDelta4 (2,4) (j,t) d =
      ExactPoint.sub (physicalStateCorner4 (2,4) (rotateTurn 1 d))
        (physicalStateCorner4 (j,t) (opposite d)) ∧
    physicalStatePath4 (2,4) d =
      ((physicalStatePath4 (j,t) (opposite d)).reverse).map
        (ExactPoint.add (physicalDelta4 (2,4) (j,t) d)) := by decide
end SpectreGeometry.ReversePhysicalCluster
