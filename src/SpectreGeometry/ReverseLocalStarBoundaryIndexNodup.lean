module

public import SpectreGeometry.ReverseClusterTriangulationData

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem all_boundary_indices_distinct : ∀ (k : Fin 9) (d : Fin 6),
    (boundaryIndices k d).Nodup := by
  decide

#print axioms all_boundary_indices_distinct
end SpectreGeometry.ReverseLocalStarOccurrences
