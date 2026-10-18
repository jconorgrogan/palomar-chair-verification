module

public import SpectreGeometry.SectorBoundaryRays

@[expose] public section

namespace SpectreGeometry
 theorem edge_complement_end_samples_case1 : ∀ (j : Fin 14) (k : Fin 12),
    ¬edgeSector j (directionAdd (directionInverse k) (edgeTurn 1)) →
    ¬edgeSector j (directionAdd (directionInverse k) (directionAdd (edgeTurn 1) 5)) →
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn 1) 6 := by decide
end SpectreGeometry
