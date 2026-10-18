module

public import SpectreGeometry.SectorBoundaryRays

@[expose] public section

namespace SpectreGeometry
 theorem edge_complement_end_samples_case3 : ∀ (j : Fin 14) (k : Fin 12),
    ¬edgeSector j (directionAdd (directionInverse k) (edgeTurn 3)) →
    ¬edgeSector j (directionAdd (directionInverse k) (directionAdd (edgeTurn 3) 5)) →
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn 3) 6 := by decide
end SpectreGeometry
