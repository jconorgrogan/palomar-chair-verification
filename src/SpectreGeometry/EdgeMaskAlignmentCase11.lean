module

public import SpectreGeometry.SectorBoundaryRays

@[expose] public section

namespace SpectreGeometry
 theorem edge_complement_end_samples_case11 : ∀ (j : Fin 14) (k : Fin 12),
    ¬edgeSector j (directionAdd (directionInverse k) (edgeTurn 11)) →
    ¬edgeSector j (directionAdd (directionInverse k) (directionAdd (edgeTurn 11) 5)) →
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn 11) 6 := by decide
end SpectreGeometry
