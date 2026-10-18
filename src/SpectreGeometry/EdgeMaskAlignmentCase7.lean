module

public import SpectreGeometry.SectorBoundaryRays

@[expose] public section

namespace SpectreGeometry
 theorem edge_complement_end_samples_case7 : ∀ (j : Fin 14) (k : Fin 12),
    ¬edgeSector j (directionAdd (directionInverse k) (edgeTurn 7)) →
    ¬edgeSector j (directionAdd (directionInverse k) (directionAdd (edgeTurn 7) 5)) →
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn 7) 6 := by decide
end SpectreGeometry
