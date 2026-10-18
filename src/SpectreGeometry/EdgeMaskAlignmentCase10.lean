module

public import SpectreGeometry.SectorBoundaryRays

@[expose] public section

namespace SpectreGeometry
 theorem edge_complement_end_samples_case10 : ∀ (j : Fin 14) (k : Fin 12),
    ¬edgeSector j (directionAdd (directionInverse k) (edgeTurn 10)) →
    ¬edgeSector j (directionAdd (directionInverse k) (directionAdd (edgeTurn 10) 5)) →
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn 10) 6 := by decide
end SpectreGeometry
