module

public import SpectreGeometry.ReverseLocalStarFastData
public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreFinite.HexSearch ReverseClusterTriangulation

def InteriorFastCertificate (big : Bool) (v : Nat) : Prop :=
  v < (targetVertices (kindMark big)).length → ¬IsBoundaryIndex (kindMark big) v →
    occurrenceStructuralB (fastLocalStar (kindMark big,0) v) (interiorCode big v 0) = true
end SpectreGeometry.ReverseLocalStarOccurrences
