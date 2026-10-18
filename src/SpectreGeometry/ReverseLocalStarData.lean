module

public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStars
open HalfplaneCertificate ReverseClusterTriangulation

def starBoxFacets : List Constraint := [(0,1,1),(-1,0,1),(0,-1,1),(1,0,1),(0,0,1)]

def StarCertificate (ps : List PolygonPacket) (tree : CoverTree) (rows : List (List Nat)) : Prop :=
  familyCheckedB ps = true ∧ checkTree starBoxFacets (familyFacets ps) tree = true ∧
    ∀ i : Fin ps.length, packetFaceRowB (ps.getD i.val default) (ps.take i.val)
      (rows.getD i.val []) = true
end SpectreGeometry.ReverseLocalStars
