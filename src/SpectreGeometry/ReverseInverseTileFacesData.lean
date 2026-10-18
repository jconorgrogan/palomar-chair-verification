module

public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section

namespace SpectreGeometry.ReverseInverseTile
open SpectreClusters SpectreClusters.BodyBSP ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def canonicalPacket (kind : HTKind) (i : Fin 12) : PolygonPacket :=
  ⟨(targetVertexLists kind).getD i.val [],(targetFacets kind).getD i.val [],
    (targetFacetScales kind).getD i.val []⟩
def canonicalPackets (kind : HTKind) : List PolygonPacket :=
  (List.finRange 12).map (canonicalPacket kind)
def canonicalFaceRows : HTKind → List (List Nat)
  | .hat => [[], [1], [2, 2], [0, 0, 0], [0, 0, 2, 1], [2, 2, 1, 1, 1], [3, 3, 2, 2, 2, 3], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 2, 0, 0, 2, 1, 1], [2, 2, 2, 2, 2, 2, 1, 1, 1, 1], [3, 3, 1, 1, 1, 1, 1, 3, 4, 1, 1]]
  | .turtle => [[], [1], [2, 4], [0, 0, 0], [2, 3, 2, 1], [2, 2, 1, 1, 1], [0, 0, 3, 2, 3, 0], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 2, 0, 0, 2, 1, 1], [2, 2, 2, 3, 2, 2, 1, 1, 1, 1], [3, 5, 1, 1, 1, 1, 1, 3, 3, 1, 1]]
theorem canonicalPackets_checked : ∀ kind : HTKind,
    familyCheckedB (canonicalPackets kind) = true := by intro kind; cases kind <;> decide
theorem canonicalPackets_vertices : ∀ kind : HTKind,
    (canonicalPackets kind).map PolygonPacket.vertices = targetVertexLists kind := by
  intro kind; cases kind <;> decide
theorem canonicalPackets_length : ∀ kind : HTKind, (canonicalPackets kind).length = 12 := by
  intro kind; rfl
theorem canonical_face_rows : ∀ kind : HTKind, ∀ i : Fin 12,
    packetFaceRowB (canonicalPacket kind i) ((canonicalPackets kind).take i.val)
      ((canonicalFaceRows kind).getD i.val []) = true := by
  intro kind; cases kind <;> decide
end SpectreGeometry.ReverseInverseTile
