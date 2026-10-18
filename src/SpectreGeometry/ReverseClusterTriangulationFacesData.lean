module

public import SpectreGeometry.ReverseClusterTriangulationCertificates

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

def separatesPacketsB (p q : PolygonPacket) (f : Constraint) : Bool :=
  verticesSatisfyB p.vertices [f] && verticesSatisfyB q.vertices [negConstraint f]

def supportsPacketFaceB (p q : PolygonPacket) (f : Constraint) : Bool :=
  separatesPacketsB p q f &&
    q.vertices.all (fun v => decide (edgeValue f v ≠ 0) || decide (v ∈ p.vertices)) &&
    p.vertices.any (fun v => decide (0 < edgeValue f v)) &&
    q.vertices.any (fun v => decide (edgeValue f v < 0))

def summedPacketSeparator (p q : PolygonPacket) : Constraint :=
  ((p.facets ++ q.facets.map negConstraint).filter (separatesPacketsB p q)).foldl addConstraint zeroConstraint

def pairPacketsFaceB (p q : PolygonPacket) (code : Nat) : Bool :=
  if code < 3 then supportsPacketFaceB p q (p.facets.getD code zeroConstraint)
  else if code < 6 then supportsPacketFaceB q p (q.facets.getD (code-3) zeroConstraint)
  else if code = 6 then supportsPacketFaceB p q (summedPacketSeparator p q)
  else supportsPacketFaceB q p (summedPacketSeparator q p)

def packetFaceRowB (p : PolygonPacket) : List PolygonPacket → List Nat → Bool
  | [], [] => true
  | q :: qs, c :: cs => pairPacketsFaceB p q c && packetFaceRowB p qs cs
  | _, _ => false

end SpectreGeometry.ReverseClusterTriangulation
