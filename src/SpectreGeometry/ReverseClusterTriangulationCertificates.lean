module

public import SpectreGeometry.HalfplaneCertificateData
public import SpectreClusters.BodyBSPData

@[expose] public section


/-! Finite certificate language for common polygonal disk triangulations.
Every polygon is tied to explicit integer vertices and exact oriented facets.
This module contains no real geometric or tiling hypotheses. -/
namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

structure PolygonPacket where
  vertices : List Point
  facets : List Constraint
  scales : List Nat
  deriving Inhabited

def packetCheckedB (p : PolygonPacket) : Bool :=
  facetBindingB p.vertices p.facets p.scales && polygonPositiveB p.vertices &&
    (p.vertices.length == 3 || p.vertices.length == 4)

def familyFacets (ps : List PolygonPacket) : List (List Constraint) := ps.map (·.facets)

def familyCheckedB (ps : List PolygonPacket) : Bool := ps.all packetCheckedB

def coverFamilyB (targets : List (List Constraint)) :
    List PolygonPacket → List CoverTree → Bool
  | [], [] => true
  | p :: ps, t :: ts => checkTree (p.facets ++ [unitFacet]) targets t &&
      coverFamilyB targets ps ts
  | _, _ => false

def verticesSatisfyB (vs : List Point) (fs : List Constraint) : Bool :=
  fs.all fun f => vs.all fun v => decide (0 ≤ edgeValue f v)

def familyWithinB (ps : List PolygonPacket) (fs : List Constraint) : Bool :=
  ps.all fun p => verticesSatisfyB p.vertices fs

abbrev TriangleCode := Nat × Nat × Nat

def triangleIndices (t : TriangleCode) : List Nat := [t.1,t.2.1,t.2.2]
def triangleVertexList (vs : List Point) (t : TriangleCode) : List Point :=
  (triangleIndices t).map fun i => vs.getD i (0,0)

def faceSupportB (vs : List Point) (t u : TriangleCode) (e : Nat) : Bool :=
  let ids := triangleIndices t
  let a := ids.getD (e % 3) 0
  let b := ids.getD ((e+1) % 3) 0
  let f := edgeFacet (vs.getD a (0,0)) (vs.getD b (0,0))
  (triangleIndices u).all fun v =>
    decide (edgeValue f (vs.getD v (0,0)) ≤ 0) &&
      (decide (edgeValue f (vs.getD v (0,0)) ≠ 0) || decide (v=a ∨ v=b))

def pairFaceB (vs : List Point) (t u : TriangleCode) (code : Nat) : Bool :=
  if code < 3 then faceSupportB vs t u code else faceSupportB vs u t (code-3)

def faceRowB (vs : List Point) (t : TriangleCode) : List TriangleCode → List Nat → Bool
  | [], [] => true
  | u :: us, c :: cs => pairFaceB vs t u c && faceRowB vs t us cs
  | _, _ => false

end SpectreGeometry.ReverseClusterTriangulation
