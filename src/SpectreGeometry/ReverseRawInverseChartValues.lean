module

public import SpectreGeometry.ReverseRawInverseChartReal
public import SpectreGeometry.ReverseInverseAffine
public import SpectreGeometry.DeformationHomeomorphismPhysical

@[expose] public section


namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section
open Set SpectreClusters Deformation ReverseExistence

def rawPiece (big : Bool) (n : Nat) : HTPlacement :=
  (pieces big).getD n ⟨.turtle,0,(0,0)⟩

def rawInverseSourceAnchor (big : Bool) (n : Nat) (i : Fin 12) : EPlane :=
  euclideanCoordinates (physicalOrigin big n +
    SpectreGeometry.rotate (physicalTurn (rawPiece big n)) (realVertex (triangle i).1))

def rawInverseTargetAnchor (big : Bool) (n : Nat) (i : Fin 12) : EPlane :=
  euclideanCoordinates (rawTileTargetOrigin (rawPiece big n) +
    realDeformedVertex (physicalTurn (rawPiece big n)) (triangle i).1)

/-- The real inverse chart uses the first triangle vertex as its affine base,
with the source and target translations kept distinct. -/
def rawPieceInverseChart (big : Bool) (n : Nat) (i : Fin 12) : EPlane ≃ₜ EPlane :=
  inverseAffineChart (physicalTurn (rawPiece big n)) i
    (rawInverseSourceAnchor big n i) (rawInverseTargetAnchor big n i)

/-- Every inverse-chart vertex is exactly the independently certified proper-P
placement vertex of its literal raw piece. -/
theorem rawPieceInverseChart_vertex (big : Bool) (n : Fin 9)
    (hn : n.val < (pieces big).length) (i : Fin 12) (v : Fin 3) :
    rawPieceInverseChart big n.val i
      (euclideanCoordinates (rawFrame (integerPoint
        (rawPlacedVertex (rawPiece big n.val)
          (physicalIndex (rawPiece big n.val).kind (triangleIndex i v)))))) =
      euclideanCoordinates (quarterPoint (vertexImage4 big
        (rawPlacedVertex (rawPiece big n.val)
          (physicalIndex (rawPiece big n.val).kind (triangleIndex i v))))) := by
  let p := rawPiece big n.val
  let k := physicalTurn p
  have hf := affineEuclidean_realFormula k i (physicalOrigin big n.val)
    (rawTileTargetOrigin p) (SpectreGeometry.rotate k (realVertex (triangleIndex i v)))
  change affineEuclidean k i (rawInverseSourceAnchor big n.val i)
    (rawInverseTargetAnchor big n.val i)
    (euclideanCoordinates (physicalOrigin big n.val +
      SpectreGeometry.rotate k (realVertex (triangleIndex i v)))) = _ at hf
  rw [←sourceAffine_apply,sourceAffine_vertex] at hf
  rw [←raw_placed_vertex_target p (triangleIndex i v)] at hf
  have hv := literal_piece_vertex_real big n hn
    (physicalIndex p.kind (triangleIndex i v))
  change quarterPoint (vertexImage4 big
    (rawPlacedVertex p (physicalIndex p.kind (triangleIndex i v)))) =
      physicalOrigin big n.val + SpectreGeometry.rotate k
        (realVertex (physicalIndex p.kind (physicalIndex p.kind (triangleIndex i v)))) at hv
  rw [physicalIndex_involutive] at hv
  change inverseAffineChart k i (rawInverseSourceAnchor big n.val i)
    (rawInverseTargetAnchor big n.val i) _ = _
  rw [←hf,inverse_affine_chart,hv]

end
end SpectreGeometry.ReversePhysicalCluster
