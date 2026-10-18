module

public import SpectreGeometry.WholeEdgeRegistration

@[expose] public section


/-! The explicit hypotheses for the forward curved transfer. No existence
premise is discharged here; the closed source existence theorem is separate. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry

structure SourceTiling {I : Type*} (p : I → EPlane ≃ᵢ EPlane) : Prop where
  direct : ∀ i, DirectPlacement (p i)
  covers : ∀ x : EPlane, ∃ i, x ∈ p i '' euclideanBody
  interiors_disjoint : Pairwise fun i j =>
    Disjoint (interior (p i '' euclideanBody)) (interior (p j '' euclideanBody))

theorem source_locallyFinite {I : Type*} (p : I → EPlane ≃ᵢ EPlane)
    (T : SourceTiling p) : LocallyFinite (fun i => p i '' euclideanBody) :=
  CompactPacking.polygon_packing_locallyFinite p T.interiors_disjoint

/-- The exact endpoint registration used by the polynomial pasting recipe is
proved from proper placements, covering and interior packing. -/
theorem source_whole_unit_edge_registration {I : Type*}
    (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I) (e : Fin 14) :
    ∃ i, i ≠ root ∧ ∃ j : Fin 14,
      (p root (euclideanVertex e) = p i (euclideanVertex j) ∧
        p root (euclideanVertex (next e)) = p i (euclideanVertex (next j))) ∨
      (p root (euclideanVertex e) = p i (euclideanVertex (next j)) ∧
        p root (euclideanVertex (next e)) = p i (euclideanVertex j)) :=
  homochiral_whole_unit_edge_registration p T.direct T.interiors_disjoint T.covers root e

end
end LiteralPlanar.Forward
