module

public import LiteralPlanar.CurvedPhysicalDecode
public import LiteralPlanar.CurvedChirality
public import LiteralPlanar.CurvedCarrierPeriods
public import LiteralPlanar.AmbientNormalization

@[expose] public section


/-! Unrestricted physical curved tilings decode after one genuine ambient
frame normalization. The all-reflected case is included; an original nonzero
translation is transported by the inverse root frame's orthogonal linear map. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry SpectreGeometry.Deformation FanBounds
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem normalized_physical_curved_source {J : Type*} (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) (base : J) :
    SourceTiling (fun j => (q j).trans (q base).symm) := by
  obtain ⟨hc,hp⟩ := ambient_isometry_tiling curvedBody q (q base).symm hcover hpack
  obtain ⟨hs,hs'⟩ := physical_curved_tiling_to_source_tiling p T root
    (fun j => (q j).trans (q base).symm) hc hp
  exact ⟨normalized_curved_placements_direct p T root q hcover hpack base,hs,hs'⟩

theorem normalized_physical_curved_period {J : Type*} (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) (base : J) (v : EPlane) (hv : v ≠ 0)
    (hperiod : Set.range (fun j => (fun x : EPlane => x+v) '' (q j '' curvedBody)) =
      Set.range (fun j => q j '' curvedBody)) :
    (q base).symm.toRealLinearIsometryEquiv v ≠ 0 ∧
      CarrierCollectionPeriod (fun j => (q j).trans (q base).symm)
        ((q base).symm.toRealLinearIsometryEquiv v) := by
  refine ⟨ambient_isometry_nonzero_translation (q base).symm v hv,?_⟩
  apply curved_collection_period_to_source p T root
    (fun j => (q j).trans (q base).symm)
    (normalized_curved_placements_direct p T root q hcover hpack base)
  exact ambient_isometry_collection_period curvedBody q (q base).symm v hperiod

end
end LiteralPlanar.Forward
