module

public import LiteralPlanar.CurvedPlacementRigidity
public import SpectreGeometry.DeformationHomeomorphismCarrierPeriod

@[expose] public section


/-! Unlabelled curved-carrier periods determine the actual proper placements,
then preserve the same translation vector for the straight P carriers. This
uses intrinsic polynomial-arc rigidity, not an arbitrary homeomorphism claim. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry SpectreGeometry.Deformation FanBounds
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem curved_direct_placement_eq (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g)
    (hbody : f '' curvedBody = g '' curvedBody) : f = g := by
  have hs : (f.trans g.symm) '' curvedBody = curvedBody := by
    calc
      (f.trans g.symm) '' curvedBody = g.symm '' (f '' curvedBody) := by
        rw [Set.image_image]
        rfl
      _ = g.symm '' (g '' curvedBody) := by rw [hbody]
      _ = curvedBody := by
        rw [Set.image_image]
        simp only [IsometryEquiv.symm_apply_apply,Set.image_id,Set.image_id']
  have hh := curved_direct_self_isometry_rigid p T root (f.trans g.symm)
    (direct_relative f g hf hg) hs
  apply IsometryEquiv.ext
  intro x
  have he := congrArg g (hh x)
  simpa only [IsometryEquiv.trans_apply,IsometryEquiv.apply_symm_apply] using he

theorem curved_carrier_translation_recovers_placement (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (v : EPlane)
    (hbody : g '' curvedBody = (fun x : EPlane => x+v) '' (f '' curvedBody)) :
    g = translatedPlacement f v := by
  apply curved_direct_placement_eq p T root g (translatedPlacement f v) hg
    (translatedPlacement_direct f hf v)
  rw [hbody,Set.image_image]
  rfl

theorem same_translation_source_carriers (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (v : EPlane)
    (hbody : g '' curvedBody = (fun x : EPlane => x+v) '' (f '' curvedBody)) :
    g '' euclideanBody = (fun x : EPlane => x+v) '' (f '' euclideanBody) := by
  rw [curved_carrier_translation_recovers_placement p T root f g hf hg v hbody,
    Set.image_image]
  rfl

/-- The carrier collection is unlabelled, and the actual nonzero period vector
is unchanged when the ambient frame is kept fixed. -/
theorem curved_collection_period_to_source {J : Type*}
    (q : J → EPlane ≃ᵢ EPlane) (hdirect : ∀ j, DirectPlacement (q j)) (v : EPlane)
    (hperiod : Set.range (fun j => (fun x : EPlane => x+v) '' (q j '' curvedBody)) =
      Set.range (fun j => q j '' curvedBody)) : CarrierCollectionPeriod q v := by
  apply Set.Subset.antisymm
  · rintro S ⟨j,rfl⟩
    have hmem : (fun x : EPlane => x+v) '' (q j '' curvedBody) ∈
        Set.range (fun k => q k '' curvedBody) := by
      rw [←hperiod]
      exact ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := hmem
    exact ⟨k,same_translation_source_carriers p T root (q j) (q k)
      (hdirect j) (hdirect k) v hk⟩
  · rintro S ⟨j,rfl⟩
    have hmem : q j '' curvedBody ∈
        Set.range (fun k => (fun x : EPlane => x+v) '' (q k '' curvedBody)) := by
      rw [hperiod]
      exact ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := hmem
    exact ⟨k,(same_translation_source_carriers p T root (q k) (q j)
      (hdirect k) (hdirect j) v hk.symm).symm⟩

end
end LiteralPlanar.Forward
