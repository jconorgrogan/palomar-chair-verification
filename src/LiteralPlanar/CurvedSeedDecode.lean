module

public import LiteralPlanar.CurvedNormalizedDecode
public import LiteralPlanar.ForwardSeedTransfer

@[expose] public section


/-! Exact original-seed interface for unrestricted curved reverse decoding.
No contact registration, coverage transfer, or chirality premise is supplied.
The original seed remains explicit until its separately checked closed application. -/
set_option autoImplicit false
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry SpectreGeometry.Deformation
universe u

theorem curved_normalized_decode_of_original_seed (hseed : OriginalSeedStatement)
    {J : Type u} (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' LiteralPlanar.FanBounds.curvedBody)
    (hpack : Pairwise fun i j => Disjoint
      (interior (q i '' LiteralPlanar.FanBounds.curvedBody))
      (interior (q j '' LiteralPlanar.FanBounds.curvedBody))) (base : J) :
    SourceTiling (fun j => (q j).trans (q base).symm) ∧
    ∀ v : EPlane, v ≠ 0 →
      (Set.range (fun j => (fun x : EPlane => x+v) ''
        (q j '' LiteralPlanar.FanBounds.curvedBody)) =
        Set.range (fun j => q j '' LiteralPlanar.FanBounds.curvedBody)) →
      (q base).symm.toRealLinearIsometryEquiv v ≠ 0 ∧
        CarrierCollectionPeriod (fun j => (q j).trans (q base).symm)
          ((q base).symm.toRealLinearIsometryEquiv v) := by
  obtain ⟨I,p,hd,hc,hp,_hl⟩ := hseed
  let T : SourceTiling p := ⟨hd,hc,hp⟩
  obtain ⟨root,_hr⟩ := hc 0
  exact ⟨normalized_physical_curved_source p T root q hcover hpack base,
    fun v hv hperiod => normalized_physical_curved_period p T root q
      hcover hpack base v hv hperiod⟩

end
end LiteralPlanar.Forward
