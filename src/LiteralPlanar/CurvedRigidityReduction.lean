module

public import LiteralPlanar.CurvedSeedDecode

@[expose] public section


/-! Lightweight checked interface to the original homochiral hierarchy.
Both the original seed and planar rigidity are explicit hypotheses here;
ParentOccurrence is not assumed proved by this interface. -/
set_option autoImplicit false
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry SpectreGeometry.Deformation
universe u

def HomochiralCarrierPeriodRigidity : Prop :=
  ∀ {J : Type u} (q : J → EPlane ≃ᵢ EPlane),
    (∀ j, DirectPlacement (q j)) →
    (Pairwise fun i j => Disjoint (interior (q i '' euclideanBody))
      (interior (q j '' euclideanBody))) →
    (∀ x, ∃ j, x ∈ q j '' euclideanBody) →
    ∀ v : EPlane, CarrierCollectionPeriod q v → v = 0

theorem curved_period_eq_zero_of_seed_and_planar_rigidity
    (hseed : OriginalSeedStatement) (H : HomochiralCarrierPeriodRigidity.{u})
    {J : Type u} (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' LiteralPlanar.FanBounds.curvedBody)
    (hpack : Pairwise fun i j => Disjoint
      (interior (q i '' LiteralPlanar.FanBounds.curvedBody))
      (interior (q j '' LiteralPlanar.FanBounds.curvedBody)))
    (v : EPlane)
    (hperiod : Set.range (fun j => (fun x : EPlane => x+v) ''
      (q j '' LiteralPlanar.FanBounds.curvedBody)) =
      Set.range (fun j => q j '' LiteralPlanar.FanBounds.curvedBody)) : v = 0 := by
  by_contra hv
  obtain ⟨base,_hb⟩ := hcover 0
  obtain ⟨T,htransfer⟩ := curved_normalized_decode_of_original_seed hseed q hcover hpack base
  obtain ⟨hw,hp⟩ := htransfer v hv hperiod
  exact hw (H (fun j => (q j).trans (q base).symm)
    T.direct T.interiors_disjoint T.covers _ hp)

end
end LiteralPlanar.Forward
