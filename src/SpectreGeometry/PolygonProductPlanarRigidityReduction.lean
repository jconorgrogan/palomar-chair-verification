module

public import SpectreGeometry.PolygonProductFactorPeriods

@[expose] public section


/-! A lightweight interface for the final rigidity application. The planar
rigidity proposition is explicit here and is to be supplied by the separately
checked ParentOccurrence-conditional physical hierarchy theorem. -/
namespace SpectreGeometry
noncomputable section
open Set

def HomochiralPlanarCarrierPeriodRigidity : Prop :=
  ∀ {κ : Type} (g : κ → EPlane ≃ᵢ EPlane),
    (∀ k, DirectPlacement (g k)) →
    (Pairwise fun i j => Disjoint (interior (g i '' euclideanBody))
      (interior (g j '' euclideanBody))) →
    (∀ x, ∃ k, x ∈ g k '' euclideanBody) →
    ∀ w : EPlane,
      (Set.range (fun k => (fun x : EPlane => x+w) '' (g k '' euclideanBody)) =
        Set.range (fun k => g k '' euclideanBody)) → w = 0

theorem physical_polygon_product_period_eq_zero_of_planar_rigidity
    (H : HomochiralPlanarCarrierPeriodRigidity)
    {ι : Type*} {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (v : EFour)
    (hperiod : Set.range (fun i => (fun z : EFour => z+v) '' (f i '' polygonProductKeyBody)) =
      Set.range (fun i => f i '' polygonProductKeyBody)) : v = 0 := by
  by_contra hv
  obtain ⟨κ,g,w,hw,hdirect,hdisjoint,hcover,hplanar⟩ :=
    physical_nonzero_product_period_has_planar_factor T v hv hperiod
  exact hw (H g hdirect hdisjoint hcover w hplanar)

end
end SpectreGeometry
