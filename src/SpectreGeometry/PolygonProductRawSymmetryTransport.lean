module

public import SpectreGeometry.PolygonProductCarrierRecovery

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

/-- An isometry carrying each unmarked physical tile to another tile also
carries the recovered raw carriers to the corresponding raw carriers. -/
theorem physical_keyed_symmetry_preserves_raw {I : Type*}
    (f : I → EFour ≃ᵢ EFour) (T : PolygonProductPhysicalTiling f)
    (h : EFour ≃ᵢ EFour)
    (hsym : ∀ i, ∃ j, h '' (f i '' polygonProductKeyBody) = f j '' polygonProductKeyBody) :
    ∀ i, ∃ j, h '' (f i '' polygonProductBody) = f j '' polygonProductBody := by
  intro i
  obtain ⟨j,hj⟩ := hsym i
  have himage (S : Set EFour) : h '' (f i '' S) = (f i).trans h '' S := by
    rw [Set.image_image]
    apply congrArg (fun k : EFour → EFour => k '' S)
    funext x
    exact ((f i).trans_apply h x).symm
  have he : (f i).trans h '' polygonProductKeyBody = f j '' polygonProductKeyBody := by
    rw [← himage]
    exact hj
  have hr := physical_equal_keyed_carrier_equal_raw f T j ((f i).trans h) he
  exact ⟨j,(himage polygonProductBody).trans hr⟩

end
end SpectreGeometry
