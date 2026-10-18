module

public import SpectreGeometry.PolygonProductRawSymmetryTransport

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem physical_keyed_pair_preserves_raw {I : Type*}
    (f : I → EFour ≃ᵢ EFour) (T : PolygonProductPhysicalTiling f)
    (h : EFour ≃ᵢ EFour) (i j : I)
    (he : h '' (f i '' polygonProductKeyBody) = f j '' polygonProductKeyBody) :
    h '' (f i '' polygonProductBody) = f j '' polygonProductBody := by
  have himage (S : Set EFour) : h '' (f i '' S) = (f i).trans h '' S := by
    rw [Set.image_image]
    apply congrArg (fun k : EFour → EFour => k '' S)
    funext x
    exact ((f i).trans_apply h x).symm
  have hk : (f i).trans h '' polygonProductKeyBody = f j '' polygonProductKeyBody := by
    rw [← himage]
    exact he
  exact (himage polygonProductBody).trans
    (physical_equal_keyed_carrier_equal_raw f T j ((f i).trans h) hk)

/-- Equality of the actual unmarked physical tile families gives equality of
the recovered raw families, without a chosen bijection of tile indices. -/
theorem physical_keyed_range_symmetry_preserves_raw {I : Type*}
    (f : I → EFour ≃ᵢ EFour) (T : PolygonProductPhysicalTiling f)
    (h : EFour ≃ᵢ EFour)
    (hsym : Set.range (fun i => h '' (f i '' polygonProductKeyBody)) =
      Set.range (fun i => f i '' polygonProductKeyBody)) :
    Set.range (fun i => h '' (f i '' polygonProductBody)) =
      Set.range (fun i => f i '' polygonProductBody) := by
  ext S
  constructor
  · rintro ⟨i,rfl⟩
    have hm : h '' (f i '' polygonProductKeyBody) ∈
        Set.range (fun i => f i '' polygonProductKeyBody) := by rw [← hsym]; exact ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hm
    exact ⟨j,(physical_keyed_pair_preserves_raw f T h i j hj.symm).symm⟩
  · rintro ⟨j,rfl⟩
    have hm : f j '' polygonProductKeyBody ∈
        Set.range (fun i => h '' (f i '' polygonProductKeyBody)) := by rw [hsym]; exact ⟨j,rfl⟩
    obtain ⟨i,hi⟩ := hm
    exact ⟨i,physical_keyed_pair_preserves_raw f T h i j hi⟩

end
end SpectreGeometry
