module

public import SpectreGeometry.DeformationHomeomorphismCarrierPeriod

@[expose] public section


/-! Ambient isometries preserve physical tilings and transport unlabelled
translation periods by their genuine orthogonal linear parts. This is the
normalization needed when every curved placement is reflected. -/
namespace LiteralPlanar
noncomputable section
open SpectreGeometry SpectreGeometry.Deformation

theorem isometry_add_linear (A : EPlane ≃ᵢ EPlane) (x v : EPlane) :
    A (x+v) = A x + A.toRealLinearIsometryEquiv v := by
  have he (z : EPlane) : A z = A.toRealLinearIsometryEquiv z + A 0 := by
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]
    exact (sub_add_cancel _ _).symm
  rw [he (x+v),map_add,he x]
  abel

theorem ambient_isometry_nonzero_translation (A : EPlane ≃ᵢ EPlane)
    (v : EPlane) (hv : v ≠ 0) : A.toRealLinearIsometryEquiv v ≠ 0 := by
  intro h
  apply hv
  apply A.toRealLinearIsometryEquiv.injective
  simpa only [map_zero] using h

theorem ambient_isometry_collection_period {J : Type*}
    (S : Set EPlane) (q : J → EPlane ≃ᵢ EPlane) (A : EPlane ≃ᵢ EPlane) (v : EPlane)
    (hperiod : Set.range (fun j => (fun x : EPlane => x+v) '' (q j '' S)) =
      Set.range (fun j => q j '' S)) :
    Set.range (fun j => (fun x : EPlane => x+A.toRealLinearIsometryEquiv v) ''
      ((q j).trans A '' S)) = Set.range (fun j => (q j).trans A '' S) := by
  apply carrier_collection_translation_transport
    (fun j => q j '' S) (fun j => (q j).trans A '' S) A v
    (A.toRealLinearIsometryEquiv v) _ (isometry_add_linear A · v) hperiod
  intro j
  rw [Set.image_image]
  rfl

theorem ambient_isometry_tiling {J : Type*}
    (S : Set EPlane) (q : J → EPlane ≃ᵢ EPlane) (A : EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' S)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' S)) (interior (q j '' S))) :
    (∀ x, ∃ j, x ∈ (q j).trans A '' S) ∧
      Pairwise (fun i j => Disjoint (interior ((q i).trans A '' S))
        (interior ((q j).trans A '' S))) := by
  apply tiling_transport A.toHomeomorph (fun j => q j '' S)
    (fun j => (q j).trans A '' S) hcover hpack
  intro j
  rw [Set.image_image]
  rfl

end
end LiteralPlanar
