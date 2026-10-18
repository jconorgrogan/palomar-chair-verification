module

public import SpectreGeometry.PolygonProductKeyPairedMaterialInterior

@[expose] public section


/-! Direct world-coordinate nonoverlap of the two original carrier interiors
inside a matched actual collar. No isolation from other collars is assumed. -/
namespace SpectreGeometry
noncomputable section
open Set

private theorem isometry_mem_interior_image (f : EFour ≃ᵢ EFour) (S : Set EFour) (z : EFour) :
    f z ∈ interior (f '' S) ↔ z ∈ interior S := by
  have he : f '' interior S = interior (f '' S) := f.toHomeomorph.image_interior S
  rw [← he]
  constructor
  · rintro ⟨y,hy,he⟩
    exact (f.injective he) ▸ hy
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem paired_raw_interiors_disjoint_on_collar (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour)
    (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g)
    (x : EFour) (hx : x ∈ interior (f '' productKeyCollar s)) :
    ¬ (x ∈ interior (f '' polygonProductBody) ∧ x ∈ interior (g '' polygonProductBody)) := by
  have hi : f '' interior (productKeyCollar s) = interior (f '' productKeyCollar s) :=
    f.toHomeomorph.image_interior (productKeyCollar s)
  rw [← hi,← product_key_signed_pose_image_collar_interior s,
    Set.image_image] at hx
  obtain ⟨w,hw,rfl⟩ := hx
  rintro ⟨hi,hj⟩
  have he := congrArg (fun h : EFour ≃ᵢ EFour => h w) hp
  change f (productKeySignedAffineIsometry s w) = g (productKeySignedAffineIsometry t w) at he
  have hi' := (isometry_mem_interior_image f polygonProductBody _).mp hi
  change f (productKeySignedAffineIsometry s w) ∈ interior (g '' polygonProductBody) at hj
  rw [he] at hj
  have hj' := (isometry_mem_interior_image g polygonProductBody _).mp hj
  have hs := (product_key_signed_raw_interior_iff s w hw).mp hi'
  have ht := (product_key_signed_raw_interior_iff t w hw).mp hj'
  rw [hsign,neg_mul] at ht
  linarith

end
end SpectreGeometry
