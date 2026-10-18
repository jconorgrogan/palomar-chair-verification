module

public import SpectreGeometry.PolygonProductKeyFactorTransition

@[expose] public section


namespace SpectreGeometry
noncomputable section

/-- The edge-normal-passive chart reaches every reference point. -/
theorem product_key_full_reference_surjective (s : ProductKeySite) (w : EFour) :
    ∃ r h p, productKeyFullReference s r h p = w := by
  refine ⟨1/2+productKeySign s*(w 0-1/4),productKeySign s*w 3,
    (w 1+1/2,w 2+1/2),?_⟩
  cases he : s.2.2 <;> ext k <;> fin_cases k <;>
    simp [productKeyFullReference,productKeySign,he] <;> ring

/-- Conversely, actual full edge-frame agreement identifies the complete
signed key poses. This is used to construct, rather than assume, forward pairs. -/
theorem product_key_pose_of_full_coordinates (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour) (hsign : productKeySign t = -productKeySign s)
    (hcoord : ∀ r h p,
      f (productFactorPoint s.1 (productEdgeFramePoint s.2.1 r h) p) =
      g (productFactorPoint t.1 (productEdgeFramePoint t.2.1 (1-r) (-h)) p)) :
    (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g := by
  apply IsometryEquiv.ext
  intro w
  obtain ⟨r,h,p,rfl⟩ := product_key_full_reference_surjective s w
  change f (productKeySignedAffineIsometry s (productKeyFullReference s r h p)) =
    g (productKeySignedAffineIsometry t (productKeyFullReference s r h p))
  have hw : productKeyFullReference s r h p = productKeyFullReference t (1-r) (-h) p := by
    ext k; fin_cases k <;> simp [productKeyFullReference,hsign] <;> ring
  rw [product_key_signed_full_reference,hw,product_key_signed_full_reference]
  exact hcoord r h p

end
end SpectreGeometry
