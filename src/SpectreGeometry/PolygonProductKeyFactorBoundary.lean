module

public import SpectreGeometry.PolygonProductKeyPoseOpposition

@[expose] public section


/-! Exact factor-boundary transport from a registered actual signed key pose.
The active edge parameter reverses and every passive coordinate is preserved.
These are local registration consequences; no global Cartesian decomposition
or completeness of factor sections is assumed or asserted here. -/
namespace SpectreGeometry
noncomputable section
open Set

/-- The entire supporting edge line with an arbitrary passive factor point. -/
def productKeyBoundaryPoint (s : ProductKeySite) (r : ℝ) (p : RealPoint) : EFour :=
  if s.1 = 0 then productCoordinates (realVertex s.2.1 + r • realEdge s.2.1,p)
  else productCoordinates (p,realVertex s.2.1 + r • realEdge s.2.1)

def productKeyBoundaryReference (s : ProductKeySite) (r : ℝ) (p : RealPoint) : EFour :=
  WithLp.toLp 2 ![productKeySign s * (r-1/2) + 1/4,p.1-1/2,p.2-1/2,0]

/-- The exact quarter-edge anchoring cancels in common signed coordinates. -/
theorem product_key_signed_boundary_reference (s : ProductKeySite) (r : ℝ) (p : RealPoint) :
    productKeySignedAffineIsometry s (productKeyBoundaryReference s r p) =
      productKeyBoundaryPoint s r p := by
  rw [product_key_signed_pose_apply,productKeyAffineIsometry_apply]
  rcases s with ⟨b,i,e⟩
  fin_cases b <;> cases e <;> ext k <;> fin_cases k <;>
    simp [productKeyBoundaryReference,productKeyBoundaryPoint,
      product_key_normal_reflection_coordinate,productKeyCenter,productKeyActiveCenter,
      productKeyFrame,productKeyTangent,productKeyOutwardNormal,productKeySign,
      leftNormalMap,rightNormalMap,productCoordinates,productCoordinateLinearEquiv,
      Fin.sum_univ_succ] <;> ring

theorem product_key_boundary_reference_reversal (s t : ProductKeySite)
    (hsign : productKeySign t = -productKeySign s) (r : ℝ) (p : RealPoint) :
    productKeyBoundaryReference s r p = productKeyBoundaryReference t (1-r) p := by
  ext k
  fin_cases k <;> simp [productKeyBoundaryReference,hsign] <;> ring

/-- Full pointwise passive identity and active edge reversal, for every real
edge parameter, follow from exact actual signed-pose registration. -/
theorem registered_product_boundary_point (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour) (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g)
    (r : ℝ) (p : RealPoint) :
    f (productKeyBoundaryPoint s r p) = g (productKeyBoundaryPoint t (1-r) p) := by
  rw [← product_key_signed_boundary_reference s,← product_key_signed_boundary_reference t]
  have he := congrArg (fun h : EFour ≃ᵢ EFour => h (productKeyBoundaryReference s r p)) hp
  change f (productKeySignedAffineIsometry s (productKeyBoundaryReference s r p)) =
    g (productKeySignedAffineIsometry t (productKeyBoundaryReference s r p)) at he
  rw [product_key_boundary_reference_reversal s t hsign r p] at he
  simpa only [product_key_boundary_reference_reversal s t hsign r p] using he

/-- The literal whole edge times the full passive polygon, independent of key polarity. -/
def productKeyBoundaryPiece (s : ProductKeySite) : Set EFour :=
  {x | ∃ r ∈ Icc (0:ℝ) 1, ∃ p ∈ polygonBody, productKeyBoundaryPoint s r p = x}

theorem product_key_boundary_piece_polarity_independent (b : Fin 2) (i : Fin 14) :
    productKeyBoundaryPiece (b,i,false) = productKeyBoundaryPiece (b,i,true) := rfl

theorem registered_product_boundary_piece (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour) (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g) :
    f '' productKeyBoundaryPiece s = g '' productKeyBoundaryPiece t := by
  ext x
  constructor
  · rintro ⟨y,⟨r,hr,p,hp',rfl⟩,rfl⟩
    refine ⟨productKeyBoundaryPoint t (1-r) p,⟨1-r,⟨by linarith [hr.2],by linarith [hr.1]⟩,p,hp',rfl⟩,?_⟩
    exact (registered_product_boundary_point s t f g hsign hp r p).symm
  · rintro ⟨y,⟨r,hr,p,hp',rfl⟩,rfl⟩
    refine ⟨productKeyBoundaryPoint s (1-r) p,⟨1-r,⟨by linarith [hr.2],by linarith [hr.1]⟩,p,hp',rfl⟩,?_⟩
    have he := registered_product_boundary_point s t f g hsign hp (1-r) p
    convert he using 1 <;> congr 2 <;> ring

end
end SpectreGeometry
