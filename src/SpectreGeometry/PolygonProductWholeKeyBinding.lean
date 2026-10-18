module

public import SpectreGeometry.PolygonProductReferenceTentBinding
public import SpectreGeometry.PolygonProductKeyReferencePose
public import SpectreGeometry.PolygonProductKeySignedPoses
public import SpectreGeometry.PolygonProductKeyHypographs

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open SparseMonotiles PhysicalRegistration
open scoped InnerProductSpace
noncomputable section

/-- The literal closed whole bump/dent pyramid, restricted to its actual
asymmetric base footprint. Its height uses the same signed max-min formula
as the physical product-key hypograph. -/
def actualWholeKey (s : ProductKeySite) : Set EFour := {x |
  (∀ i : Fin 3,
    -productKeyEta/(productKeyPrime i false : ℝ) ≤ inner ℝ (productKeyTangent s i) (x-productKeyCenter s) ∧
    inner ℝ (productKeyTangent s i) (x-productKeyCenter s) ≤ productKeyEta/(productKeyPrime i true : ℝ)) ∧
  0 ≤ inner ℝ (productKeySign s • productKeyOutwardNormal s) (x-productKeyCenter s) ∧
  inner ℝ (productKeySign s • productKeyOutwardNormal s) (x-productKeyCenter s) ≤
    productKeySign s * productKeyHeight s (x-productKeyCenter s)}

theorem signed_pose_tent_height (s : ProductKeySite) (w : EFour) :
    productKeySign s * productKeyHeight s
      (productKeySignedAffineIsometry s w-productKeyCenter s) =
    referenceHeight s.1 * max 0 (coordinateEnvelope w) := by
  simp only [productKeyHeight,keyHeight,keyTentProfile,finiteLowerEnvelope,
    product_key_signed_pose_tangent_coordinate,productKeySignedLabel_real]
  change productKeySign s *
    (productKeyEta * (productKeySign s * (s.1.val+1)) / productKeyN *
      max 0 (coordinateEnvelope w)) = _
  unfold referenceHeight
  cases hs : s.2.2 <;> simp [productKeySign,hs] <;> ring

theorem signed_pose_mem_actualWholeKey (s : ProductKeySite) (w : EFour) :
    productKeySignedAffineIsometry s w ∈ actualWholeKey s ↔ w ∈ referenceSolid s.1 := by
  rw [reference_mem_iff_tent]
  simp only [actualWholeKey,Set.mem_setOf_eq,product_key_signed_pose_tangent_coordinate,
    product_key_signed_pose_normal_coordinate,signed_pose_tent_height,coordinateFootprint]

theorem signed_pose_image_reference (s : ProductKeySite) :
    productKeySignedAffineIsometry s '' referenceSolid s.1 = actualWholeKey s := by
  ext x
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (signed_pose_mem_actualWholeKey s w).mpr hw
  · intro hx
    refine ⟨(productKeySignedAffineIsometry s).symm x,?_,by simp⟩
    apply (signed_pose_mem_actualWholeKey s _).mp
    simpa using hx

/-- Coincident whole physical keys determine their absolute label and their
full composed Euclidean pose. The hypothesis is whole-key coincidence;
recognition from a local contact is a separate geometric obligation. -/
theorem coincident_actualWholeKeys (s t : ProductKeySite) (g h : EFour ≃ᵢ EFour)
    (heq : g '' actualWholeKey s = h '' actualWholeKey t) :
    s.1 = t.1 ∧
      (productKeySignedAffineIsometry s).toIsometryEquiv.trans g =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans h := by
  rw [←signed_pose_image_reference s,←signed_pose_image_reference t,
    Set.image_image,Set.image_image] at heq
  exact placed_reference_unique s.1 t.1
    ((productKeySignedAffineIsometry s).toIsometryEquiv.trans g)
    ((productKeySignedAffineIsometry t).toIsometryEquiv.trans h) heq

end
end SpectreGeometry.ProductKeyReference
