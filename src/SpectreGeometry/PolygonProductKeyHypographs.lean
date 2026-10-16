module

public import SpectreGeometry.PolygonProductKeyFrames
public import PhysicalRegistration.KeyTube

@[expose] public section


/-! The literal signed max-min key heights of the optimized P-product recipe,
with actual Lipschitz and local graph properties. These are the centered
single-key hypographs; bounded tube-replacement assembly is separate. -/
namespace SpectreGeometry
open scoped InnerProductSpace
open PhysicalRegistration
noncomputable section

def productKeyHeight (s : ProductKeySite) (v : EFour) : ℝ :=
  keyHeight productKeyEta (productKeySignedLabel s : ℝ) (productKeyN : ℝ)
    (fun j => (productKeyPrime j false : ℝ)) (fun j => (productKeyPrime j true : ℝ))
    (productKeyTangent s) v

def productKeyHypograph (s : ProductKeySite) : Set EFour :=
  centeredGraphHypograph (productKeyCenter s) (productKeyOutwardNormal s) (productKeyHeight s)

def productKeyGraph (s : ProductKeySite) : Set EFour :=
  {x | inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s) =
    productKeyHeight s (x - productKeyCenter s)}

theorem product_key_prime_bounds (j : Fin 3) (b : Bool) :
    1 ≤ (productKeyPrime j b : ℝ) ∧ (productKeyPrime j b : ℝ) ≤ 17 := by
  fin_cases j <;> cases b <;> norm_num [productKeyPrime,productKeyPrimePairs]

theorem product_key_label_bound (s : ProductKeySite) : |(productKeySignedLabel s : ℝ)| ≤ 2 := by
  rcases s with ⟨b,i,e⟩
  fin_cases b <;> cases e <;> norm_num [productKeySignedLabel]

theorem product_key_height_lipschitz (s : ProductKeySite) (v w : EFour) :
    |productKeyHeight s v - productKeyHeight s w| ≤ (34 / 4357 : ℝ) * ‖v - w‖ := by
  have h := keyHeight_lipschitz productKeyEta (productKeySignedLabel s : ℝ)
    (productKeyN : ℝ) 2 17 (by norm_num [productKeyEta]) (by norm_num [productKeyN])
    (product_key_label_bound s) (by norm_num)
    (fun j => (productKeyPrime j false : ℝ)) (fun j => (productKeyPrime j true : ℝ))
    (productKeyTangent s)
    (fun j => ⟨by linarith [(product_key_prime_bounds j false).1],(product_key_prime_bounds j false).2⟩)
    (fun j => ⟨by linarith [(product_key_prime_bounds j true).1],(product_key_prime_bounds j true).2⟩)
    (productKeyTangent_norm s) v w
  norm_num [productKeyHeight,productKeyN] at h ⊢
  exact h

theorem product_key_height_normal_shift (s : ProductKeySite) (v : EFour) (t : ℝ) :
    productKeyHeight s (v + t • productKeyOutwardNormal s) = productKeyHeight s v := by
  apply keyHeight_normal_shift
  intro j
  rw [real_inner_comm]
  exact productKeyOutwardNormal_inner_tangent s j

theorem product_key_height_support (s : ProductKeySite) (v : EFour)
    (hv : productKeyHeight s v ≠ 0) :
    ∀ j : Fin 3, |inner ℝ (productKeyTangent s j) v| ≤ productKeyEta := by
  have h := keyHeight_active_footprint productKeyEta (productKeySignedLabel s : ℝ)
    (productKeyN : ℝ) (by norm_num [productKeyEta])
    (fun j => (productKeyPrime j false : ℝ)) (fun j => (productKeyPrime j true : ℝ))
    (productKeyTangent s)
    (fun j => by linarith [(product_key_prime_bounds j false).1])
    (fun j => by linarith [(product_key_prime_bounds j true).1]) v hv
  intro j
  exact asymmetric_footprint_coordinate_bound _ _ _ _ (by norm_num [productKeyEta])
    (product_key_prime_bounds j false).1 (product_key_prime_bounds j true).1 (h j)

theorem product_key_hypograph_closed (s : ProductKeySite) : IsClosed (productKeyHypograph s) :=
  centeredGraphHypograph_isClosed _ _ (productKeyOutwardNormal_norm s) _ (34/4357)
    (by norm_num) (product_key_height_lipschitz s)

/-- A local inward graph at every actual key-graph point, including creases,
the apex, and the zero extension. No graph/Lipschitz premise is assumed. -/
def productKeyGraph_local_graph (s : ProductKeySite) (x : EFour) (hx : x ∈ productKeyGraph s) :
    LocalLipschitzGraphAt (productKeyHypograph s) x (34/4357) :=
  centeredGraphHypograph_local_graph _ _ (productKeyOutwardNormal_norm s) _ (34/4357)
    (by norm_num) (product_key_height_lipschitz s) (product_key_height_normal_shift s) x hx

theorem product_key_slope_below_half : (0 : ℝ) ≤ 34/4357 ∧ (34 : ℝ)/4357 < 1/2 := by norm_num

end
end SpectreGeometry
