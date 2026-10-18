module

public import SpectreGeometry.PolygonProductKeyHypographs
public import SpectreGeometry.PolygonProductKeyNormalAngles

@[expose] public section


/-! Affine branches extracted from the actual optimized max-min height.
The zero-extended graph is covered by its flat base plane and six side
planes. These are literal graph equations, not a contact classification. -/
namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration
open scoped InnerProductSpace

def productKeyBranchProfile (s : ProductKeySite) (b : ProductKeySide) (x : EFour) : ℝ :=
  1 + (if b.2 then -1 else 1) * (productKeyPrime b.1 b.2 : ℝ) *
    inner ℝ (productKeyTangent s b.1) (x - productKeyCenter s) / productKeyEta

def productKeyBranchRegion (s : ProductKeySite) (b : ProductKeySide) : Set EFour :=
  {x | 0 ≤ productKeyBranchProfile s b x ∧
    ∀ c, productKeyBranchProfile s b x ≤ productKeyBranchProfile s c x}

private theorem profile_false (s : ProductKeySite) (j : Fin 3) (x : EFour) :
    productKeyBranchProfile s (j,false) x =
      1 + (productKeyPrime j false : ℝ) * inner ℝ (productKeyTangent s j)
        (x-productKeyCenter s) / productKeyEta := by simp [productKeyBranchProfile]

private theorem profile_true (s : ProductKeySite) (j : Fin 3) (x : EFour) :
    productKeyBranchProfile s (j,true) x =
      1 - (productKeyPrime j true : ℝ) * inner ℝ (productKeyTangent s j)
        (x-productKeyCenter s) / productKeyEta := by simp [productKeyBranchProfile]; ring

theorem product_key_profile_eq_branch (s : ProductKeySite) (b : ProductKeySide) (x : EFour)
    (hx : x ∈ productKeyBranchRegion s b) :
    keyTentProfile productKeyEta (fun j => (productKeyPrime j false : ℝ))
      (fun j => (productKeyPrime j true : ℝ)) (productKeyTangent s) (x-productKeyCenter s) =
      productKeyBranchProfile s b x := by
  have hlo : ∀ j : Fin 3, productKeyBranchProfile s b x ≤
      min (1 + (productKeyPrime j false : ℝ) * inner ℝ (productKeyTangent s j)
        (x-productKeyCenter s) / productKeyEta)
        (1 - (productKeyPrime j true : ℝ) * inner ℝ (productKeyTangent s j)
        (x-productKeyCenter s) / productKeyEta) := by
    intro j
    exact le_min (by simpa only [profile_false] using hx.2 (j,false))
      (by simpa only [profile_true] using hx.2 (j,true))
  have hlower : productKeyBranchProfile s b x ≤ finiteLowerEnvelope (fun j y =>
      min (1 + (productKeyPrime j false : ℝ) * inner ℝ (productKeyTangent s j) y / productKeyEta)
        (1 - (productKeyPrime j true : ℝ) * inner ℝ (productKeyTangent s j) y / productKeyEta))
      (x-productKeyCenter s) := by
    apply Finset.le_inf'
    intro j _
    exact hlo j
  have hupper := finiteLowerEnvelope_le (fun j y =>
      min (1 + (productKeyPrime j false : ℝ) * inner ℝ (productKeyTangent s j) y / productKeyEta)
        (1 - (productKeyPrime j true : ℝ) * inner ℝ (productKeyTangent s j) y / productKeyEta))
      (x-productKeyCenter s) b.1
  have heq : finiteLowerEnvelope (fun j y =>
      min (1 + (productKeyPrime j false : ℝ) * inner ℝ (productKeyTangent s j) y / productKeyEta)
        (1 - (productKeyPrime j true : ℝ) * inner ℝ (productKeyTangent s j) y / productKeyEta))
      (x-productKeyCenter s) = productKeyBranchProfile s b x := by
    apply le_antisymm _ hlower
    rcases b with ⟨j,e⟩
    cases e
    · rw [profile_false]; exact hupper.trans (min_le_left _ _)
    · rw [profile_true]; exact hupper.trans (min_le_right _ _)
  unfold keyTentProfile
  rw [heq,max_eq_right hx.1]

theorem product_key_height_eq_side_height (s : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ productKeyBranchRegion s b) :
    productKeyHeight s (x-productKeyCenter s) = productKeySideHeight s b x := by
  unfold productKeyHeight keyHeight
  rw [product_key_profile_eq_branch s b x hx]
  unfold productKeyBranchProfile productKeySideHeight productKeySideSlope
  rcases b with ⟨j,e⟩
  cases e <;> norm_num [productKeyEta,productKeyN] <;> ring

theorem product_key_active_branch_exists (s : ProductKeySite) (x : EFour)
    (hx : productKeyHeight s (x-productKeyCenter s) ≠ 0) :
    ∃ b : ProductKeySide, x ∈ productKeyBranchRegion s b := by
  have hf := keyHeight_active_footprint productKeyEta (productKeySignedLabel s : ℝ)
    (productKeyN : ℝ) (by norm_num [productKeyEta])
    (fun j => (productKeyPrime j false : ℝ)) (fun j => (productKeyPrime j true : ℝ))
    (productKeyTangent s)
    (fun j => by linarith [(product_key_prime_bounds j false).1])
    (fun j => by linarith [(product_key_prime_bounds j true).1]) (x-productKeyCenter s) hx
  have hnonneg (b : ProductKeySide) : 0 ≤ productKeyBranchProfile s b x := by
    rcases b with ⟨j,e⟩
    have heta : 0 < productKeyEta := by norm_num [productKeyEta]
    cases e
    · rw [profile_false]
      have h := (div_lt_iff₀ (by linarith [(product_key_prime_bounds j false).1] :
        0 < (productKeyPrime j false : ℝ))).mp (hf j).1
      have hd : -1 ≤ (productKeyPrime j false : ℝ) *
          inner ℝ (productKeyTangent s j) (x-productKeyCenter s) / productKeyEta :=
        (le_div_iff₀ heta).mpr (by nlinarith)
      linarith
    · rw [profile_true]
      have h := (lt_div_iff₀ (by linarith [(product_key_prime_bounds j true).1] :
        0 < (productKeyPrime j true : ℝ))).mp (hf j).2
      have hd : (productKeyPrime j true : ℝ) *
          inner ℝ (productKeyTangent s j) (x-productKeyCenter s) / productKeyEta ≤ 1 :=
        (div_le_iff₀ heta).mpr (by nlinarith)
      linarith
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ProductKeySide))
    (fun b => productKeyBranchProfile s b x)
  refine ⟨b,hnonneg b,?_⟩
  intro c
  rw [← hb]
  exact Finset.inf'_le _ (Finset.mem_univ c)

def productKeySideFace (s : ProductKeySite) (b : ProductKeySide) : Set EFour :=
  productKeyGraph s ∩ productKeyBranchRegion s b

theorem product_key_side_face_plane (s : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ productKeySideFace s b) :
    inner ℝ (productKeySideNormal s b) (x-productKeyCenter s) =
      productKeyEta * (productKeySignedLabel s : ℝ) / productKeyN := by
  apply (product_key_branch_normal_equation s b x).mp
  exact hx.1.trans (product_key_height_eq_side_height s b x hx.2)

theorem product_key_graph_plane_cover (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyGraph s) :
    inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) = 0 ∨
    ∃ b : ProductKeySide, x ∈ productKeySideFace s b := by
  by_cases hz : productKeyHeight s (x-productKeyCenter s) = 0
  · exact Or.inl (hx.trans hz)
  · obtain ⟨b,hb⟩ := product_key_active_branch_exists s x hz
    exact Or.inr ⟨b,hx,hb⟩

theorem product_key_graph_affine_plane_cover (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyGraph s) :
    inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) = 0 ∨
    ∃ b : ProductKeySide, inner ℝ (productKeySideNormal s b) (x-productKeyCenter s) =
      productKeyEta * (productKeySignedLabel s : ℝ) / productKeyN := by
  rcases product_key_graph_plane_cover s x hx with h | ⟨b,hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨b,product_key_side_face_plane s b x hb⟩

end
end SpectreGeometry
