module

public import SpectreGeometry.PolygonProductKeyBody
public import SpectreGeometry.PolygonProductKeyBranches

@[expose] public section


/-!
# Actual material sectors at generic actual product-key creases

The finite branch inequalities below supply open neighborhoods on which the
literal zero-extended tent is a maximum of two affine functions at a base
crease, or a minimum of two affine functions at a side-side crease. Combining
these identities with the actual-body hypograph theorem proves the material
sector germs, with their convexity reversed by the sign of the coefficient.
No local-sector or contact-matching hypothesis is used.
-/

namespace SpectreGeometry.ProductCreaseSectors
open SpectreGeometry PhysicalRegistration
open scoped InnerProductSpace
open Set
noncomputable section

def normalCoord (u : ProductKeySite) (x : EFour) : ℝ :=
  inner ℝ (productKeyOutwardNormal u) (x-productKeyCenter u)
def tangentCoord (u : ProductKeySite) (x : EFour) (i : Fin 3) : ℝ :=
  inner ℝ (productKeyTangent u i) (x-productKeyCenter u)
private theorem eta_pos : 0 < productKeyEta := by norm_num [productKeyEta]
private theorem branchProfile_false (u : ProductKeySite) (i : Fin 3) (x : EFour) :
    productKeyBranchProfile u (i,false) x =
    1 + (productKeyPrime i false : ℝ) * inner ℝ (productKeyTangent u i) (x-productKeyCenter u) / productKeyEta := by
  simp [productKeyBranchProfile]
private theorem branchProfile_true (u : ProductKeySite) (i : Fin 3) (x : EFour) :
    productKeyBranchProfile u (i,true) x =
    1 - (productKeyPrime i true : ℝ) * inner ℝ (productKeyTangent u i) (x-productKeyCenter u) / productKeyEta := by
  simp [productKeyBranchProfile]; ring
private theorem product_branch_continuous (u : ProductKeySite) (s : ProductKeySide) :
    Continuous (productKeyBranchProfile u s) := by
  unfold productKeyBranchProfile
  fun_prop
private theorem body_locally_eq_siteHypograph (u : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyGraphWindow u) :
    ∃ V : Set EFour, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V,
      y ∈ polygonProductKeyBody ↔ normalCoord u y ≤ productKeyHeight u (y-productKeyCenter u) := by
  exact ⟨interior (productKeyCollar u),isOpen_interior,
    product_key_graph_window_subset_interior_collar u hx,
    fun y hy => polygon_product_key_body_local_outward_iff u y hy⟩


/-- The affine side height formula holds without a branch-region restriction. -/
theorem sideHeight_eq_scaled_branch (u : ProductKeySite) (s : ProductKeySide) (x : EFour) :
    productKeySideHeight u s x =
      (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) * productKeyBranchProfile u s x := by
  unfold productKeySideHeight productKeySideSlope productKeyBranchProfile
  have he : productKeyEta ≠ 0 := eta_pos.ne'
  rcases s with ⟨i,b⟩
  cases b <;> norm_num [productKeyEta,productKeyN] <;> ring

/-- The side halfspace is expressed by the computed, unnormalized normal. -/
theorem le_sideHeight_iff (u : ProductKeySite) (s : ProductKeySide) (x : EFour) :
    normalCoord u x ≤ productKeySideHeight u s x ↔
      ⟪productKeySideNormal u s, x - productKeyCenter u⟫_ℝ ≤
        productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN := by
  simp only [productKeySideHeight, productKeySideNormal, inner_sub_left, real_inner_smul_left]
  change normalCoord u x ≤ _ + productKeySideSlope u s * tangentCoord u x s.1 ↔
    normalCoord u x - productKeySideSlope u s * tangentCoord u x s.1 ≤ _
  constructor <;> intro h <;> linarith

/-- A minimal affine branch determines the zero-extended profile even outside
the tube, where that branch may be negative. -/
theorem native_profile_eq_max_of_minimal (u : ProductKeySite) (s : ProductKeySide) (x : EFour)
    (hmin : ∀ t, productKeyBranchProfile u s x ≤ productKeyBranchProfile u t x) :
    keyTentProfile (productKeyEta) (fun i => (productKeyPrime i false : ℝ)) (fun i => (productKeyPrime i true : ℝ)) (productKeyTangent u) (x - productKeyCenter u) =
      max 0 (productKeyBranchProfile u s x) := by
  by_cases hs : 0 ≤ productKeyBranchProfile u s x
  · rw [max_eq_right hs]
    exact product_key_profile_eq_branch u s x ⟨hs, hmin⟩
  · have hs' : productKeyBranchProfile u s x ≤ 0 := le_of_not_ge hs
    rw [max_eq_left hs']
    unfold keyTentProfile
    apply max_eq_left
    have hupper := finiteLowerEnvelope_le (fun i y =>
      min (1 + (productKeyPrime i false : ℝ) * ⟪productKeyTangent u i, y⟫_ℝ / productKeyEta)
        (1 - (productKeyPrime i true : ℝ) * ⟪productKeyTangent u i, y⟫_ℝ / productKeyEta)) (x - productKeyCenter u) s.1
    apply le_trans _ hs'
    rcases s with ⟨i, b⟩
    cases b
    · rw [branchProfile_false]
      exact hupper.trans (min_le_left _ _)
    · rw [branchProfile_true]
      exact hupper.trans (min_le_right _ _)

/-- An open neighborhood on which one branch is the unique minimum. -/
def minimalBranchNeighborhood (u : ProductKeySite)
    (s : ProductKeySide) : Set (EFour) :=
  {x | ∀ t : {t : ProductKeySide // t ≠ s}, productKeyBranchProfile u s x < productKeyBranchProfile u t.val x}

theorem minimalBranchNeighborhood_isOpen (u : ProductKeySite)
    (s : ProductKeySide) : IsOpen (minimalBranchNeighborhood u s) := by
  unfold minimalBranchNeighborhood
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite (fun t => isOpen_lt
    (product_branch_continuous u s) (product_branch_continuous u t.val))

theorem minimalBranchNeighborhood_minimal (u : ProductKeySite)
    (s : ProductKeySide) {x : EFour} (hx : x ∈ minimalBranchNeighborhood u s) :
    ∀ t, productKeyBranchProfile u s x ≤ productKeyBranchProfile u t x := by
  intro t
  by_cases h : t = s
  · rw [h]
  · exact (hx ⟨t, h⟩).le

/-- The full height, including its zero extension, near a generic base crease. -/
theorem body_locally_eq_base_max_hypograph (u : ProductKeySite) (s : ProductKeySide) (x : EFour)
    (hx : x ∈ productKeyGraphWindow u) (hs : productKeyBranchProfile u s x = 0)
    (hother : ∀ t, t ≠ s → 0 < productKeyBranchProfile u t x) :
    ∃ U : Set (EFour), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔ normalCoord u y ≤
        (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) * max 0 (productKeyBranchProfile u s y) := by
  obtain ⟨V, hV, hxV, heq⟩ := body_locally_eq_siteHypograph u x hx
  have hxW : x ∈ minimalBranchNeighborhood u s := by
    intro t
    rw [hs]
    exact hother t.val t.property
  refine ⟨V ∩ minimalBranchNeighborhood u s,
    hV.inter (minimalBranchNeighborhood_isOpen u s), ⟨hxV, hxW⟩, ?_⟩
  intro y hy
  rw [heq y hy.1]
  change normalCoord u y ≤ productKeyHeight u (y-productKeyCenter u) ↔ _
  unfold productKeyHeight keyHeight
  rw [native_profile_eq_max_of_minimal u s y
    (minimalBranchNeighborhood_minimal u s hy.2)]

private theorem mul_max_nonpos (c b d : ℝ) (hc : c ≤ 0) :
    c * max b d = min (c * b) (c * d) := by
  rcases le_total b d with h | h
  · rw [max_eq_right h, min_eq_right (mul_le_mul_of_nonpos_left h hc)]
  · rw [max_eq_left h, min_eq_left (mul_le_mul_of_nonpos_left h hc)]

private theorem mul_min_nonpos (c b d : ℝ) (hc : c ≤ 0) :
    c * min b d = max (c * b) (c * d) := by
  rcases le_total b d with h | h
  · rw [min_eq_left h, max_eq_left (mul_le_mul_of_nonpos_left h hc)]
  · rw [min_eq_right h, max_eq_right (mul_le_mul_of_nonpos_left h hc)]

/-- A positive-coefficient base crease is locally the union of the carrier
halfspace and the computed affine side halfspace. -/
theorem body_locally_eq_base_sector_pos (u : ProductKeySite) (s : ProductKeySide) (x : EFour)
    (hx : x ∈ productKeyGraphWindow u) (hs : productKeyBranchProfile u s x = 0)
    (hother : ∀ t, t ≠ s → 0 < productKeyBranchProfile u t x)
    (ha : 0 < (productKeySignedLabel u : ℝ)) :
    ∃ U : Set (EFour), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔ normalCoord u y ≤ 0 ∨
        ⟪productKeySideNormal u s, y - productKeyCenter u⟫_ℝ ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_base_max_hypograph u s x hx hs hother
  have hc : 0 ≤ productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN :=
    div_nonneg (mul_nonneg eta_pos.le ha.le) (Nat.cast_nonneg _)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  rw [heq y hy, mul_max_of_nonneg _ _ hc, mul_zero,
    ← sideHeight_eq_scaled_branch, le_max_iff, le_sideHeight_iff]

/-- A negative-coefficient base crease is locally the intersection of the
carrier halfspace and the computed affine side halfspace. -/
theorem body_locally_eq_base_sector_neg (u : ProductKeySite) (s : ProductKeySide) (x : EFour)
    (hx : x ∈ productKeyGraphWindow u) (hs : productKeyBranchProfile u s x = 0)
    (hother : ∀ t, t ≠ s → 0 < productKeyBranchProfile u t x)
    (ha : (productKeySignedLabel u : ℝ) < 0) :
    ∃ U : Set (EFour), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔ normalCoord u y ≤ 0 ∧
        ⟪productKeySideNormal u s, y - productKeyCenter u⟫_ℝ ≤
          productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_base_max_hypograph u s x hx hs hother
  have hc : productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos eta_pos.le ha.le)
      (Nat.cast_nonneg _)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  rw [heq y hy, mul_max_nonpos _ _ _ hc, mul_zero,
    ← sideHeight_eq_scaled_branch, le_min_iff, le_sideHeight_iff]

/-- The open region where only these two positive branches can be minimal. -/
def pairBranchNeighborhood (u : ProductKeySite)
    (s t : ProductKeySide) : Set (EFour) :=
  {x | 0 < min (productKeyBranchProfile u s x) (productKeyBranchProfile u t x) ∧
    ∀ r : {r : ProductKeySide // r ≠ s ∧ r ≠ t},
      min (productKeyBranchProfile u s x) (productKeyBranchProfile u t x) < productKeyBranchProfile u r.val x}

theorem pairBranchNeighborhood_isOpen (u : ProductKeySite)
    (s t : ProductKeySide) : IsOpen (pairBranchNeighborhood u s t) := by
  have hc := (product_branch_continuous u s).min (product_branch_continuous u t)
  unfold pairBranchNeighborhood
  simp only [ofPred_and, ofPred_forall]
  exact (isOpen_lt continuous_const hc).inter (isOpen_iInter_of_finite
    (fun r => isOpen_lt hc (product_branch_continuous u r.val)))

/-- The actual tent is the minimum of the two selected branches on this open
region; no affine-face coverage is assumed. -/
theorem native_profile_eq_min_of_pair (u : ProductKeySite) (s t : ProductKeySide) (x : EFour)
    (hx : x ∈ pairBranchNeighborhood u s t) :
    keyTentProfile (productKeyEta) (fun i => (productKeyPrime i false : ℝ)) (fun i => (productKeyPrime i true : ℝ)) (productKeyTangent u) (x - productKeyCenter u) =
      min (productKeyBranchProfile u s x) (productKeyBranchProfile u t x) := by
  have hmin : ∀ r, min (productKeyBranchProfile u s x) (productKeyBranchProfile u t x) ≤
      productKeyBranchProfile u r x := by
    intro r
    by_cases hrs : r = s
    · rw [hrs]; exact min_le_left _ _
    by_cases hrt : r = t
    · rw [hrt]; exact min_le_right _ _
    exact (hx.2 ⟨r, hrs, hrt⟩).le
  have hx0 := hx.1
  rcases le_total (productKeyBranchProfile u s x) (productKeyBranchProfile u t x) with hst | hts
  · rw [min_eq_left hst] at hx0 hmin ⊢
    exact product_key_profile_eq_branch u s x ⟨hx0.le, hmin⟩
  · rw [min_eq_right hts] at hx0 hmin ⊢
    exact product_key_profile_eq_branch u t x ⟨hx0.le, hmin⟩

/-- The two-branch signed hypograph at a generic side-side point. -/
theorem body_locally_eq_side_min_hypograph (u : ProductKeySite) (s t : ProductKeySide) (x : EFour)
    (hx : x ∈ productKeyGraphWindow u) (hs : 0 < productKeyBranchProfile u s x)
    (hst : productKeyBranchProfile u s x = productKeyBranchProfile u t x)
    (hother : ∀ r, r ≠ s → r ≠ t → productKeyBranchProfile u s x < productKeyBranchProfile u r x) :
    ∃ U : Set (EFour), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔ normalCoord u y ≤
        (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) *
          min (productKeyBranchProfile u s y) (productKeyBranchProfile u t y) := by
  obtain ⟨V, hV, hxV, heq⟩ := body_locally_eq_siteHypograph u x hx
  have hxW : x ∈ pairBranchNeighborhood u s t := by
    change 0 < min _ _ ∧ _
    rw [← hst, min_self]
    exact ⟨hs, fun r => hother r.val r.property.1 r.property.2⟩
  refine ⟨V ∩ pairBranchNeighborhood u s t,
    hV.inter (pairBranchNeighborhood_isOpen u s t), ⟨hxV, hxW⟩, ?_⟩
  intro y hy
  rw [heq y hy.1]
  change normalCoord u y ≤ productKeyHeight u (y-productKeyCenter u) ↔ _
  unfold productKeyHeight keyHeight
  rw [native_profile_eq_min_of_pair u s t y hy.2]

/-- A positive-coefficient generic side-side crease has the intersection of
the two computed side halfspaces as its actual local material sector. The
algebraic statement also holds without the distinct-axis restriction. -/
theorem body_locally_eq_side_sector_pos (u : ProductKeySite) (s t : ProductKeySide) (x : EFour)
    (hx : x ∈ productKeyGraphWindow u) (hs : 0 < productKeyBranchProfile u s x)
    (hst : productKeyBranchProfile u s x = productKeyBranchProfile u t x)
    (hother : ∀ r, r ≠ s → r ≠ t → productKeyBranchProfile u s x < productKeyBranchProfile u r x)
    (ha : 0 < (productKeySignedLabel u : ℝ)) :
    ∃ U : Set (EFour), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔
        (⟪productKeySideNormal u s, y - productKeyCenter u⟫_ℝ ≤ productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) ∧
        (⟪productKeySideNormal u t, y - productKeyCenter u⟫_ℝ ≤ productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_side_min_hypograph u s t x hx hs hst hother
  have hc : 0 ≤ productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN :=
    div_nonneg (mul_nonneg eta_pos.le ha.le) (Nat.cast_nonneg _)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  rw [heq y hy, mul_min_of_nonneg _ _ hc,
    ← sideHeight_eq_scaled_branch, ← sideHeight_eq_scaled_branch,
    le_min_iff, le_sideHeight_iff, le_sideHeight_iff]

/-- A negative-coefficient generic side-side crease has the union of the two
computed side halfspaces as its actual local material sector. -/
theorem body_locally_eq_side_sector_neg (u : ProductKeySite) (s t : ProductKeySide) (x : EFour)
    (hx : x ∈ productKeyGraphWindow u) (hs : 0 < productKeyBranchProfile u s x)
    (hst : productKeyBranchProfile u s x = productKeyBranchProfile u t x)
    (hother : ∀ r, r ≠ s → r ≠ t → productKeyBranchProfile u s x < productKeyBranchProfile u r x)
    (ha : (productKeySignedLabel u : ℝ) < 0) :
    ∃ U : Set (EFour), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ polygonProductKeyBody ↔
        (⟪productKeySideNormal u s, y - productKeyCenter u⟫_ℝ ≤ productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) ∨
        (⟪productKeySideNormal u t, y - productKeyCenter u⟫_ℝ ≤ productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_side_min_hypograph u s t x hx hs hst hother
  have hc : productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos eta_pos.le ha.le)
      (Nat.cast_nonneg _)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  rw [heq y hy, mul_min_nonpos _ _ _ hc,
    ← sideHeight_eq_scaled_branch, ← sideHeight_eq_scaled_branch,
    le_max_iff, le_sideHeight_iff, le_sideHeight_iff]

#print axioms body_locally_eq_base_sector_pos
#print axioms body_locally_eq_base_sector_neg
#print axioms body_locally_eq_side_sector_pos
#print axioms body_locally_eq_side_sector_neg

end
end SpectreGeometry.ProductCreaseSectors
