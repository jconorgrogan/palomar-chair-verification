module

public import PhysicalRegistration.NativeBoundary

@[expose] public section

/-!
# Actual material sectors at generic native creases

The finite branch inequalities below supply open neighborhoods on which the
literal zero-extended tent is a maximum of two affine functions at a base
crease, or a minimum of two affine functions at a side-side crease. Combining
these identities with the actual-body hypograph theorem proves the material
sector germs, with their convexity reversed by the sign of the coefficient.
No local-sector or contact-matching hypothesis is used.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- The affine side height formula holds without a branch-region restriction. -/
theorem sideHeight_eq_scaled_branch {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) (x : Space m) :
    sideHeight a u s x =
      (eta m * (a.value u : ℝ) / denominator m J) * branchProfile J u s x := by
  unfold sideHeight sideSlope branchProfile
  have he : eta m ≠ 0 := (eta_pos m).ne'
  field_simp

/-- The side halfspace is expressed by the computed, unnormalized normal. -/
theorem le_sideHeight_iff {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) (x : Space m) :
    normalCoord u x ≤ sideHeight a u s x ↔
      ⟪sideNormal a u s, x - siteCenter u⟫_ℝ ≤
        eta m * (a.value u : ℝ) / denominator m J := by
  simp only [sideHeight, sideNormal, inner_sub_left, real_inner_smul_left]
  change normalCoord u x ≤ _ + sideSlope a u s * tangentCoord u x s.1 ↔
    normalCoord u x - sideSlope a u s * tangentCoord u x s.1 ≤ _
  constructor <;> intro h <;> linarith

/-- A minimal affine branch determines the zero-extended profile even outside
the tube, where that branch may be negative. -/
theorem native_profile_eq_max_of_minimal {m : ℕ} [NeZero m]
    (J : ℕ) (u : Site m) (s : Side m) (x : Space m)
    (hmin : ∀ t, branchProfile J u s x ≤ branchProfile J u t x) :
    keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u) =
      max 0 (branchProfile J u s x) := by
  by_cases hs : 0 ≤ branchProfile J u s x
  · rw [max_eq_right hs]
    exact native_profile_eq_branch J u s x ⟨hs, hmin⟩
  · have hs' : branchProfile J u s x ≤ 0 := le_of_not_ge hs
    rw [max_eq_left hs']
    unfold keyTentProfile
    apply max_eq_left
    have hupper := finiteLowerEnvelope_le (fun i y =>
      min (1 + pMinus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)
        (1 - pPlus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)) (x - siteCenter u) s.1
    apply le_trans _ hs'
    rcases s with ⟨i, b⟩
    cases b
    · rw [branchProfile_false]
      exact hupper.trans (min_le_left _ _)
    · rw [branchProfile_true]
      exact hupper.trans (min_le_right _ _)

/-- An open neighborhood on which one branch is the unique minimum. -/
def minimalBranchNeighborhood {m : ℕ} (J : ℕ) (u : Site m)
    (s : Side m) : Set (Space m) :=
  {x | ∀ t : {t : Side m // t ≠ s}, branchProfile J u s x < branchProfile J u t.val x}

theorem minimalBranchNeighborhood_isOpen {m : ℕ} (J : ℕ) (u : Site m)
    (s : Side m) : IsOpen (minimalBranchNeighborhood J u s) := by
  unfold minimalBranchNeighborhood
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite (fun t => isOpen_lt
    (branchProfile_continuous J u s) (branchProfile_continuous J u t.val))

theorem minimalBranchNeighborhood_minimal {m : ℕ} (J : ℕ) (u : Site m)
    (s : Side m) {x : Space m} (hx : x ∈ minimalBranchNeighborhood J u s) :
    ∀ t, branchProfile J u s x ≤ branchProfile J u t x := by
  intro t
  by_cases h : t = s
  · rw [h]
  · exact (hx ⟨t, h⟩).le

/-- The full height, including its zero extension, near a generic base crease. -/
theorem body_locally_eq_base_max_hypograph {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (s : Side m) (x : Space m)
    (hx : x ∈ keyGraph a u) (hs : branchProfile J u s x = 0)
    (hother : ∀ t, t ≠ s → 0 < branchProfile J u t x) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ body a ↔ normalCoord u y ≤
        (eta m * (a.value u : ℝ) / denominator m J) * max 0 (branchProfile J u s y) := by
  obtain ⟨V, hV, hxV, heq⟩ := body_locally_eq_siteHypograph hm a u x hx
  have hxW : x ∈ minimalBranchNeighborhood J u s := by
    intro t
    rw [hs]
    exact hother t.val t.property
  refine ⟨V ∩ minimalBranchNeighborhood J u s,
    hV.inter (minimalBranchNeighborhood_isOpen J u s), ⟨hxV, hxW⟩, ?_⟩
  intro y hy
  rw [heq y hy.1]
  change normalCoord u y ≤ siteHeight a u y ↔ _
  unfold siteHeight keyHeight
  rw [native_profile_eq_max_of_minimal J u s y
    (minimalBranchNeighborhood_minimal J u s hy.2)]

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
theorem body_locally_eq_base_sector_pos {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (s : Side m) (x : Space m)
    (hx : x ∈ keyGraph a u) (hs : branchProfile J u s x = 0)
    (hother : ∀ t, t ≠ s → 0 < branchProfile J u t x)
    (ha : 0 < (a.value u : ℝ)) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ body a ↔ normalCoord u y ≤ 0 ∨
        ⟪sideNormal a u s, y - siteCenter u⟫_ℝ ≤
          eta m * (a.value u : ℝ) / denominator m J := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_base_max_hypograph hm a u s x hx hs hother
  have hc : 0 ≤ eta m * (a.value u : ℝ) / denominator m J :=
    div_nonneg (mul_nonneg (eta_pos m).le ha.le) (Nat.cast_nonneg _)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  rw [heq y hy, mul_max_of_nonneg _ _ hc, mul_zero,
    ← sideHeight_eq_scaled_branch, le_max_iff, le_sideHeight_iff]

/-- A negative-coefficient base crease is locally the intersection of the
carrier halfspace and the computed affine side halfspace. -/
theorem body_locally_eq_base_sector_neg {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (s : Side m) (x : Space m)
    (hx : x ∈ keyGraph a u) (hs : branchProfile J u s x = 0)
    (hother : ∀ t, t ≠ s → 0 < branchProfile J u t x)
    (ha : (a.value u : ℝ) < 0) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ body a ↔ normalCoord u y ≤ 0 ∧
        ⟪sideNormal a u s, y - siteCenter u⟫_ℝ ≤
          eta m * (a.value u : ℝ) / denominator m J := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_base_max_hypograph hm a u s x hx hs hother
  have hc : eta m * (a.value u : ℝ) / denominator m J ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (eta_pos m).le ha.le)
      (Nat.cast_nonneg _)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  rw [heq y hy, mul_max_nonpos _ _ _ hc, mul_zero,
    ← sideHeight_eq_scaled_branch, le_min_iff, le_sideHeight_iff]

/-- The open region where only these two positive branches can be minimal. -/
def pairBranchNeighborhood {m : ℕ} (J : ℕ) (u : Site m)
    (s t : Side m) : Set (Space m) :=
  {x | 0 < min (branchProfile J u s x) (branchProfile J u t x) ∧
    ∀ r : {r : Side m // r ≠ s ∧ r ≠ t},
      min (branchProfile J u s x) (branchProfile J u t x) < branchProfile J u r.val x}

theorem pairBranchNeighborhood_isOpen {m : ℕ} (J : ℕ) (u : Site m)
    (s t : Side m) : IsOpen (pairBranchNeighborhood J u s t) := by
  have hc := (branchProfile_continuous J u s).min (branchProfile_continuous J u t)
  unfold pairBranchNeighborhood
  simp only [ofPred_and, ofPred_forall]
  exact (isOpen_lt continuous_const hc).inter (isOpen_iInter_of_finite
    (fun r => isOpen_lt hc (branchProfile_continuous J u r.val)))

/-- The actual tent is the minimum of the two selected branches on this open
region; no affine-face coverage is assumed. -/
theorem native_profile_eq_min_of_pair {m : ℕ} [NeZero m]
    (J : ℕ) (u : Site m) (s t : Side m) (x : Space m)
    (hx : x ∈ pairBranchNeighborhood J u s t) :
    keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u) =
      min (branchProfile J u s x) (branchProfile J u t x) := by
  have hmin : ∀ r, min (branchProfile J u s x) (branchProfile J u t x) ≤
      branchProfile J u r x := by
    intro r
    by_cases hrs : r = s
    · rw [hrs]; exact min_le_left _ _
    by_cases hrt : r = t
    · rw [hrt]; exact min_le_right _ _
    exact (hx.2 ⟨r, hrs, hrt⟩).le
  have hx0 := hx.1
  rcases le_total (branchProfile J u s x) (branchProfile J u t x) with hst | hts
  · rw [min_eq_left hst] at hx0 hmin ⊢
    exact native_profile_eq_branch J u s x ⟨hx0.le, hmin⟩
  · rw [min_eq_right hts] at hx0 hmin ⊢
    exact native_profile_eq_branch J u t x ⟨hx0.le, hmin⟩

/-- The two-branch signed hypograph at a generic side-side point. -/
theorem body_locally_eq_side_min_hypograph {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (s t : Side m) (x : Space m)
    (hx : x ∈ keyGraph a u) (hs : 0 < branchProfile J u s x)
    (hst : branchProfile J u s x = branchProfile J u t x)
    (hother : ∀ r, r ≠ s → r ≠ t → branchProfile J u s x < branchProfile J u r x) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ body a ↔ normalCoord u y ≤
        (eta m * (a.value u : ℝ) / denominator m J) *
          min (branchProfile J u s y) (branchProfile J u t y) := by
  obtain ⟨V, hV, hxV, heq⟩ := body_locally_eq_siteHypograph hm a u x hx
  have hxW : x ∈ pairBranchNeighborhood J u s t := by
    change 0 < min _ _ ∧ _
    rw [← hst, min_self]
    exact ⟨hs, fun r => hother r.val r.property.1 r.property.2⟩
  refine ⟨V ∩ pairBranchNeighborhood J u s t,
    hV.inter (pairBranchNeighborhood_isOpen J u s t), ⟨hxV, hxW⟩, ?_⟩
  intro y hy
  rw [heq y hy.1]
  change normalCoord u y ≤ siteHeight a u y ↔ _
  unfold siteHeight keyHeight
  rw [native_profile_eq_min_of_pair J u s t y hy.2]

/-- A positive-coefficient generic side-side crease has the intersection of
the two computed side halfspaces as its actual local material sector. The
algebraic statement also holds without the distinct-axis restriction. -/
theorem body_locally_eq_side_sector_pos {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (s t : Side m) (x : Space m)
    (hx : x ∈ keyGraph a u) (hs : 0 < branchProfile J u s x)
    (hst : branchProfile J u s x = branchProfile J u t x)
    (hother : ∀ r, r ≠ s → r ≠ t → branchProfile J u s x < branchProfile J u r x)
    (ha : 0 < (a.value u : ℝ)) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ body a ↔
        (⟪sideNormal a u s, y - siteCenter u⟫_ℝ ≤ eta m * (a.value u : ℝ) / denominator m J) ∧
        (⟪sideNormal a u t, y - siteCenter u⟫_ℝ ≤ eta m * (a.value u : ℝ) / denominator m J) := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_side_min_hypograph hm a u s t x hx hs hst hother
  have hc : 0 ≤ eta m * (a.value u : ℝ) / denominator m J :=
    div_nonneg (mul_nonneg (eta_pos m).le ha.le) (Nat.cast_nonneg _)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  rw [heq y hy, mul_min_of_nonneg _ _ hc,
    ← sideHeight_eq_scaled_branch, ← sideHeight_eq_scaled_branch,
    le_min_iff, le_sideHeight_iff, le_sideHeight_iff]

/-- A negative-coefficient generic side-side crease has the union of the two
computed side halfspaces as its actual local material sector. -/
theorem body_locally_eq_side_sector_neg {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (s t : Side m) (x : Space m)
    (hx : x ∈ keyGraph a u) (hs : 0 < branchProfile J u s x)
    (hst : branchProfile J u s x = branchProfile J u t x)
    (hother : ∀ r, r ≠ s → r ≠ t → branchProfile J u s x < branchProfile J u r x)
    (ha : (a.value u : ℝ) < 0) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ body a ↔
        (⟪sideNormal a u s, y - siteCenter u⟫_ℝ ≤ eta m * (a.value u : ℝ) / denominator m J) ∨
        (⟪sideNormal a u t, y - siteCenter u⟫_ℝ ≤ eta m * (a.value u : ℝ) / denominator m J) := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_side_min_hypograph hm a u s t x hx hs hst hother
  have hc : eta m * (a.value u : ℝ) / denominator m J ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (eta_pos m).le ha.le)
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
end PhysicalRegistration.NativeChair
