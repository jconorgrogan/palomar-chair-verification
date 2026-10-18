module

public import ProductClosure.GenericCreaseDensity
public import ProductClosure.CreaseSectors
public import ProductClosure.NativeAngleSeparation

@[expose] public section

/-!
# Exact plane-intersection germs of literal generic native creases

The open sets below are explicit finite strict-branch neighborhoods intersected
with the normal tube slab. The converse plane-to-crease inclusions are derived
from branch nonnegativity and the literal tent, not assumed as local geometry.
The two defining normals are proved independent. No boundary inventory or
contact-preservation assertion is made.
-/

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- The common affine height coefficient is nonzero for every native key. -/
theorem native_height_coefficient_ne_zero {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) : eta m * (a.value u : ℝ) / denominator m J ≠ 0 := by
  have ha : (a.value u : ℝ) ≠ 0 := by exact_mod_cast a.nonzero u
  have hN : (denominator m J : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_prime m J).ne_zero
  exact div_ne_zero (mul_ne_zero (eta_pos m).ne' ha) hN

/-- Equality in the computed side plane is precisely the affine graph equation. -/
theorem eq_sideHeight_iff {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) (x : Space m) :
    normalCoord u x = sideHeight a u s x ↔
      ⟪sideNormal a u s, x - siteCenter u⟫_ℝ =
        eta m * (a.value u : ℝ) / denominator m J := by
  simp only [sideHeight, sideNormal, inner_sub_left, real_inner_smul_left]
  change normalCoord u x = _ + sideSlope a u s * tangentCoord u x s.1 ↔
    normalCoord u x - sideSlope a u s * tangentCoord u x s.1 = _
  constructor <;> intro h <;> linarith

/-- Nonnegativity of all affine branches gives the exact asymmetric footprint. -/
theorem footprint_bounds_of_branchProfile_nonneg  (J : ℕ) (u : Site polyCells)
    (x : Space m) (hx : ∀ s, 0 ≤ branchProfile J u s x) :
    ∀ i, -eta m / pMinus J i ≤ tangentCoord u x i ∧
      tangentCoord u x i ≤ eta m / pPlus J i := by
  intro i
  have hm := hx (i, false)
  have hp := hx (i, true)
  rw [branchProfile_false] at hm
  rw [branchProfile_true] at hp
  have hm' : -1 ≤ pMinus J i * tangentCoord u x i / eta m := by linarith
  have hp' : pPlus J i * tangentCoord u x i / eta m ≤ 1 := by linarith
  have hm'' := (le_div_iff₀ (eta_pos m)).mp hm'
  have hp'' := (div_le_iff₀ (eta_pos m)).mp hp'
  constructor
  · apply (div_le_iff₀ (pMinus_pos J i)).mpr
    nlinarith
  · apply (le_div_iff₀ (pPlus_pos J i)).mpr
    nlinarith

theorem mem_closedTube_of_branchProfile_nonneg  (J : ℕ) (u : Site polyCells)
    (x : Space m) (hn : |normalCoord u x| ≤ rho m)
    (hx : ∀ s, 0 ≤ branchProfile J u s x) : x ∈ closedTube J u :=
  ⟨hn, footprint_bounds_of_branchProfile_nonneg J u x hx⟩

/-- The open normal slab used to avoid the ends of the native tube. -/
def creaseNormalSlab  (u : Site polyCells) : Set (Space m) :=
  {x | |normalCoord u x| < rho m}

theorem creaseNormalSlab_isOpen  (u : Site polyCells) :
    IsOpen (creaseNormalSlab u) := by
  apply isOpen_lt _ continuous_const
  unfold normalCoord
  fun_prop

/-- An explicit open neighborhood of every generic point of this base crease. -/
def baseCreasePlaneNeighborhood  (J : ℕ) (u : Site polyCells)
    (s : Side m) : Set (Space m) :=
  minimalBranchNeighborhood J u s ∩ creaseNormalSlab u

theorem baseCreasePlaneNeighborhood_isOpen  (J : ℕ) (u : Site polyCells)
    (s : Side m) : IsOpen (baseCreasePlaneNeighborhood J u s) :=
  (minimalBranchNeighborhood_isOpen J u s).inter (creaseNormalSlab_isOpen u)

theorem genericBaseCrease_mem_planeNeighborhood {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) (x : Space m)
    (hx : x ∈ genericBaseCrease a u s) : x ∈ baseCreasePlaneNeighborhood J u s := by
  refine ⟨?_, ?_⟩
  · intro t
    rw [hx.2.1]
    exact hx.2.2 t.val t.property
  · change |normalCoord u x| < rho m
    rw [hx.1.2, abs_zero]
    exact rho_pos m

/-- Exact equality with the two supporting planes throughout the explicit
neighborhood; its reverse direction reconstructs literal crease membership. -/
theorem baseCrease_iff_plane_intersection_on {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) (y : Space m)
    (hy : y ∈ baseCreasePlaneNeighborhood J u s) :
    y ∈ baseCrease a u s ↔ normalCoord u y = 0 ∧
      ⟪sideNormal a u s, y - siteCenter u⟫_ℝ =
        eta m * (a.value u : ℝ) / denominator m J := by
  constructor
  · intro h
    exact ⟨h.2, sideFace_plane a u s y h.1⟩
  · rintro ⟨hn, hp⟩
    have hheight := (eq_sideHeight_iff a u s y).mpr hp
    rw [sideHeight_eq_scaled_branch, hn] at hheight
    have hs : branchProfile J u s y = 0 :=
      (mul_eq_zero.mp hheight.symm).resolve_left (native_height_coefficient_ne_zero a u)
    have hall : ∀ t, 0 ≤ branchProfile J u t y := by
      intro t
      rw [← hs]
      exact minimalBranchNeighborhood_minimal J u s hy.1 t
    exact mem_baseCrease_of_branch_zero a u s y
      (mem_closedTube_of_branchProfile_nonneg J u y hy.2.le hall) hn hs

theorem genericBaseCrease_locally_eq_plane_intersection {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) (x : Space m)
    (hx : x ∈ genericBaseCrease a u s) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ baseCrease a u s ↔ normalCoord u y = 0 ∧
        ⟪sideNormal a u s, y - siteCenter u⟫_ℝ =
          eta m * (a.value u : ℝ) / denominator m J :=
  ⟨baseCreasePlaneNeighborhood J u s, baseCreasePlaneNeighborhood_isOpen J u s,
    genericBaseCrease_mem_planeNeighborhood a u s x hx,
    fun y hy => baseCrease_iff_plane_intersection_on a u s y hy⟩

/-- An explicit open neighborhood for the two active side branches. -/
def sideCreasePlaneNeighborhood  (J : ℕ) (u : Site polyCells)
    (s t : Side m) : Set (Space m) :=
  pairBranchNeighborhood J u s t ∩ creaseNormalSlab u

theorem sideCreasePlaneNeighborhood_isOpen  (J : ℕ) (u : Site polyCells)
    (s t : Side m) : IsOpen (sideCreasePlaneNeighborhood J u s t) :=
  (pairBranchNeighborhood_isOpen J u s t).inter (creaseNormalSlab_isOpen u)

theorem genericSideCrease_mem_planeNeighborhood {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (x : Space m)
    (hx : x ∈ genericSideCrease a u s t) :
    x ∈ sideCreasePlaneNeighborhood J u s t := by
  refine ⟨?_, ?_⟩
  · change 0 < min _ _ ∧ _
    rw [← hx.2.2.1, min_self]
    exact ⟨hx.2.1, fun r => hx.2.2.2 r.val r.property.1 r.property.2⟩
  · change |normalCoord u x| < rho m
    rw [hx.1.1.1.2]
    exact siteHeight_abs_lt_rho a u x

/-- Equal side-plane heights force equal branches, using the actual nonzero
prime coefficient. The pair neighborhood then supplies the other branches. -/
theorem sideCrease_iff_plane_intersection_on {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (y : Space m)
    (hy : y ∈ sideCreasePlaneNeighborhood J u s t) :
    y ∈ sideCrease a u s t ↔
      (⟪sideNormal a u s, y - siteCenter u⟫_ℝ =
        eta m * (a.value u : ℝ) / denominator m J) ∧
      (⟪sideNormal a u t, y - siteCenter u⟫_ℝ =
        eta m * (a.value u : ℝ) / denominator m J) := by
  constructor
  · intro h
    exact ⟨sideFace_plane a u s y h.1, sideFace_plane a u t y h.2⟩
  · rintro ⟨hs, ht⟩
    have hhs := (eq_sideHeight_iff a u s y).mpr hs
    have hht := (eq_sideHeight_iff a u t y).mpr ht
    have heq : branchProfile J u s y = branchProfile J u t y := by
      have h := hhs.symm.trans hht
      rw [sideHeight_eq_scaled_branch, sideHeight_eq_scaled_branch] at h
      exact (mul_left_cancel₀ (native_height_coefficient_ne_zero a u)) h
    have hpair := hy.1
    change 0 < min _ _ ∧ _ at hpair
    rw [← heq, min_self] at hpair
    have hmin : ∀ r, branchProfile J u s y ≤ branchProfile J u r y := by
      intro r
      by_cases hrs : r = s
      · rw [hrs]
      by_cases hrt : r = t
      · rw [hrt, heq]
      exact (hpair.2 ⟨r, hrs, hrt⟩).le
    have hregs : y ∈ branchRegion J u s := ⟨hpair.1.le, hmin⟩
    have hregt : y ∈ branchRegion J u t := by
      constructor
      · rw [← heq]; exact hpair.1.le
      · intro r; rw [← heq]; exact hmin r
    have htube : y ∈ closedTube J u :=
      mem_closedTube_of_branchProfile_nonneg J u y hy.2.le
        (fun r => hpair.1.le.trans (hmin r))
    have hgraph : y ∈ keyGraph a u :=
      ⟨htube, hhs.trans (siteHeight_eq_sideHeight a u s y hregs).symm⟩
    exact ⟨⟨hgraph, hregs⟩, ⟨hgraph, hregt⟩⟩

theorem genericSideCrease_locally_eq_plane_intersection {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (x : Space m)
    (hx : x ∈ genericSideCrease a u s t) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ sideCrease a u s t ↔
        (⟪sideNormal a u s, y - siteCenter u⟫_ℝ =
          eta m * (a.value u : ℝ) / denominator m J) ∧
        (⟪sideNormal a u t, y - siteCenter u⟫_ℝ =
          eta m * (a.value u : ℝ) / denominator m J) :=
  ⟨sideCreasePlaneNeighborhood J u s t, sideCreasePlaneNeighborhood_isOpen J u s t,
    genericSideCrease_mem_planeNeighborhood a u s t x hx,
    fun y hy => sideCrease_iff_plane_intersection_on a u s t y hy⟩

/-- Every native signed side slope is nonzero. -/
theorem sideSlope_ne_zero {J : ℕ} (a : Coefficients polyCells J) (u : Site polyCells)
    (s : Side m) : sideSlope a u s ≠ 0 := by
  have ha : (a.value u : ℝ) ≠ 0 := by exact_mod_cast a.nonzero u
  have hp : (sidePrime J s : ℝ) ≠ 0 := by
    exact_mod_cast (keyPrime_prime J _).ne_zero
  have hN : (denominator m J : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_prime m J).ne_zero
  have hsign : sideSign s ≠ 0 := by unfold sideSign; cases s.2 <;> norm_num
  exact div_ne_zero (mul_ne_zero (mul_ne_zero ha hsign) hp) hN

/-- The base and side normals are genuinely independent. -/
theorem base_normals_combination_eq_zero {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) (c d : ℝ)
    (h : c • outward u.1 + d • sideNormal a u s = 0) : c = 0 ∧ d = 0 := by
  have haxis := congrArg (fun v : Space m => ⟪v, siteAxis u s.1⟫_ℝ) h
  have horth : ⟪outward u.1, siteAxis u s.1⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact siteAxis_outward_inner u s.1
  simp only [inner_add_left, real_inner_smul_left, sideNormal, inner_sub_left,
    horth, siteAxis_inner, ↓reduceIte, mul_one, mul_zero, zero_sub,
    zero_add, inner_zero_left] at haxis
  have hd : d = 0 := (mul_eq_zero.mp haxis).resolve_right (neg_ne_zero.mpr (sideSlope_ne_zero a u s))
  have hn := congrArg (fun v : Space m => ⟪v, outward u.1⟫_ℝ) h
  simp [hd, real_inner_smul_left] at hn
  exact ⟨hn, hd⟩

/-- Distinct tangent axes make the two side-plane normals independent. -/
theorem side_normals_combination_eq_zero {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) (c d : ℝ)
    (h : c • sideNormal a u s + d • sideNormal a u t = 0) : c = 0 ∧ d = 0 := by
  have haxis := congrArg (fun v : Space m => ⟪v, siteAxis u s.1⟫_ℝ) h
  have horth : ⟪outward u.1, siteAxis u s.1⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact siteAxis_outward_inner u s.1
  simp only [inner_add_left, real_inner_smul_left, sideNormal, inner_sub_left,
    horth, siteAxis_inner, hst.symm, ↓reduceIte, mul_one, mul_zero,
    zero_sub, sub_zero, add_zero, inner_zero_left] at haxis
  have hc : c = 0 := (mul_eq_zero.mp haxis).resolve_right (neg_ne_zero.mpr (sideSlope_ne_zero a u s))
  have hn := congrArg (fun v : Space m => ⟪v, outward u.1⟫_ℝ) h
  simp [hc, real_inner_smul_left, sideNormal_inner_outward] at hn
  exact ⟨hc, hn⟩

/-- The carrier and native side planes have linearly independent normals. -/
theorem base_normals_linearIndependent {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) :
    LinearIndependent ℝ ![outward u.1, sideNormal a u s] := by
  apply linearIndependent_fin2.mpr
  constructor
  · exact sideNormal_ne_zero a u s
  · intro c hc
    change c • sideNormal a u s = outward u.1 at hc
    have h : (-1 : ℝ) • outward u.1 + c • sideNormal a u s = 0 := by
      rw [hc, neg_one_smul, neg_add_cancel]
    have hz := (base_normals_combination_eq_zero a u s (-1) c h).1
    norm_num at hz

/-- Two native side planes on distinct axes have linearly independent normals. -/
theorem side_normals_linearIndependent {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) :
    LinearIndependent ℝ ![sideNormal a u s, sideNormal a u t] := by
  apply linearIndependent_fin2.mpr
  constructor
  · exact sideNormal_ne_zero a u t
  · intro c hc
    change c • sideNormal a u t = sideNormal a u s at hc
    have h : (-1 : ℝ) • sideNormal a u s + c • sideNormal a u t = 0 := by
      rw [hc, neg_one_smul, neg_add_cancel]
    have hz := (side_normals_combination_eq_zero a u s t hst (-1) c h).1
    norm_num at hz


end
end ProductClosure.NativeCompiler
