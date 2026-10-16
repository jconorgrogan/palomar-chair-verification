module

public import PhysicalRegistration.LocalGraphs
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section


/-!
The concrete zero-extended max-min tent from the recovered registration
manuscript. Its Lipschitz and footprint properties are proved from the
formula, not supplied as fields or assumptions.
-/

namespace PhysicalRegistration
open scoped InnerProductSpace
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def finiteLowerEnvelope (f : ι → E → ℝ) (x : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => f i x)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem finiteLowerEnvelope_le (f : ι → E → ℝ) (x : E) (i : ι) :
    finiteLowerEnvelope f x ≤ f i x :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem finiteLowerEnvelope_lipschitz (f : ι → E → ℝ) (L : ℝ)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * ‖x - y‖) (x y : E) :
    |finiteLowerEnvelope f x - finiteLowerEnvelope f y| ≤ L * ‖x - y‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => f i x)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => f i y)
  change finiteLowerEnvelope f x = f i x at hi
  change finiteLowerEnvelope f y = f j y at hj
  apply abs_le.mpr
  constructor
  · have h := (abs_le.mp (hf i x y)).1
    have hmin := finiteLowerEnvelope_le f y i
    linarith
  · have h := (abs_le.mp (hf j x y)).2
    have hmin := finiteLowerEnvelope_le f x j
    linarith

/-- The exact asymmetric tent before multiplication by its signed height. -/
noncomputable def keyTentProfile (eta : ℝ) (pMinus pPlus : ι → ℝ)
    (axis : ι → E) (x : E) : ℝ :=
  max 0 (finiteLowerEnvelope (fun i x =>
    min (1 + pMinus i * ⟪axis i, x⟫_ℝ / eta)
        (1 - pPlus i * ⟪axis i, x⟫_ℝ / eta)) x)

/-- The manuscript's signed height h=(eta*a/N)*psi. Rational inputs therefore
give its exact rational affine coefficients; the ambient points are real. -/
noncomputable def keyHeight (eta a N : ℝ) (pMinus pPlus : ι → ℝ)
    (axis : ι → E) (x : E) : ℝ :=
  (eta * a / N) * keyTentProfile eta pMinus pPlus axis x

theorem affine_unit_axis_lipschitz (e : E) (he : ‖e‖ = 1)
    (b c L : ℝ) (hb : |b| ≤ L) (x y : E) :
    |(c + b * ⟪e, x⟫_ℝ) - (c + b * ⟪e, y⟫_ℝ)| ≤ L * ‖x - y‖ := by
  have hid : (c + b * ⟪e, x⟫_ℝ) - (c + b * ⟪e, y⟫_ℝ) =
      b * ⟪e, x - y⟫_ℝ := by
    rw [inner_sub_right]
    ring
  rw [hid, abs_mul]
  have hinner : |⟪e, x - y⟫_ℝ| ≤ ‖x - y‖ := by
    simpa [he] using abs_real_inner_le_norm e (x - y)
  exact (mul_le_mul_of_nonneg_left hinner (abs_nonneg b)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem keyTentProfile_lipschitz (eta pMax : ℝ)
    (heta : 0 < eta) (hMax : 0 ≤ pMax)
    (pMinus pPlus : ι → ℝ) (axis : ι → E)
    (hMinus : ∀ i, 0 ≤ pMinus i ∧ pMinus i ≤ pMax)
    (hPlus : ∀ i, 0 ≤ pPlus i ∧ pPlus i ≤ pMax)
    (haxis : ∀ i, ‖axis i‖ = 1) (x y : E) :
    |keyTentProfile eta pMinus pPlus axis x -
      keyTentProfile eta pMinus pPlus axis y| ≤ (pMax / eta) * ‖x - y‖ := by
  have hbranches : ∀ i x y,
      |min (1 + pMinus i * ⟪axis i, x⟫_ℝ / eta)
          (1 - pPlus i * ⟪axis i, x⟫_ℝ / eta) -
        min (1 + pMinus i * ⟪axis i, y⟫_ℝ / eta)
          (1 - pPlus i * ⟪axis i, y⟫_ℝ / eta)| ≤ (pMax / eta) * ‖x - y‖ := by
    intro i x y
    have hm : |pMinus i / eta| ≤ pMax / eta := by
      rw [abs_of_nonneg (div_nonneg (hMinus i).1 heta.le)]
      exact div_le_div_of_nonneg_right (hMinus i).2 heta.le
    have hp : |-(pPlus i / eta)| ≤ pMax / eta := by
      rw [abs_neg, abs_of_nonneg (div_nonneg (hPlus i).1 heta.le)]
      exact div_le_div_of_nonneg_right (hPlus i).2 heta.le
    have hbm := affine_unit_axis_lipschitz (axis i) (haxis i)
      (pMinus i / eta) 1 (pMax / eta) hm x y
    have hbp := affine_unit_axis_lipschitz (axis i) (haxis i)
      (-(pPlus i / eta)) 1 (pMax / eta) hp x y
    have hm' : |(1 + pMinus i * ⟪axis i, x⟫_ℝ / eta) -
        (1 + pMinus i * ⟪axis i, y⟫_ℝ / eta)| ≤ (pMax / eta) * ‖x - y‖ := by
      convert hbm using 1 <;> congr 1 <;> ring
    have hp' : |(1 - pPlus i * ⟪axis i, x⟫_ℝ / eta) -
        (1 - pPlus i * ⟪axis i, y⟫_ℝ / eta)| ≤ (pMax / eta) * ‖x - y‖ := by
      convert hbp using 1 <;> congr 1 <;> ring
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hm' hp')
  have hmin := finiteLowerEnvelope_lipschitz _ (pMax / eta) hbranches x y
  unfold keyTentProfile
  exact (abs_max_sub_max_le_max _ _ _ _).trans
    (max_le (by simp; positivity) hmin)

/-- Global bound valid across base creases, side creases, the apex, and the
zero extension. No derivative or smoothness assumption is needed. -/
theorem keyHeight_lipschitz (eta a N J pMax : ℝ)
    (heta : 0 < eta) (hN : 0 < N) (ha : |a| ≤ J) (hMax : 0 ≤ pMax)
    (pMinus pPlus : ι → ℝ) (axis : ι → E)
    (hMinus : ∀ i, 0 ≤ pMinus i ∧ pMinus i ≤ pMax)
    (hPlus : ∀ i, 0 ≤ pPlus i ∧ pPlus i ≤ pMax)
    (haxis : ∀ i, ‖axis i‖ = 1) (x y : E) :
    |keyHeight eta a N pMinus pPlus axis x -
      keyHeight eta a N pMinus pPlus axis y| ≤ (J * pMax / N) * ‖x - y‖ := by
  have hpsi := keyTentProfile_lipschitz eta pMax heta hMax
    pMinus pPlus axis hMinus hPlus haxis x y
  unfold keyHeight
  rw [← mul_sub, abs_mul]
  calc
    |eta * a / N| * |keyTentProfile eta pMinus pPlus axis x -
        keyTentProfile eta pMinus pPlus axis y|
        ≤ |eta * a / N| * ((pMax / eta) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hpsi (abs_nonneg _)
    _ = (|a| * pMax / N) * ‖x - y‖ := by
      rw [abs_div, abs_mul, abs_of_pos heta, abs_of_pos hN]
      field_simp
    _ ≤ (J * pMax / N) * ‖x - y‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right ha hMax) hN.le

theorem keyTentProfile_zero_below (eta : ℝ) (heta : 0 < eta)
    (pMinus pPlus : ι → ℝ) (axis : ι → E) (x : E) (i : ι)
    (hp : 0 < pMinus i) (hx : ⟪axis i, x⟫_ℝ ≤ -eta / pMinus i) :
    keyTentProfile eta pMinus pPlus axis x = 0 := by
  have hmul := (le_div_iff₀ hp).mp hx
  have hdiv : pMinus i * ⟪axis i, x⟫_ℝ / eta ≤ -1 :=
    (div_le_iff₀ heta).mpr (by nlinarith)
  have hbranch : 1 + pMinus i * ⟪axis i, x⟫_ℝ / eta ≤ 0 := by linarith
  have hmin := finiteLowerEnvelope_le
    (fun i x => min (1 + pMinus i * ⟪axis i, x⟫_ℝ / eta)
      (1 - pPlus i * ⟪axis i, x⟫_ℝ / eta)) x i
  exact max_eq_left ((hmin.trans (min_le_left _ _)).trans hbranch)

theorem keyTentProfile_zero_above (eta : ℝ) (heta : 0 < eta)
    (pMinus pPlus : ι → ℝ) (axis : ι → E) (x : E) (i : ι)
    (hp : 0 < pPlus i) (hx : eta / pPlus i ≤ ⟪axis i, x⟫_ℝ) :
    keyTentProfile eta pMinus pPlus axis x = 0 := by
  have hmul := (div_le_iff₀ hp).mp hx
  have hdiv : 1 ≤ pPlus i * ⟪axis i, x⟫_ℝ / eta :=
    (le_div_iff₀ heta).mpr (by nlinarith)
  have hbranch : 1 - pPlus i * ⟪axis i, x⟫_ℝ / eta ≤ 0 := by linarith
  have hmin := finiteLowerEnvelope_le
    (fun i x => min (1 + pMinus i * ⟪axis i, x⟫_ℝ / eta)
      (1 - pPlus i * ⟪axis i, x⟫_ℝ / eta)) x i
  exact max_eq_left ((hmin.trans (min_le_right _ _)).trans hbranch)

/-- Every point where the tent is active lies strictly inside the actual
asymmetric rectangular footprint. At and outside its boundary it is zero. -/
theorem keyTentProfile_active_footprint (eta : ℝ) (heta : 0 < eta)
    (pMinus pPlus : ι → ℝ) (axis : ι → E)
    (hMinus : ∀ i, 0 < pMinus i) (hPlus : ∀ i, 0 < pPlus i) (x : E)
    (hx : keyTentProfile eta pMinus pPlus axis x ≠ 0) :
    ∀ i, -eta / pMinus i < ⟪axis i, x⟫_ℝ ∧
      ⟪axis i, x⟫_ℝ < eta / pPlus i := by
  intro i
  constructor
  · by_contra hi
    exact hx (keyTentProfile_zero_below eta heta pMinus pPlus axis x i
      (hMinus i) (le_of_not_gt hi))
  · by_contra hi
    exact hx (keyTentProfile_zero_above eta heta pMinus pPlus axis x i
      (hPlus i) (le_of_not_gt hi))

/-- The signed height has the same support containment, for either sign of a. -/
theorem keyHeight_active_footprint (eta a N : ℝ) (heta : 0 < eta)
    (pMinus pPlus : ι → ℝ) (axis : ι → E)
    (hMinus : ∀ i, 0 < pMinus i) (hPlus : ∀ i, 0 < pPlus i) (x : E)
    (hx : keyHeight eta a N pMinus pPlus axis x ≠ 0) :
    ∀ i, -eta / pMinus i < ⟪axis i, x⟫_ℝ ∧
      ⟪axis i, x⟫_ℝ < eta / pPlus i := by
  apply keyTentProfile_active_footprint eta heta pMinus pPlus axis hMinus hPlus x
  intro hz
  exact hx (by simp [keyHeight, hz])

theorem asymmetric_footprint_coordinate_bound (eta pMinus pPlus v : ℝ)
    (heta : 0 ≤ eta) (hm : 1 ≤ pMinus) (hp : 1 ≤ pPlus)
    (hv : -eta / pMinus < v ∧ v < eta / pPlus) : |v| ≤ eta := by
  have hm0 : 0 < pMinus := by linarith
  have hp0 : 0 < pPlus := by linarith
  have hmdiv : eta / pMinus ≤ eta :=
    (div_le_iff₀ hm0).mpr (by nlinarith)
  have hpdiv : eta / pPlus ≤ eta :=
    (div_le_iff₀ hp0).mpr (by nlinarith)
  apply abs_le.mpr
  rw [neg_div] at hv
  constructor <;> linarith [hv.1, hv.2]

/-- Each positive coordinate k/(4d) of the native orbit center is below 1/4.
Signed axis permutations preserve this absolute-value conclusion. -/
theorem orbit_offset_below_quarter (d k : ℝ) (hd : 0 < d)
    (hk : 0 ≤ k) (hkd : k < d) : |k / (4 * d)| < 1 / 4 := by
  rw [abs_of_nonneg (div_nonneg hk (by positivity))]
  apply (div_lt_iff₀ (by positivity : 0 < 4 * d)).mpr
  linarith

/-- Concrete separation from either integer edge of a unit facet: q is a
native orbit offset and v is any coordinate in the key's footprint. -/
theorem key_support_facet_margin (eta q v : ℝ)
    (hq : |q| < 1 / 4) (hv : |v| ≤ eta) :
    1 / 4 - eta < 1 / 2 + q + v ∧
      1 / 2 + q + v < 3 / 4 + eta := by
  rcases abs_lt.mp hq with ⟨hqlo, hqhi⟩
  rcases abs_le.mp hv with ⟨hvlo, hvhi⟩
  constructor <;> linarith

theorem key_support_inside_unit_facet (eta q v : ℝ)
    (heta : eta < 1 / 4) (hq : |q| < 1 / 4) (hv : |v| ≤ eta) :
    0 < 1 / 2 + q + v ∧ 1 / 2 + q + v < 1 := by
  have h := key_support_facet_margin eta q v hq hv
  constructor <;> linarith [h.1, h.2]

/-- The manuscript's numerical choice is much stronger than the slope bound
needed by the checked no-three-local-graphs theorem. -/
theorem chosen_slope_lt_half (d J pMax N : ℝ)
    (hd : 3 ≤ d) (hJ : 0 < J) (hp : 0 < pMax)
    (hN : 32 * d * J * pMax < N) :
    0 ≤ J * pMax / N ∧ J * pMax / N < 1 / 2 := by
  have hd0 : 0 < d := by linarith
  have hN0 : 0 < N := (by positivity : 0 < 32 * d * J * pMax).trans hN
  have hprod : 0 < J * pMax := mul_pos hJ hp
  have hscale : 2 * J * pMax < 32 * d * J * pMax := by
    have haux : 0 < (32 * d - 2) * (J * pMax) :=
      mul_pos (by linarith) hprod
    nlinarith
  constructor
  · exact div_nonneg hprod.le hN0.le
  · apply (div_lt_iff₀ hN0).mpr
    linarith

#print axioms keyTentProfile_lipschitz
#print axioms keyHeight_lipschitz
#print axioms keyHeight_active_footprint
#print axioms key_support_facet_margin
#print axioms chosen_slope_lt_half
end PhysicalRegistration
