module

public import ProductClosure.Polycube
public import PhysicalRegistration.NativeChair

@[expose] public section

/-!
Literal dense full-frame compiler on an arbitrary finite integer polycube.
The arithmetic tent and prime parameters are identical to the verified chair
construction. No registration, contact legality, or tiling existence is assumed.
-/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section

abbrev Space (m : ℕ) := Polycube.Space (m + 1)
abbrev Frame (m : ℕ) := PhysicalRegistration.NativeChair.Frame m
abbrev Facet {m : ℕ} (S : Finset (Polycube.LatticeIndex (m + 1))) := Polycube.Facet S
abbrev Site {m : ℕ} (S : Finset (Polycube.LatticeIndex (m + 1))) := Facet S × Frame m

variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

def sign (b : Bool) : ℝ := if b then 1 else -1

def normalIndex (f : Facet S) : Fin (m + 1) := f.axis
def normalSign (f : Facet S) : ℝ := sign f.positive
def facetCenter (f : Facet S) : Space m := Polycube.facetCenter f
def outward (f : Facet S) : Space m :=
  normalSign f • EuclideanSpace.single (normalIndex f) 1

def tangentAxis (f : Facet S) (j : Fin m) : Space m :=
  EuclideanSpace.single ((normalIndex f).succAbove j) 1

def siteAxis (u : Site S) (j : Fin m) : Space m :=
  sign (u.2.2 j) • tangentAxis u.1 (u.2.1 j)

/-- The exact free-orbit seed, indexed from zero in Lean. -/
def q0  (j : Fin m) : ℝ :=
  ((j.val : ℝ) + 1) / (4 * ((m : ℝ) + 1))

def siteOffset  (u : Site S) : Space m :=
  ∑ j : Fin m, q0 j • siteAxis u j

def siteCenter  (u : Site S) : Space m :=
  facetCenter u.1 + siteOffset u

def delta (m : ℕ) : ℝ := 1 / (16 * ((m : ℝ) + 1))
def eta (m : ℕ) : ℝ := 1 / (128 * ((m : ℝ) + 1))
def rho (m : ℕ) : ℝ := 1 / (32 * ((m : ℝ) + 1))

/-- The least prime strictly above a natural number. -/
def nextPrime (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))

theorem nextPrime_spec (n : ℕ) : n < nextPrime n ∧ Nat.Prime (nextPrime n) := by
  have h := Nat.find_spec (Nat.exists_infinite_primes (n + 1))
  exact ⟨h.1, h.2⟩

theorem nextPrime_min (n p : ℕ) (hn : n < p) (hp : Nat.Prime p) :
    nextPrime n ≤ p := Nat.find_min' _ ⟨hn, hp⟩

/-- Consecutive primes strictly above `J`, in increasing order. -/
def keyPrime (J : ℕ) : ℕ → ℕ
  | 0 => nextPrime J
  | n + 1 => nextPrime (keyPrime J n)

def pMinus  (J : ℕ) (j : Fin m) : ℝ := keyPrime J (2 * j.val)
def pPlus  (J : ℕ) (j : Fin m) : ℝ := keyPrime J (2 * j.val + 1)
def pMax (m J : ℕ) : ℕ := keyPrime J (2 * m - 1)

/-- The manuscript's exact least-prime denominator. -/
def denominator (m J : ℕ) : ℕ := nextPrime (32 * (m + 1) * J * pMax m J)

theorem keyPrime_prime (J n : ℕ) : Nat.Prime (keyPrime J n) := by
  cases n with
  | zero => exact (nextPrime_spec J).2
  | succ n => exact (nextPrime_spec (keyPrime J n)).2

theorem keyPrime_strictMono (J : ℕ) : StrictMono (keyPrime J) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (nextPrime_spec (keyPrime J n)).1

theorem keyPrime_gt (J n : ℕ) : J < keyPrime J n :=
  (nextPrime_spec J).1.trans_le ((keyPrime_strictMono J).monotone (Nat.zero_le n))

theorem pMinus_pos  (J : ℕ) (j : Fin m) : 0 < pMinus J j := by
  unfold pMinus
  exact_mod_cast (keyPrime_prime J (2 * j.val)).pos

theorem pPlus_pos  (J : ℕ) (j : Fin m) : 0 < pPlus J j := by
  unfold pPlus
  exact_mod_cast (keyPrime_prime J (2 * j.val + 1)).pos

theorem pMinus_le_pMax  (J : ℕ) (j : Fin m) :
    pMinus J j ≤ (pMax m J : ℝ) := by
  have hj : 2 * j.val ≤ 2 * m - 1 := by omega
  unfold pMinus pMax
  exact_mod_cast (keyPrime_strictMono J).monotone hj

theorem pPlus_le_pMax  (J : ℕ) (j : Fin m) :
    pPlus J j ≤ (pMax m J : ℝ) := by
  have hj : 2 * j.val + 1 ≤ 2 * m - 1 := by omega
  unfold pPlus pMax
  exact_mod_cast (keyPrime_strictMono J).monotone hj

theorem denominator_prime (m J : ℕ) : Nat.Prime (denominator m J) :=
  (nextPrime_spec _).2

theorem denominator_gt (m J : ℕ) :
    32 * (m + 1) * J * pMax m J < denominator m J := (nextPrime_spec _).1

/-- Explicit coefficient input. No contact-graph, chirality, or component
 theorem is hidden in this structure. The bound is in the real field to feed
 the checked analytic estimates without an implicit cast convention. -/
structure Coefficients (S : Finset (Polycube.LatticeIndex (m + 1))) (J : ℕ) where
  value : Site S → ℤ
  bound : ∀ u, |(value u : ℝ)| ≤ (J : ℝ)
  nonzero : ∀ u, value u ≠ 0

/-- Outward normal coordinate centered at a native site. -/
def normalCoord  (u : Site S) (x : Space m) : ℝ :=
  ⟪outward u.1, x - siteCenter u⟫_ℝ

/-- The coordinate in column `j` of the keyed native tangent frame. -/
def tangentCoord  (u : Site S) (x : Space m) (j : Fin m) : ℝ :=
  ⟪siteAxis u j, x - siteCenter u⟫_ℝ

/-- The exact asymmetric closed footprint `K`, in keyed coordinates. -/
def footprint (m J : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {v | ∀ j, -eta m / pMinus J j ≤ v j ∧ v j ≤ eta m / pPlus J j}

/-- The actual closed ambient tube, with normal half-width `rho`. -/
def closedTube  (J : ℕ) (u : Site S) : Set (Space m) :=
  {x | |normalCoord u x| ≤ rho m ∧
    ∀ j, -eta m / pMinus J j ≤ tangentCoord u x j ∧
      tangentCoord u x j ≤ eta m / pPlus J j}

/-- The exact signed normal graph, expressed using the proved max-min tent. -/
def siteHeight {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (x : Space m) : ℝ :=
  keyHeight (eta m) (a.value u : ℝ) (denominator m J : ℝ)
    (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u)

/-- Material is on the inward side of the signed graph. -/
def siteHypograph {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : Set (Space m) :=
  {x | normalCoord u x ≤ siteHeight a u x}

/-- The replacement is restricted to the closed asymmetric tube. -/
def replacementPiece {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : Set (Space m) :=
  closedTube J u ∩ siteHypograph a u

/-- The literal assembled set. Only tube interiors are removed from the
 carrier, and closed hypograph pieces are inserted. Whether this set is a
 ball and whether different native tubes are disjoint are separate theorems. -/
def body {J : ℕ} [NeZero m] (a : Coefficients S J) : Set (Space m) :=
  (Polycube.carrier S \ ⋃ u : Site S, interior (closedTube J u)) ∪
    ⋃ u : Site S, replacementPiece a u

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

@[simp] theorem abs_normalSign (f : Facet S) : |normalSign f| = 1 := abs_sign _

@[simp] theorem outward_unit  (f : Facet S) : ‖outward f‖ = 1 := by
  simp [outward, norm_smul, Real.norm_eq_abs]

@[simp] theorem siteAxis_unit  (u : Site S) (j : Fin m) :
    ‖siteAxis u j‖ = 1 := by
  simp [siteAxis, tangentAxis, norm_smul, Real.norm_eq_abs]

@[simp] theorem siteAxis_outward_inner  (u : Site S) (j : Fin m) :
    ⟪siteAxis u j, outward u.1⟫_ℝ = 0 := by
  simp [siteAxis, tangentAxis, outward, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.inner_single_left]

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

/-- The signed permuted tangent columns form an orthonormal family. -/
theorem siteAxis_inner  (u : Site S) (i j : Fin m) :
    ⟪siteAxis u i, siteAxis u j⟫_ℝ = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp
  · simp [siteAxis, tangentAxis, real_inner_smul_left, real_inner_smul_right,
      EuclideanSpace.inner_single_left, h]

@[simp] theorem outward_siteOffset_inner  (u : Site S) :
    ⟪outward u.1, siteOffset u⟫_ℝ = 0 := by
  have horth : ∀ j, ⟪outward u.1, siteAxis u j⟫_ℝ = 0 := by
    intro j
    rw [real_inner_comm]
    exact siteAxis_outward_inner u j
  simp [siteOffset, inner_sum, real_inner_smul_right, horth]

@[simp] theorem siteAxis_siteOffset_inner  (u : Site S) (j : Fin m) :
    ⟪siteAxis u j, siteOffset u⟫_ℝ = q0 j := by
  simp [siteOffset, inner_sum, real_inner_smul_right, siteAxis_inner]

theorem outward_inner_coordinate  (f : Facet S) (v : Space m) :
    ⟪outward f, v⟫_ℝ = normalSign f * v (normalIndex f) := by
  simp [outward, real_inner_smul_left, EuclideanSpace.inner_single_left]

theorem siteAxis_inner_coordinate  (u : Site S) (j : Fin m) (v : Space m) :
    ⟪siteAxis u j, v⟫_ℝ =
      sign (u.2.2 j) * v ((normalIndex u.1).succAbove (u.2.1 j)) := by
  simp [siteAxis, tangentAxis, real_inner_smul_left, EuclideanSpace.inner_single_left]

@[simp] theorem siteOffset_normal  (u : Site S) :
    siteOffset u (normalIndex u.1) = 0 := by
  have h := outward_siteOffset_inner u
  simp only [outward, real_inner_smul_left, EuclideanSpace.inner_single_left,
    map_one, one_mul] at h
  have hn : normalSign u.1 ≠ 0 := by
    intro hz
    have := abs_normalSign u.1
    simp [hz] at this
  exact (mul_eq_zero.mp h).resolve_left hn

theorem siteOffset_tangent  (u : Site S) (j : Fin m) :
    siteOffset u ((normalIndex u.1).succAbove (u.2.1 j)) = sign (u.2.2 j) * q0 j := by
  have h := siteAxis_siteOffset_inner u j
  rw [siteAxis_inner_coordinate] at h
  cases hb : u.2.2 j <;> simp [sign, hb] at h ⊢ <;> linarith

theorem q0_pos  (j : Fin m) : 0 < q0 j := by unfold q0; positivity

theorem abs_q0_lt_quarter  (j : Fin m) : |q0 j| < 1 / 4 := by
  apply orbit_offset_below_quarter
  · positivity
  · positivity
  · exact_mod_cast Nat.succ_lt_succ j.isLt

/-- Every native offset has strict coordinate distance less than one quarter. -/
theorem siteOffset_coordinate_bound  (u : Site S) (k : Fin (m + 1)) :
    |siteOffset u k| < 1 / 4 := by
  by_cases hk : k = normalIndex u.1
  · subst k
    simp
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
    let l : Fin m := u.2.1.symm j
    have hl : u.2.1 l = j := u.2.1.apply_symm_apply j
    rw [← hj, ← hl, siteOffset_tangent, abs_mul, abs_sign, one_mul]
    exact abs_q0_lt_quarter l

theorem abs_normalCoord  (u : Site S) (x : Space m) :
    |normalCoord u x| =
      |x (normalIndex u.1) - siteCenter u (normalIndex u.1)| := by
  simp [normalCoord, outward_inner_coordinate, abs_mul]

theorem abs_tangentCoord  (u : Site S) (x : Space m) (j : Fin m) :
    |tangentCoord u x j| =
      |x ((normalIndex u.1).succAbove (u.2.1 j)) -
        siteCenter u ((normalIndex u.1).succAbove (u.2.1 j))| := by
  simp [tangentCoord, siteAxis_inner_coordinate, abs_mul]

/-- A site shift changes no carrier-normal coordinate. -/
theorem normalCoord_eq_facet  (u : Site S) (x : Space m) :
    normalCoord u x = ⟪outward u.1, x - facetCenter u.1⟫_ℝ := by
  simp [normalCoord, siteCenter, inner_sub_right, inner_add_right]

@[simp] theorem normalCoord_center  (u : Site S) :
    normalCoord u (siteCenter u) = 0 := by simp [normalCoord]

@[simp] theorem tangentCoord_center  (u : Site S) (j : Fin m) :
    tangentCoord u (siteCenter u) j = 0 := by simp [tangentCoord]

theorem eta_pos (m : ℕ) : 0 < eta m := by unfold eta; positivity

theorem rho_pos (m : ℕ) : 0 < rho m := by unfold rho; positivity

theorem eta_lt_rho (m : ℕ) : eta m < rho m := by
  unfold eta rho
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- The concrete native signed height inherits the previously checked
 global Lipschitz estimate, now with all axis and prime hypotheses discharged. -/
theorem siteHeight_lipschitz {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (x y : Space m) :
    |siteHeight a u x - siteHeight a u y| ≤
      ((J : ℝ) * pMax m J / denominator m J) * ‖x - y‖ := by
  have h := keyHeight_lipschitz (eta m) (a.value u : ℝ) (denominator m J : ℝ)
    (J : ℝ) (pMax m J : ℝ) (eta_pos m)
    (by exact_mod_cast (denominator_prime m J).pos) (a.bound u) (Nat.cast_nonneg _)
    (pMinus J) (pPlus J) (siteAxis u)
    (fun j => ⟨(pMinus_pos J j).le, pMinus_le_pMax J j⟩)
    (fun j => ⟨(pPlus_pos J j).le, pPlus_le_pMax J j⟩)
    (siteAxis_unit u) (x - siteCenter u) (y - siteCenter u)
  simpa only [siteHeight, sub_sub_sub_cancel_right] using h

theorem siteHeight_normal_shift {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (x : Space m) (s : ℝ) :
    siteHeight a u (x + s • outward u.1) = siteHeight a u x := by
  have h := keyHeight_normal_shift (eta m) (a.value u : ℝ) (denominator m J : ℝ)
    (pMinus J) (pPlus J) (siteAxis u) (outward u.1)
    (siteAxis_outward_inner u) (x - siteCenter u) s
  have hid : x + s • outward u.1 - siteCenter u = x - siteCenter u + s • outward u.1 := by abel
  simpa only [siteHeight, hid] using h

/-- The actual native tent takes values between zero and one everywhere. -/
theorem native_profile_range  [NeZero m] (J : ℕ) (u : Site S) (v : Space m) :
    0 ≤ keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) v ∧
    keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) v ≤ 1 := by
  let j : Fin m := 0
  have hmin := finiteLowerEnvelope_le
    (fun i v => min (1 + pMinus J i * ⟪siteAxis u i, v⟫_ℝ / eta m)
      (1 - pPlus J i * ⟪siteAxis u i, v⟫_ℝ / eta m)) v j
  have hb : min (1 + pMinus J j * ⟪siteAxis u j, v⟫_ℝ / eta m)
      (1 - pPlus J j * ⟪siteAxis u j, v⟫_ℝ / eta m) ≤ 1 := by
    by_cases hv : 0 ≤ ⟪siteAxis u j, v⟫_ℝ
    · have hp := div_nonneg (mul_nonneg (pPlus_pos J j).le hv) (eta_pos m).le
      exact (min_le_right _ _).trans (by linarith)
    · have hp := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (pMinus_pos J j).le (le_of_not_ge hv))
        (eta_pos m).le
      exact (min_le_left _ _).trans (by linarith)
  exact ⟨le_max_left _ _, max_le (by norm_num) (hmin.trans hb)⟩

/-- The signed graph never exceeds its advertised absolute height. -/
theorem siteHeight_abs_le {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (x : Space m) :
    |siteHeight a u x| ≤ eta m * (J : ℝ) / denominator m J := by
  have hN : 0 < (denominator m J : ℝ) := by exact_mod_cast (denominator_prime m J).pos
  have hprofile := native_profile_range J u (x - siteCenter u)
  unfold siteHeight keyHeight
  rw [abs_mul, abs_div, abs_mul, abs_of_pos (eta_pos m), abs_of_pos hN,
    abs_of_nonneg hprofile.1]
  calc
    eta m * |(a.value u : ℝ)| / denominator m J *
        keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u)
      ≤ eta m * |(a.value u : ℝ)| / denominator m J * 1 :=
        mul_le_mul_of_nonneg_left hprofile.2
          (div_nonneg (mul_nonneg (eta_pos m).le (abs_nonneg _)) hN.le)
    _ ≤ eta m * (J : ℝ) / denominator m J := by
      rw [mul_one]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (a.bound u) (eta_pos m).le) hN.le

theorem denominator_gt_coefficient_bound (m J : ℕ) : J < denominator m J := by
  have hp : 1 ≤ pMax m J := (keyPrime_prime J (2 * m - 1)).one_lt.le
  have hfactor : 1 ≤ 32 * (m + 1) := by omega
  have h := Nat.mul_le_mul_right J hfactor
  have h' := Nat.mul_le_mul_left (32 * (m + 1) * J) hp
  exact (by nlinarith : J ≤ 32 * (m + 1) * J * pMax m J).trans_lt (denominator_gt m J)

/-- Graph points are strictly inside the tube's normal strip, for every
 allowed coefficient input and either sign of the height. -/
theorem siteHeight_abs_lt_rho {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (x : Space m) : |siteHeight a u x| < rho m := by
  have hN : 0 < (denominator m J : ℝ) := by exact_mod_cast (denominator_prime m J).pos
  have hJ : (J : ℝ) < denominator m J := by exact_mod_cast denominator_gt_coefficient_bound m J
  have hamp : eta m * (J : ℝ) / denominator m J < eta m := by
    apply (div_lt_iff₀ hN).mpr
    exact mul_lt_mul_of_pos_left hJ (eta_pos m)
  exact (siteHeight_abs_le a u x).trans_lt (hamp.trans (eta_lt_rho m))


end
end ProductClosure.NativeCompiler
