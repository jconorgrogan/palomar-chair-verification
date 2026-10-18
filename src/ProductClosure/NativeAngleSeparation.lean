module

public import ProductClosure.PrimeAngleSeparation
public import ProductClosure.KeyCreaseGeometry

@[expose] public section

/-!
# Prime-label separation for actual native normal-angle invariants

The normal lines are those of the literal native affine key branches. Equality
of base invariants recovers the coefficient magnitude and signed side label;
a base invariant cannot equal a distinct-axis side-side invariant. These facts
are also transported by arbitrary ambient isometric bijections. They do not
assert that boundary contact preserves a crease or supplies a companion key.
-/

namespace ProductClosure.NativeCompiler
open PhysicalRegistration
open scoped InnerProductSpace
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- The positive, integral numerator of a native slope magnitude. -/
def slopeNumerator {J : ℕ} (a : Coefficients S J) (u : Site S) (s : Side m) : ℕ :=
  (a.value u).natAbs * sidePrime J s

theorem coefficient_natAbs_bounds {J : ℕ} (a : Coefficients S J) (u : Site S) :
    0 < (a.value u).natAbs ∧ (a.value u).natAbs ≤ J := by
  refine ⟨Int.natAbs_pos.mpr (a.nonzero u), ?_⟩
  have h : ((a.value u).natAbs : ℝ) ≤ J := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using a.bound u
  exact_mod_cast h

theorem sidePrime_index_lt  (s : Side m) :
    2 * s.1.val + (if s.2 then 1 else 0) < 2 * m := by
  have hs := s.1.isLt
  cases s.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem sidePrime_injective  (J : ℕ) : Function.Injective (sidePrime (m := m) J) := by
  intro s t h
  have hi := (keyPrime_strictMono J).injective h
  change 2 * s.1.val + (if s.2 then 1 else 0) =
    2 * t.1.val + (if t.2 then 1 else 0) at hi
  rcases s with ⟨i, b⟩
  rcases t with ⟨j, c⟩
  cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi ⊢
  all_goals first | omega | (have hij : i = j := Fin.ext (by omega); simp [hij])

theorem slopeNumerator_bounds {J : ℕ} (a : Coefficients S J)
    (u : Site S) (s : Side m) :
    0 < slopeNumerator a u s ∧ slopeNumerator a u s < denominator m J := by
  have ha := coefficient_natAbs_bounds a u
  exact native_slope_numerator_bounds ha.1 ha.2 (sidePrime_index_lt s)

/-- The sign of the coefficient and the side orientation disappear upon
squaring, leaving the exact positive integral slope numerator. -/
theorem sideSlope_sq {J : ℕ} (a : Coefficients S J) (u : Site S) (s : Side m) :
    sideSlope a u s ^ 2 = ((slopeNumerator a u s : ℝ) / denominator m J) ^ 2 := by
  simp only [sideSlope, slopeNumerator, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs,
    div_pow, mul_pow, sq_abs]
  have hs : sideSign s ^ 2 = 1 := by
    unfold sideSign
    cases s.2 <;> norm_num
  rw [hs, mul_one]

/-- Equality of actual base normal-line invariants determines the absolute
integer coefficient and the full signed-axis label, even across different
sites and coefficient records. -/
theorem base_normalCosSq_injective {J : ℕ} (a b : Coefficients S J)
    (u v : Site S) (s t : Side m)
    (h : normalCosSq (sideNormal a u s) (outward u.1) =
      normalCosSq (sideNormal b v t) (outward v.1)) :
    |a.value u| = |b.value v| ∧ s = t := by
  rw [base_normalCosSq, base_normalCosSq] at h
  have hs : sideSlope a u s ^ 2 = sideSlope b v t ^ 2 := by
    simpa only [one_div, inv_inj, add_right_inj] using h
  rw [sideSlope_sq, sideSlope_sq, div_pow, div_pow] at hs
  have hN : (denominator m J : ℝ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (denominator_prime m J).ne_zero)
  have heq : slopeNumerator a u s = slopeNumerator b v t := by
    have hs' := (div_left_inj' hN).mp hs
    have habs := (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp hs'
    exact_mod_cast habs
  have ha := coefficient_natAbs_bounds a u
  have hb := coefficient_natAbs_bounds b v
  have hprod := bounded_prime_products_injective
    (keyPrime_prime J _) (keyPrime_prime J _) (keyPrime_gt J _) (keyPrime_gt J _)
    ha.1 hb.1 ha.2 hb.2 heq
  refine ⟨?_, sidePrime_injective J hprod.2⟩
  simpa only [Int.natCast_natAbs] using congrArg (fun n : ℕ => (n : ℤ)) hprod.1

/-- A base normal-line angle cannot be a distinct-axis side-side normal-line
angle in any other native key with the same construction parameters. -/
theorem base_normalCosSq_ne_side_normalCosSq {J : ℕ} (a b : Coefficients S J)
    (u v : Site S) (s t r : Side m) (htr : t.1 ≠ r.1) :
    normalCosSq (sideNormal a u s) (outward u.1) ≠
      normalCosSq (sideNormal b v t) (sideNormal b v r) := by
  intro h
  rw [base_normalCosSq, side_normalCosSq b v t r htr] at h
  have heq : 1 + sideSlope a u s ^ 2 =
      (1 + sideSlope b v t ^ 2) * (1 + sideSlope b v r ^ 2) := by
    simpa only [one_div, inv_inj] using h
  rw [sideSlope_sq, sideSlope_sq, sideSlope_sq] at heq
  have hN : (denominator m J : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_prime m J).ne_zero
  have hreal : (denominator m J : ℝ) ^ 2 *
      ((slopeNumerator a u s : ℝ) ^ 2 - (slopeNumerator b v t : ℝ) ^ 2 -
        (slopeNumerator b v r : ℝ) ^ 2) =
      (slopeNumerator b v t : ℝ) ^ 2 * (slopeNumerator b v r : ℝ) ^ 2 := by
    field_simp [hN] at heq
    nlinarith [heq]
  have hint : (denominator m J : ℤ) ^ 2 *
      ((slopeNumerator a u s : ℤ) ^ 2 - (slopeNumerator b v t : ℤ) ^ 2 -
        (slopeNumerator b v r : ℤ) ^ 2) =
      (slopeNumerator b v t : ℤ) ^ 2 * (slopeNumerator b v r : ℤ) ^ 2 := by
    exact_mod_cast hreal
  have hb := slopeNumerator_bounds b v t
  have hc := slopeNumerator_bounds b v r
  exact prime_angle_equation_impossible (denominator_prime m J)
    hb.1 hb.2 hc.1 hc.2 (slopeNumerator a u s : ℤ) hint

/-- Orthogonal normal transport induced by any ambient isometric bijection;
Mazur–Ulam supplies its linear part without a placement restriction. -/
def placedNormal  (f : Space m ≃ᵢ Space m) (n : Space m) : Space m :=
  f.toRealAffineIsometryEquiv.linearIsometryEquiv n

theorem normalCosSq_placedNormal  (f : Space m ≃ᵢ Space m)
    (n w : Space m) : normalCosSq (placedNormal f n) (placedNormal f w) =
      normalCosSq n w := normalCosSq_map f.toRealAffineIsometryEquiv.linearIsometryEquiv n w

theorem placed_base_normalCosSq_injective {J : ℕ} (a b : Coefficients S J)
    (u v : Site S) (s t : Side m) (f g : Space m ≃ᵢ Space m)
    (h : normalCosSq (placedNormal f (sideNormal a u s)) (placedNormal f (outward u.1)) =
      normalCosSq (placedNormal g (sideNormal b v t)) (placedNormal g (outward v.1))) :
    |a.value u| = |b.value v| ∧ s = t := by
  rw [normalCosSq_placedNormal, normalCosSq_placedNormal] at h
  exact base_normalCosSq_injective a b u v s t h

theorem placed_base_normalCosSq_ne_side_normalCosSq {J : ℕ} (a b : Coefficients S J)
    (u v : Site S) (s t r : Side m) (htr : t.1 ≠ r.1) (f g : Space m ≃ᵢ Space m) :
    normalCosSq (placedNormal f (sideNormal a u s)) (placedNormal f (outward u.1)) ≠
      normalCosSq (placedNormal g (sideNormal b v t)) (placedNormal g (sideNormal b v r)) := by
  rw [normalCosSq_placedNormal, normalCosSq_placedNormal]
  exact base_normalCosSq_ne_side_normalCosSq a b u v s t r htr


end
end ProductClosure.NativeCompiler
