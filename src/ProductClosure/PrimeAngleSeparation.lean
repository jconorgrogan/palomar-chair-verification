module

public import ProductClosure.NativeCompiler
public import PhysicalRegistration.PrimeAngleSeparation

@[expose] public section
namespace ProductClosure.NativeCompiler
open PhysicalRegistration


/-- Every allowed native slope numerator is strictly between zero and its
literal prime denominator. This estimate in fact holds in every dimension. -/
theorem native_slope_numerator_bounds {m J j i : ℕ} (hj : 0 < j)
    (hjJ : j ≤ J) (hi : i < 2 * m) :
    0 < j * keyPrime J i ∧ j * keyPrime J i < denominator m J := by
  refine ⟨Nat.mul_pos hj (keyPrime_prime J i).pos, ?_⟩
  have hp : keyPrime J i ≤ pMax m J :=
    (keyPrime_strictMono J).monotone (by omega)
  have hfactor : 1 ≤ 32 * (m + 1) := by omega
  calc
    j * keyPrime J i ≤ J * pMax m J := Nat.mul_le_mul hjJ hp
    _ ≤ 32 * (m + 1) * J * pMax m J := by
      have h := Nat.mul_le_mul_right (J * pMax m J) hfactor
      simpa only [one_mul, Nat.mul_assoc] using h
    _ < denominator m J := denominator_gt m J

/-- Native slope products determine both the positive coefficient and the
zero-based prime label. No finite bound on the prime indices is needed. -/
theorem native_slope_numerator_injective {J j k i l : ℕ}
    (hj : 0 < j) (hk : 0 < k) (hjJ : j ≤ J) (hkJ : k ≤ J)
    (h : j * keyPrime J i = k * keyPrime J l) : j = k ∧ i = l := by
  have hprod := bounded_prime_products_injective
    (keyPrime_prime J i) (keyPrime_prime J l) (keyPrime_gt J i) (keyPrime_gt J l)
    hj hk hjJ hkJ h
  exact ⟨hprod.1, (keyPrime_strictMono J).injective hprod.2⟩

/-- The manuscript's mixed-angle obstruction with the actual native primes,
allowed coefficient magnitudes, and exact least-prime denominator. -/
theorem native_prime_angle_equation_impossible {m J j k i l : ℕ}
    (hj : 0 < j) (hk : 0 < k) (hjJ : j ≤ J) (hkJ : k ≤ J)
    (hi : i < 2 * m) (hl : l < 2 * m) (a : ℤ) :
    (denominator m J : ℤ) ^ 2 *
      (a ^ 2 - (j * keyPrime J i : ℕ) ^ 2 - (k * keyPrime J l : ℕ) ^ 2) ≠
      ((j * keyPrime J i : ℕ) : ℤ) ^ 2 * ((k * keyPrime J l : ℕ) : ℤ) ^ 2 := by
  have hb := native_slope_numerator_bounds hj hjJ hi
  have hc := native_slope_numerator_bounds hk hkJ hl
  exact prime_angle_equation_impossible (denominator_prime m J) hb.1 hb.2 hc.1 hc.2 a


end ProductClosure.NativeCompiler
