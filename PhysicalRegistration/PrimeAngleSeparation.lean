module

public import PhysicalRegistration.NativeChair

@[expose] public section

/-!
# Exact prime arithmetic for native key-angle separation

The coefficients and prime denominator are the literal choices in `NativeChair`.
This module proves only the arithmetic separation facts. Converting geometric
angle equality to one of these equations is a separate geometric obligation.
-/

namespace PhysicalRegistration

/-- A positive bounded multiplier cannot conceal the identity of a prime above
its bound. Both the multiplier and the prime can be recovered from the product. -/
theorem bounded_prime_products_injective {J j k p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpJ : J < p) (_hqJ : J < q)
    (_hj : 0 < j) (hk : 0 < k) (_hjJ : j ≤ J) (hkJ : k ≤ J)
    (h : j * p = k * q) : j = k ∧ p = q := by
  have hpdiv : p ∣ k * q := by rw [← h]; exact dvd_mul_left p j
  have hpq : p ∣ q := (hp.dvd_mul.mp hpdiv).resolve_left
    (Nat.not_dvd_of_pos_of_lt hk (hkJ.trans_lt hpJ))
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  refine ⟨?_, heq⟩
  exact Nat.eq_of_mul_eq_mul_right hp.pos (by simpa [← heq] using h)

/-- The cross-multiplied squared-angle equation forces the denominator prime
into one of the two slope numerators. The integer `a` is unrestricted. -/
theorem prime_angle_equation_forces_dvd {N b c : ℕ} (hN : Nat.Prime N)
    {a : ℤ}
    (h : (N : ℤ) ^ 2 * (a ^ 2 - (b : ℤ) ^ 2 - (c : ℤ) ^ 2) =
      (b : ℤ) ^ 2 * (c : ℤ) ^ 2) : N ∣ b ∨ N ∣ c := by
  have hdivZ : (N : ℤ) ∣ (b : ℤ) ^ 2 * (c : ℤ) ^ 2 := by
    rw [← h]
    refine ⟨(N : ℤ) * (a ^ 2 - (b : ℤ) ^ 2 - (c : ℤ) ^ 2), ?_⟩
    ring
  have hdiv : N ∣ b ^ 2 * c ^ 2 := by exact_mod_cast hdivZ
  exact (hN.dvd_mul.mp hdiv).imp hN.dvd_of_dvd_pow hN.dvd_of_dvd_pow

/-- For nonzero numerators below the prime denominator, the mixed-angle
integer equation has no solution. -/
theorem prime_angle_equation_impossible {N b c : ℕ} (hN : Nat.Prime N)
    (hb : 0 < b) (hbN : b < N) (hc : 0 < c) (hcN : c < N) (a : ℤ) :
    (N : ℤ) ^ 2 * (a ^ 2 - (b : ℤ) ^ 2 - (c : ℤ) ^ 2) ≠
      (b : ℤ) ^ 2 * (c : ℤ) ^ 2 := by
  intro h
  exact (prime_angle_equation_forces_dvd hN h).elim
    (Nat.not_dvd_of_pos_of_lt hb hbN) (Nat.not_dvd_of_pos_of_lt hc hcN)

namespace NativeChair

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

end NativeChair

#print axioms bounded_prime_products_injective
#print axioms prime_angle_equation_forces_dvd
#print axioms prime_angle_equation_impossible
#print axioms NativeChair.native_slope_numerator_bounds
#print axioms NativeChair.native_slope_numerator_injective
#print axioms NativeChair.native_prime_angle_equation_impossible

end PhysicalRegistration
