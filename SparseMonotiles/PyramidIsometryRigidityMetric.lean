module

public import SparseMonotiles.PyramidIsometryRigidity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Exact integer certificates for intrinsic Euclidean metric fingerprints

No approximate distance computation enters these proofs: a common integer
scale clears every denominator, and squared Euclidean distances become finite
integer sums. The finite certificate is useful only after the extreme-point
and affine-spanning obligations have been established geometrically.
-/
namespace SparseMonotiles

/-- A finite integer vertex array embedded at a common positive or negative scale. -/
noncomputable def scaledIntegerVertex {ι : Type*} {d : ℕ}
    (v : ι → Fin d → ℤ) (den : ℤ) (i : ι) : Point d :=
  rationalPoint (fun k => (v i k : ℚ) / (den : ℚ))

/-- Exact denominator-cleared squared-distance row sum. -/
def integerDistanceFingerprint {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (i : ι) : ℤ :=
  ∑ j, ∑ k, (v i k - v j k) ^ 2

/-- Exact conversion of Euclidean squared distances to integer arithmetic. -/
theorem scaledIntegerVertex_dist_sq {ι : Type*} {d : ℕ}
    (v : ι → Fin d → ℤ) (den : ℤ) (i j : ι) :
    dist (scaledIntegerVertex v den i) (scaledIntegerVertex v den j) ^ 2 =
      ((∑ k, (v i k - v j k) ^ 2 : ℤ) : ℝ) / (den : ℝ) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Real.dist_eq, sq_abs, scaledIntegerVertex, rationalPoint,
    Equiv.symm_apply_apply, Rat.cast_div, Rat.cast_intCast,
    Int.cast_sum, Int.cast_pow, Int.cast_sub, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  change ((v i k : ℝ) / (den : ℝ) - (v j k : ℝ) / (den : ℝ)) ^ 2 = _
  rw [← sub_div, div_pow]

/-- Injective integer fingerprints already imply that the vertex array has no duplicates. -/
theorem integerVertex_injective_of_fingerprint {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (hf : Function.Injective (integerDistanceFingerprint v)) :
    Function.Injective v := by
  intro i j hij
  apply hf
  unfold integerDistanceFingerprint
  rw [hij]

/-- Nonzero common scaling preserves injectivity of the integer vertex array. -/
theorem scaledIntegerVertex_injective {ι : Type*} {d : ℕ}
    (v : ι → Fin d → ℤ) {den : ℤ} (hd : den ≠ 0) (hv : Function.Injective v) :
    Function.Injective (scaledIntegerVertex v den) := by
  intro i j hij
  apply hv
  funext k
  have heq := congrArg (fun x : Point d => x k) hij
  change (((v i k : ℚ) / (den : ℚ) : ℚ) : ℝ) =
    (((v j k : ℚ) / (den : ℚ) : ℚ) : ℝ) at heq
  have hden : (den : ℚ) ≠ 0 := by exact_mod_cast hd
  have hq : (v i k : ℚ) / (den : ℚ) = (v j k : ℚ) / (den : ℚ) :=
    Rat.cast_injective heq
  have : (v i k : ℚ) = (v j k : ℚ) := (div_left_inj' hden).mp hq
  exact_mod_cast this

/-- The actual Euclidean vertex set used by the finite certificate. -/
noncomputable def scaledIntegerVertexFinset {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (den : ℤ) : Finset (Point d) := by
  classical
  exact Finset.univ.image (scaledIntegerVertex v den)

/-- Exact binding of a finite Euclidean fingerprint to its integer certificate. -/
theorem scaledIntegerVertex_fingerprint {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) {den : ℤ} (hd : den ≠ 0) (hv : Function.Injective v)
    (i : ι) :
    squaredDistanceFingerprint (scaledIntegerVertexFinset v den)
        (scaledIntegerVertex v den i) =
      (integerDistanceFingerprint v i : ℝ) / (den : ℝ) ^ 2 := by
  classical
  unfold squaredDistanceFingerprint scaledIntegerVertexFinset
  rw [Finset.sum_image]
  · simp only [scaledIntegerVertex_dist_sq, integerDistanceFingerprint,
      Int.cast_sum, Finset.sum_div]
  · intro i _ j _ hij
    exact scaledIntegerVertex_injective v hd hv hij

/-- A kernel-checkable integer fingerprint certificate implies intrinsic
fingerprint separation for the actual Euclidean points. -/
theorem scaledIntegerVertex_fingerprint_injOn {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) {den : ℤ} (hd : den ≠ 0)
    (hf : Function.Injective (integerDistanceFingerprint v)) :
    Set.InjOn (squaredDistanceFingerprint (scaledIntegerVertexFinset v den))
      (scaledIntegerVertexFinset v den : Set (Point d)) := by
  classical
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨j, _, rfl⟩
  have hv := integerVertex_injective_of_fingerprint v hf
  rw [scaledIntegerVertex_fingerprint v hd hv,
    scaledIntegerVertex_fingerprint v hd hv] at hxy
  have hden : (den : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd)
  have hi : integerDistanceFingerprint v i = integerDistanceFingerprint v j := by
    exact_mod_cast (div_left_inj' hden).mp hxy
  rw [hf hi]

/-- Full arbitrary-isometry rigidity from an exact integer vertex certificate. -/
theorem isometryEquiv_eq_refl_of_integerFingerprint {ι : Type*} [Fintype ι] {d : ℕ}
    (K : Set (Point d)) (v : ι → Fin d → ℤ) {den : ℤ} (hd : den ≠ 0)
    (hext : K.extremePoints ℝ = (scaledIntegerVertexFinset v den : Set (Point d)))
    (hspan : affineSpan ℝ (scaledIntegerVertexFinset v den : Set (Point d)) = ⊤)
    (hf : Function.Injective (integerDistanceFingerprint v))
    (g : Point d ≃ᵢ Point d) (hg : g '' K = K) :
    g = IsometryEquiv.refl (Point d) :=
  isometryEquiv_eq_refl_of_extremePoints_fingerprint K _ hext hspan
    (scaledIntegerVertex_fingerprint_injOn v hd hf) g hg

#print axioms scaledIntegerVertex_dist_sq
#print axioms scaledIntegerVertex_fingerprint
#print axioms isometryEquiv_eq_refl_of_integerFingerprint

end SparseMonotiles
