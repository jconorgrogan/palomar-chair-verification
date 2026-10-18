module

public import ProductClosure.CertifiedDimensions
public import ProductClosure.CompilerProductWorld
public import ProductClosure.ProductCompilerPeriods

@[expose] public section

/-! Repeatable physical product closure and concrete nonvacuous dimensions.
Every constructor obligation is discharged by proved seed or product theorems. -/
namespace ProductClosure
noncomputable section

/-- Both existential world construction and universal period freeness are
preserved by the actual finite product compiler. -/
theorem CertifiedDimension.add {d e : ℕ}
    (hd : CertifiedDimension d) (he : CertifiedDimension e) : CertifiedDimension (d+e) := by
  obtain ⟨a,A,rfl,hWA,hZA⟩ := hd
  obtain ⟨b,B,rfl,hWB,hZB⟩ := he
  exact ⟨a+(b+1), A.prod B, by omega,
    CompilerData.prod_hasWorld A B hWA hWB, CompilerData.prod_periodFree A B hZA hZB⟩

theorem six_certified : CertifiedDimension 6 := three_certified.add three_certified

theorem nine_certified : CertifiedDimension 9 := three_certified.add six_certified

theorem ten_certified : CertifiedDimension 10 := three_certified.add seven_certified

/-- Three consecutive certified dimensions, plus addition by the checked
3D compiler, supply every actual Euclidean dimension at least nine. -/
theorem every_dimension_ge_nine_certified (d : ℕ) (hd : 9 ≤ d) : CertifiedDimension d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hsmall : d < 12
    · interval_cases d <;> first | exact nine_certified | exact ten_certified | exact eleven_certified
    · have hprev : CertifiedDimension (d-3) := ih (d-3) (by omega) (by omega)
      have hsum := three_certified.add hprev
      convert hsum using 1 <;> omega

/-- First genuinely new product endpoint, including actual unrestricted-isometry
tiling existence, unmarked aperiodicity, compactness and nonempty interior. -/
theorem exists_physical_aperiodic_monotile_six :
    ∃ T : Set (EuclideanSpace ℝ (Fin 6)),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T :=
  six_certified.exists_physical_monotile

/-- The repeatable proved product construction yields the complete high-
dimensional range without any planar, CLARK, or curved-key seed assumption. -/
theorem exists_physical_aperiodic_monotile_of_ge_nine (d : ℕ) (hd : 9 ≤ d) :
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T :=
  (every_dimension_ge_nine_certified d hd).exists_physical_monotile

end
end ProductClosure
