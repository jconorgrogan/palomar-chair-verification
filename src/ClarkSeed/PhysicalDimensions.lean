module

public import ClarkSeed.MaterialExistence
public import ClarkSeed.PeriodFree
public import ProductClosure.ProductDimensions

@[expose] public section

/-! The recovered exact CLARK seed plus the proved repeatable physical
product compiler fills dimensions five and eight, hence every dimension
at least five. No planar or four-dimensional seed is assumed. -/
namespace ClarkSeed
noncomputable section
open ProductClosure

/-- Actual compact 5D dense material with nonempty interior, a real tiling,
and universal unmarked aperiodicity under unrestricted isometries. -/
theorem material_physical_monotile :
    (interior compilerData.material).Nonempty ∧
      SparseMonotiles.IsAperiodicMonotile compilerData.material :=
  compilerData.physical_monotile compilerData_hasWorld compilerData_periodFree

/-- Concrete 5D seed eligible for the repeatable product construction. -/
theorem five_certified : CertifiedDimension 5 :=
  ⟨4, compilerData, rfl, compilerData_hasWorld, compilerData_periodFree⟩

theorem eight_certified : CertifiedDimension 8 := three_certified.add five_certified

/-- Three consecutive checked seeds and addition by the actual 3D compiler. -/
theorem every_dimension_ge_five_certified (d : ℕ) (hd : 5 ≤ d) : CertifiedDimension d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hsmall : d < 8
    · interval_cases d <;> first | exact five_certified | exact six_certified | exact seven_certified
    · have hprev : CertifiedDimension (d-3) := ih (d-3) (by omega) (by omega)
      have hsum := three_certified.add hprev
      convert hsum using 1 <;> omega

/-- The exact resulting physical existence theorem in every dimension ≥5. -/
theorem exists_physical_aperiodic_monotile_of_ge_five (d : ℕ) (hd : 5 ≤ d) :
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T :=
  (every_dimension_ge_five_certified d hd).exists_physical_monotile

/-- Together with the already checked 3D seed, this is the full currently
formalized range below and above the CLARK seed. -/
theorem exists_physical_aperiodic_monotile_of_ge_three_ne_four
    (d : ℕ) (hd : 3 ≤ d) (hne : d ≠ 4) :
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T := by
  by_cases h3 : d = 3
  · subst d
    exact three_certified.exists_physical_monotile
  · exact exists_physical_aperiodic_monotile_of_ge_five d (by omega)

#print axioms material_physical_monotile
#print axioms five_certified
#print axioms every_dimension_ge_five_certified
#print axioms exists_physical_aperiodic_monotile_of_ge_five
#print axioms exists_physical_aperiodic_monotile_of_ge_three_ne_four
end
end ClarkSeed
