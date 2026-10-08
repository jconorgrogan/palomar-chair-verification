module

public import HENRY.BodyBinding
public import T7FiniteSymmetryConditional
public import T7ExactCompactExistence

@[expose] public section
namespace HENRY.Binding

/-- This adapter is conditional on the internal final proposition. It does not
assume or import an uncompiled final theorem. -/
theorem strongClaim_of_internal
    (h : IsCompact SparseMonotiles.T7 ∧ SparseMonotiles.HasTiling SparseMonotiles.T7 ∧
      SparseMonotiles.IsAperiodic SparseMonotiles.T7 ∧
      ∀ tiles, SparseMonotiles.IsTiling SparseMonotiles.T7 tiles →
        Finite (SparseMonotiles.EuclideanSymmetries tiles) ∧
          Nat.card (SparseMonotiles.EuclideanSymmetries tiles) ≤ 645120) :
    PalomarMonotiles.T7StrongClaim := by
  change (IsCompact PalomarMonotiles.T7 ∧
    SparseMonotiles.HasTiling PalomarMonotiles.T7 ∧
    SparseMonotiles.IsAperiodic PalomarMonotiles.T7) ∧
    ∀ tiles, SparseMonotiles.IsTiling PalomarMonotiles.T7 tiles →
      Finite (SparseMonotiles.EuclideanSymmetries tiles) ∧
        Nat.card (SparseMonotiles.EuclideanSymmetries tiles) ≤ 645120
  rw [T7_eq]
  exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

/-- A genuine physical existence result transported to the independent body. -/
theorem hasTiling : PalomarMonotiles.HasTiling PalomarMonotiles.T7 := by
  change SparseMonotiles.HasTiling PalomarMonotiles.T7
  rw [T7_eq]
  exact SparseMonotiles.ExactCompactExistence7.hasTiling

/-- The remaining full indexed contact classification is an explicit premise.
This checked conditional wrapper is not the final public Solution. -/
theorem strongClaim_of_contact_classification
    (hclassify : ∀ p : SparseMonotiles.Contact.Pose 7,
      SparseMonotiles.Contact.IndexedData7.geometry.LegalContact p →
        p ∈ SparseMonotiles.CarrierHierarchy.M7) :
    PalomarMonotiles.T7StrongClaim := by
  apply strongClaim_of_internal
  exact ⟨SparseMonotiles.T7_isCompact,
    SparseMonotiles.ExactCompactExistence7.hasTiling,
    SparseMonotiles.T7_isAperiodic_of_indexed_contact_classification hclassify,
    SparseMonotiles.T7_finite_full_symmetry_bound_of_contact_classification hclassify⟩

#print axioms strongClaim_of_internal
#print axioms hasTiling
#print axioms strongClaim_of_contact_classification
end HENRY.Binding
