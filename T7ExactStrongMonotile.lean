module
public import T7ExactCompactExistence
public import ReplayPhysicalClassification
public import T7FiniteSymmetryConditional
@[expose] public section
namespace SparseMonotiles.ExactCompactT7Strong
open Contact CarrierHierarchy

/-- Prepared final target. This module must not be described as checked until
both the full acceptance/existence and full contact-classification jobs pass. -/
theorem final_bound :
    IsCompact T7 ∧ HasTiling T7 ∧ IsAperiodic T7 ∧
      ∀ tiles, IsTiling T7 tiles →
        Finite (EuclideanSymmetries tiles) ∧ Nat.card (EuclideanSymmetries tiles) ≤ 645120 :=
  ⟨T7_isCompact, ExactCompactExistence7.hasTiling, FullContactReplay.T7_isAperiodic,
    T7_finite_full_symmetry_bound_of_contact_classification
      (fun _ legal => FullContactReplay.all_legal_contact_mem_M7 legal)⟩

#print axioms final_bound
#print final_bound
end SparseMonotiles.ExactCompactT7Strong
