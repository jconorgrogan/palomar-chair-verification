module

public import SparseMonotiles.FiniteSymmetry
public import SparseMonotiles.CompactKeys5
public import SparseMonotiles.StrongSymmetryStatement

@[expose] public section
namespace PalomarMonotiles

/-- Proof adapter only; it neither imports Challenge nor assumes registration. -/
theorem T5_strongAperiodicity : T5StrongClaim := by
  refine ⟨SparseMonotiles.CompactBinding.Keys5.claim_iff.mpr
    SparseMonotiles.T5_isAperiodicMonotile, ?_⟩
  intro tiles ht
  have ht' : SparseMonotiles.IsTiling SparseMonotiles.T5 tiles := by
    change SparseMonotiles.IsTiling T5 tiles at ht
    simpa only [SparseMonotiles.CompactBinding.Keys5.body_eq] using ht
  change Finite (SparseMonotiles.EuclideanSymmetries tiles) ∧
    Nat.card (SparseMonotiles.EuclideanSymmetries tiles) ≤ 3840
  exact ⟨SparseMonotiles.T5_finite_euclidean_symmetries ht',
    SparseMonotiles.T5_euclidean_symmetry_card_le_3840 ht'⟩

end PalomarMonotiles
