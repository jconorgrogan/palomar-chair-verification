module

public import ClarkSeed.CatalogClosure
public import SparseMonotiles.CoarseContactCertificates5

@[expose] public section

/-! Exact universal period theorem for the new dense 5D compiler, derived
from the fully checked recovered CLARK hierarchy and literal world decoding. -/
namespace ClarkSeed
noncomputable section
open ProductClosure NativeCompiler SparseMonotiles
open PoseAdapter

/-- All dense legal complete worlds have only the zero full-state period.
The full signed pose and the same integer translation vector are preserved. -/
theorem compilerData_periodFree : compilerData.PeriodFree := by
  intro W hW v hv
  exact CarrierHierarchy.t5_registered_period_zero (fromWorld W)
    (denseWorld_exact_catalog W hW) v ((fromWorld_period_iff W v).mpr hv)

#print axioms compilerData_periodFree
end
end ClarkSeed
