module

public import ClarkSeed.WorldProfiles
public import SparseMonotiles.ForwardContactCertificates5

@[expose] public section

/-! Actual complete dense-profile 5D world: the original nested carrier-world
construction and its fully checked finite forward rules discharge existence.
No world, profile, or hierarchy premise remains in these endpoints. -/
namespace ClarkSeed
noncomputable section
open ProductClosure NativeCompiler

/-- The exact recovered constructed world satisfies every newly compiled
native site equation, with all finite forward obligations discharged. -/
theorem seedWorld_fullProfile : CellWorldFullProfile compilerData.coefficients seedWorld :=
  seedWorld_fullProfile_of_forward SparseMonotiles.CarrierHierarchy.t5_forward_rules

/-- Unconditional cell-world existence for the dense 5D compiler input. -/
theorem compilerData_hasWorld : compilerData.HasWorld :=
  ⟨seedWorld, seedWorld_fullProfile⟩

#print axioms seedWorld_fullProfile
#print axioms compilerData_hasWorld
end
end ClarkSeed
