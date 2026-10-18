module

public import ClarkSeed.WorldExistence
public import ProductClosure.NativeMonotileCriterion

@[expose] public section

/-! Actual physical existence for the new dense 5D material, independent of
the still separate universal hierarchy/aperiodicity theorem. -/
namespace ClarkSeed
noncomputable section
open ProductClosure NativeCompiler

/-- The newly compiled material is a compact subset of actual Euclidean 5-space. -/
theorem material_isCompact : IsCompact compilerData.material :=
  body_isCompact compilerData.coefficients

/-- A retained occupied-cell ball proves genuine nonempty interior. -/
theorem material_nonemptyInterior : (interior compilerData.material).Nonempty := by
  let c : Polycube.Cell compilerData.cells :=
    ⟨compilerData.nonempty.choose, compilerData.nonempty.choose_spec⟩
  exact ⟨cellCenter c, cellCenter_mem_interior_body compilerData.coefficients c⟩

/-- The original complete registered world and all new profile equations
produce an actual unmarked tiling of the new physical body. -/
theorem material_hasTiling : SparseMonotiles.HasTiling compilerData.material := by
  let : Nonempty (Polycube.Cell compilerData.cells) :=
    ⟨⟨compilerData.nonempty.choose, compilerData.nonempty.choose_spec⟩⟩
  exact body_hasTiling_of_profile_world compilerData.dimension compilerData.coefficients
    seedWorld seedWorld_fullProfile

#print axioms material_isCompact
#print axioms material_nonemptyInterior
#print axioms material_hasTiling
end
end ClarkSeed
