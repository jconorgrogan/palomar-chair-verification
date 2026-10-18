module

public import SpectreGeometry.ReverseBoundedDistanceProper
public import Mathlib.Topology.Covering.Basic

@[expose] public section


/-! Proper local homeomorphisms are covering maps. Finite fibers are derived,
not assumed. This is a generic topological assembly component. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

/-- Properness gives compact fibers, and local homeomorphism makes them discrete. -/
theorem finite_fiber_of_proper_local_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F : X → Y} (hP : IsProperMap F) (hL : IsLocalHomeomorph F) (y : Y) :
    (F ⁻¹' {y}).Finite := by
  apply (hP.isCompact_preimage isCompact_singleton).finite
  apply IsDiscrete.of_openPartialHomeomorph F subset_rfl
  intro x hx
  obtain ⟨e,he,heq⟩ := hL x
  exact ⟨e,he,heq.symm⟩

/-- A proper local homeomorphism with Hausdorff domain is a covering map. -/
theorem isCoveringMap_of_proper_local_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {F : X → Y} (hP : IsProperMap F) (hL : IsLocalHomeomorph F) : IsCoveringMap F := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  exact hP.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun y _ => finite_fiber_of_proper_local_homeomorph hP hL y) hL.isLocalHomeomorphOn

end
end SpectreGeometry.ReverseExistence
