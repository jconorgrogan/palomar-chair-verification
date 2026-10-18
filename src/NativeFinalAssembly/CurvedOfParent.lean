module

public import NativeIndexedExistence.Curved
public import KernelCurvedParentPilot.CurvedPeriodFromParent

@[expose] public section


set_option autoImplicit false

namespace NativeFinalAssembly

/-- Source-only, uncompiled assembly of the exact curved body. The unresolved
ParentOccurrence theorem remains an explicit argument. -/
theorem curved_monotile_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) :
    (interior LiteralPlanar.FanBounds.curvedBody).Nonempty ∧
    SparseMonotiles.IsAperiodicMonotile LiteralPlanar.FanBounds.curvedBody := by
  obtain ⟨hc, hi, ht⟩ :=
    NativeIndexedExistence.curved_geometry_and_unmarked_tiling
  refine ⟨hi, hc, ht, ?_⟩
  refine FinalAssemblyDraft.indexed_period_rigidity_isAperiodic
    LiteralPlanar.FanBounds.curvedBody ?_
  intro I p hcover hpack v hperiod
  exact KernelCurvedParentPilot.curved_period_eq_zero_of_parent
    C p hcover hpack v hperiod

end NativeFinalAssembly
