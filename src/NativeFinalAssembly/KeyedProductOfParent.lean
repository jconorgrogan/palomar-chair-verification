module

public import FinalAssemblyDraft.UnmarkedBridge
public import KernelSeedPilot.ProductPhysicalExistence
public import KernelParentPilot.ProductAperiodicityFromParent

@[expose] public section


set_option autoImplicit false

namespace NativeFinalAssembly

/-- Source-only proposal. The exact native keyed body has all geometric and
existence hypotheses discharged; only ParentOccurrence remains explicit. -/
theorem keyed_product_monotile_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) :
    (interior SpectreGeometry.polygonProductKeyBody).Nonempty ∧
    SparseMonotiles.IsAperiodicMonotile SpectreGeometry.polygonProductKeyBody := by
  refine ⟨SpectreGeometry.polygon_product_key_body_interior_nonempty,
    SpectreGeometry.polygon_product_key_body_isCompact, ?_, ?_⟩
  · obtain ⟨I, p, T⟩ := KernelSeedPilot.existing_physical_product_tiling
    exact FinalAssemblyDraft.indexed_tiling_hasTiling
      SpectreGeometry.polygonProductKeyBody p T.covers T.interiors_disjoint
  · refine FinalAssemblyDraft.indexed_period_rigidity_isAperiodic
      SpectreGeometry.polygonProductKeyBody ?_
    intro I p hcover hpack v hperiod
    exact KernelParentPilot.physical_polygon_product_period_eq_zero_of_parent C
      ({ interiors_disjoint := hpack, covers := hcover } :
        SpectreGeometry.PolygonProductPhysicalTiling p) v hperiod

end NativeFinalAssembly
