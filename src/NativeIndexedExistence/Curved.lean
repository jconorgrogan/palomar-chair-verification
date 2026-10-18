module

public import FinalAssemblyDraft.UnmarkedBridge
public import KernelCurvedPilot.CurvedGeometryAndTiling

@[expose] public section


set_option autoImplicit false

namespace NativeIndexedExistence
noncomputable section

/-- The accepted exact curved body is compact, has nonempty interior, and
admits an unmarked tiling by unrestricted Euclidean isometries. -/
theorem curved_geometry_and_unmarked_tiling :
    IsCompact LiteralPlanar.FanBounds.curvedBody ∧
    (interior LiteralPlanar.FanBounds.curvedBody).Nonempty ∧
    SparseMonotiles.HasTiling LiteralPlanar.FanBounds.curvedBody := by
  obtain ⟨hc, hi, _hregular, _hfrontier, I, p, _hdirect, hcover, hpack, _hloc⟩ :=
    KernelCurvedPilot.existing_curved_geometry_and_tiling
  exact ⟨hc, hi, FinalAssemblyDraft.indexed_tiling_hasTiling
    LiteralPlanar.FanBounds.curvedBody p hcover hpack⟩

end
end NativeIndexedExistence
