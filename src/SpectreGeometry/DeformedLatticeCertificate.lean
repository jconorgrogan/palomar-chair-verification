module

public import SpectreGeometry.DeformedVertexData

@[expose] public section


/-! Kernel-reduced lattice certificate for all rotated, reversed unit-edge
matches whose two physical endpoint stars have allowable corner sums. -/
namespace SpectreGeometry

theorem deformed_anchor_shift_lattice : ∀ (r : Fin 12) (e j : Fin 14),
    AllowedReversedEdgePair e j →
    InKiteCenterLattice (deformedAnchorShift r (opposedFrame r e j) e j) := by decide

end SpectreGeometry
