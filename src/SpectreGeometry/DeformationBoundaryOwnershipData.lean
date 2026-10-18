module

public import SpectreGeometry.DeformationTriangulationData

@[expose] public section


namespace SpectreGeometry.Deformation

theorem boundary_edge_owners : ∀ e : Fin 14, ∃ i : Fin 12, ∃ v : Fin 3,
    triangleIndex i v = e ∧ triangleIndex i (triangleNext v) = next e := by decide

end SpectreGeometry.Deformation
