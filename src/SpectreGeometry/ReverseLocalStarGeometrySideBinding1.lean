module

public import SpectreGeometry.ReverseLocalStarGeometryData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem side_geometry_binding_1_0 : SideGeometryBinding 1 0 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_1_1 : SideGeometryBinding 1 1 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_1_2 : SideGeometryBinding 1 2 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_1_3 : SideGeometryBinding 1 3 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_1_4 : SideGeometryBinding 1 4 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_1_5 : SideGeometryBinding 1 5 := by
  unfold SideGeometryBinding
  decide
end SpectreGeometry.ReverseLocalStarOccurrences
