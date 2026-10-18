module

public import SpectreGeometry.ReverseLocalStarGeometryData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem side_geometry_binding_2_0 : SideGeometryBinding 2 0 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_2_1 : SideGeometryBinding 2 1 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_2_2 : SideGeometryBinding 2 2 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_2_3 : SideGeometryBinding 2 3 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_2_4 : SideGeometryBinding 2 4 := by
  unfold SideGeometryBinding
  decide
theorem side_geometry_binding_2_5 : SideGeometryBinding 2 5 := by
  unfold SideGeometryBinding
  decide
end SpectreGeometry.ReverseLocalStarOccurrences
