module

public import SpectreGeometry.ReversePhysicalClusterChartFacesData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem chart_face_rows_0_7 : ∀ j : Fin 12, ChartFaceRowCheck false (84+j.val) := by
  unfold ChartFaceRowCheck
  decide
end SpectreGeometry.ReversePhysicalClusterCharts
