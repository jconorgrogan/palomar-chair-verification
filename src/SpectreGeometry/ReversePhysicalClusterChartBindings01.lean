module

public import SpectreGeometry.ReversePhysicalClusterChartFacesData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem chart_packet_bindings_0_1 : ∀ j : Fin 12, ChartPacketBinding false (12+j.val) := by
  unfold ChartPacketBinding
  decide
end SpectreGeometry.ReversePhysicalClusterCharts
