module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_8_0 : PhysicalBoundaryChartOwnerCertificate 8 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_8_1 : PhysicalBoundaryChartOwnerCertificate 8 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_8_2 : PhysicalBoundaryChartOwnerCertificate 8 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_8_3 : PhysicalBoundaryChartOwnerCertificate 8 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_8_4 : PhysicalBoundaryChartOwnerCertificate 8 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_8_5 : PhysicalBoundaryChartOwnerCertificate 8 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_8 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 8 d := by
  exact Fin.cases physical_boundary_chart_owner_8_0 (Fin.cases physical_boundary_chart_owner_8_1 (Fin.cases physical_boundary_chart_owner_8_2 (Fin.cases physical_boundary_chart_owner_8_3 (Fin.cases physical_boundary_chart_owner_8_4 (Fin.cases physical_boundary_chart_owner_8_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
