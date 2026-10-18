module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_7_0 : PhysicalBoundaryChartOwnerCertificate 7 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_7_1 : PhysicalBoundaryChartOwnerCertificate 7 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_7_2 : PhysicalBoundaryChartOwnerCertificate 7 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_7_3 : PhysicalBoundaryChartOwnerCertificate 7 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_7_4 : PhysicalBoundaryChartOwnerCertificate 7 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_7_5 : PhysicalBoundaryChartOwnerCertificate 7 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_7 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 7 d := by
  exact Fin.cases physical_boundary_chart_owner_7_0 (Fin.cases physical_boundary_chart_owner_7_1 (Fin.cases physical_boundary_chart_owner_7_2 (Fin.cases physical_boundary_chart_owner_7_3 (Fin.cases physical_boundary_chart_owner_7_4 (Fin.cases physical_boundary_chart_owner_7_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
