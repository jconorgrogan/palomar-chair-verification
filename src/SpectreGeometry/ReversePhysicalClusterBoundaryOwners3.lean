module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_3_0 : PhysicalBoundaryChartOwnerCertificate 3 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_3_1 : PhysicalBoundaryChartOwnerCertificate 3 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_3_2 : PhysicalBoundaryChartOwnerCertificate 3 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_3_3 : PhysicalBoundaryChartOwnerCertificate 3 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_3_4 : PhysicalBoundaryChartOwnerCertificate 3 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_3_5 : PhysicalBoundaryChartOwnerCertificate 3 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_3 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 3 d := by
  exact Fin.cases physical_boundary_chart_owner_3_0 (Fin.cases physical_boundary_chart_owner_3_1 (Fin.cases physical_boundary_chart_owner_3_2 (Fin.cases physical_boundary_chart_owner_3_3 (Fin.cases physical_boundary_chart_owner_3_4 (Fin.cases physical_boundary_chart_owner_3_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
