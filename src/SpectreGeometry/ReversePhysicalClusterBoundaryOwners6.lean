module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_6_0 : PhysicalBoundaryChartOwnerCertificate 6 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_6_1 : PhysicalBoundaryChartOwnerCertificate 6 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_6_2 : PhysicalBoundaryChartOwnerCertificate 6 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_6_3 : PhysicalBoundaryChartOwnerCertificate 6 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_6_4 : PhysicalBoundaryChartOwnerCertificate 6 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_6_5 : PhysicalBoundaryChartOwnerCertificate 6 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_6 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 6 d := by
  exact Fin.cases physical_boundary_chart_owner_6_0 (Fin.cases physical_boundary_chart_owner_6_1 (Fin.cases physical_boundary_chart_owner_6_2 (Fin.cases physical_boundary_chart_owner_6_3 (Fin.cases physical_boundary_chart_owner_6_4 (Fin.cases physical_boundary_chart_owner_6_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
