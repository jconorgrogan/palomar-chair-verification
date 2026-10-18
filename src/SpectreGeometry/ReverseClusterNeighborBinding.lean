module

public import SpectreGeometry.ReverseClusterNeighborBinding0
public import SpectreGeometry.ReverseClusterNeighborBinding1
public import SpectreGeometry.ReverseClusterNeighborBinding2
public import SpectreGeometry.ReverseClusterNeighborBinding3
public import SpectreGeometry.ReverseClusterNeighborBinding4
public import SpectreGeometry.ReverseClusterNeighborBinding5
public import SpectreGeometry.ReverseClusterNeighborBinding6
public import SpectreGeometry.ReverseClusterNeighborBinding7
public import SpectreGeometry.ReverseClusterNeighborBinding8

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
theorem all_marked_configuration_certificates : ∀ k r, MarkedConfigurationCertificate k r := by
  exact Fin.cases marked_configuration_0 (Fin.cases marked_configuration_1 (Fin.cases marked_configuration_2 (Fin.cases marked_configuration_3 (Fin.cases marked_configuration_4 (Fin.cases marked_configuration_5 (Fin.cases marked_configuration_6 (Fin.cases marked_configuration_7 (Fin.cases marked_configuration_8 (fun i => Fin.elim0 i)))))))))
end SpectreGeometry.ReverseClusterNeighborBinding
