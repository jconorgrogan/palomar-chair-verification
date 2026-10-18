module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_0_0 : MarkedConfigurationCertificate 0 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_0_1 : MarkedConfigurationCertificate 0 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_0_2 : MarkedConfigurationCertificate 0 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_0_3 : MarkedConfigurationCertificate 0 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_0_4 : MarkedConfigurationCertificate 0 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_0_5 : MarkedConfigurationCertificate 0 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_0 : ∀ r, MarkedConfigurationCertificate 0 r := by
  exact Fin.cases marked_configuration_0_0 (Fin.cases marked_configuration_0_1 (Fin.cases marked_configuration_0_2 (Fin.cases marked_configuration_0_3 (Fin.cases marked_configuration_0_4 (Fin.cases marked_configuration_0_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
