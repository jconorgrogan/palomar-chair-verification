module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_1_0 : MarkedConfigurationCertificate 1 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_1_1 : MarkedConfigurationCertificate 1 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_1_2 : MarkedConfigurationCertificate 1 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_1_3 : MarkedConfigurationCertificate 1 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_1_4 : MarkedConfigurationCertificate 1 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_1_5 : MarkedConfigurationCertificate 1 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_1 : ∀ r, MarkedConfigurationCertificate 1 r := by
  exact Fin.cases marked_configuration_1_0 (Fin.cases marked_configuration_1_1 (Fin.cases marked_configuration_1_2 (Fin.cases marked_configuration_1_3 (Fin.cases marked_configuration_1_4 (Fin.cases marked_configuration_1_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
