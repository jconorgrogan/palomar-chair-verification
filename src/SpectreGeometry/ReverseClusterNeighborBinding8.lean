module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_8_0 : MarkedConfigurationCertificate 8 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_8_1 : MarkedConfigurationCertificate 8 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_8_2 : MarkedConfigurationCertificate 8 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_8_3 : MarkedConfigurationCertificate 8 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_8_4 : MarkedConfigurationCertificate 8 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_8_5 : MarkedConfigurationCertificate 8 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_8 : ∀ r, MarkedConfigurationCertificate 8 r := by
  exact Fin.cases marked_configuration_8_0 (Fin.cases marked_configuration_8_1 (Fin.cases marked_configuration_8_2 (Fin.cases marked_configuration_8_3 (Fin.cases marked_configuration_8_4 (Fin.cases marked_configuration_8_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
