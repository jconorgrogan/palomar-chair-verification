module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_5_0 : MarkedConfigurationCertificate 5 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_5_1 : MarkedConfigurationCertificate 5 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_5_2 : MarkedConfigurationCertificate 5 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_5_3 : MarkedConfigurationCertificate 5 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_5_4 : MarkedConfigurationCertificate 5 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_5_5 : MarkedConfigurationCertificate 5 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_5 : ∀ r, MarkedConfigurationCertificate 5 r := by
  exact Fin.cases marked_configuration_5_0 (Fin.cases marked_configuration_5_1 (Fin.cases marked_configuration_5_2 (Fin.cases marked_configuration_5_3 (Fin.cases marked_configuration_5_4 (Fin.cases marked_configuration_5_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
