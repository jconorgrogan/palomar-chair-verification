module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_2_0 : MarkedConfigurationCertificate 2 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_2_1 : MarkedConfigurationCertificate 2 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_2_2 : MarkedConfigurationCertificate 2 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_2_3 : MarkedConfigurationCertificate 2 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_2_4 : MarkedConfigurationCertificate 2 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_2_5 : MarkedConfigurationCertificate 2 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_2 : ∀ r, MarkedConfigurationCertificate 2 r := by
  exact Fin.cases marked_configuration_2_0 (Fin.cases marked_configuration_2_1 (Fin.cases marked_configuration_2_2 (Fin.cases marked_configuration_2_3 (Fin.cases marked_configuration_2_4 (Fin.cases marked_configuration_2_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
