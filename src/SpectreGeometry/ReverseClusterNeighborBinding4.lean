module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_4_0 : MarkedConfigurationCertificate 4 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_4_1 : MarkedConfigurationCertificate 4 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_4_2 : MarkedConfigurationCertificate 4 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_4_3 : MarkedConfigurationCertificate 4 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_4_4 : MarkedConfigurationCertificate 4 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_4_5 : MarkedConfigurationCertificate 4 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_4 : ∀ r, MarkedConfigurationCertificate 4 r := by
  exact Fin.cases marked_configuration_4_0 (Fin.cases marked_configuration_4_1 (Fin.cases marked_configuration_4_2 (Fin.cases marked_configuration_4_3 (Fin.cases marked_configuration_4_4 (Fin.cases marked_configuration_4_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
