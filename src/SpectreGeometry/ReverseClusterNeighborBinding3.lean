module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_3_0 : MarkedConfigurationCertificate 3 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_3_1 : MarkedConfigurationCertificate 3 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_3_2 : MarkedConfigurationCertificate 3 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_3_3 : MarkedConfigurationCertificate 3 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_3_4 : MarkedConfigurationCertificate 3 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_3_5 : MarkedConfigurationCertificate 3 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_3 : ∀ r, MarkedConfigurationCertificate 3 r := by
  exact Fin.cases marked_configuration_3_0 (Fin.cases marked_configuration_3_1 (Fin.cases marked_configuration_3_2 (Fin.cases marked_configuration_3_3 (Fin.cases marked_configuration_3_4 (Fin.cases marked_configuration_3_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
