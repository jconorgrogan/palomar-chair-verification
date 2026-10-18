module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_6_0 : MarkedConfigurationCertificate 6 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_6_1 : MarkedConfigurationCertificate 6 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_6_2 : MarkedConfigurationCertificate 6 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_6_3 : MarkedConfigurationCertificate 6 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_6_4 : MarkedConfigurationCertificate 6 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_6_5 : MarkedConfigurationCertificate 6 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_6 : ∀ r, MarkedConfigurationCertificate 6 r := by
  exact Fin.cases marked_configuration_6_0 (Fin.cases marked_configuration_6_1 (Fin.cases marked_configuration_6_2 (Fin.cases marked_configuration_6_3 (Fin.cases marked_configuration_6_4 (Fin.cases marked_configuration_6_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
