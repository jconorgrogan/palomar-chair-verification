module

public import SpectreGeometry.ReverseClusterNeighborBindingData

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem marked_configuration_7_0 : MarkedConfigurationCertificate 7 0 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_7_1 : MarkedConfigurationCertificate 7 1 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_7_2 : MarkedConfigurationCertificate 7 2 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_7_3 : MarkedConfigurationCertificate 7 3 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_7_4 : MarkedConfigurationCertificate 7 4 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_7_5 : MarkedConfigurationCertificate 7 5 := by
  unfold MarkedConfigurationCertificate
  decide
theorem marked_configuration_7 : ∀ r, MarkedConfigurationCertificate 7 r := by
  exact Fin.cases marked_configuration_7_0 (Fin.cases marked_configuration_7_1 (Fin.cases marked_configuration_7_2 (Fin.cases marked_configuration_7_3 (Fin.cases marked_configuration_7_4 (Fin.cases marked_configuration_7_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReverseClusterNeighborBinding
