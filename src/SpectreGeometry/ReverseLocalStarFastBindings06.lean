module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_0_96 : RawStarBinding false 96 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_97 : RawStarBinding false 97 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_98 : RawStarBinding false 98 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_99 : RawStarBinding false 99 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_100 : RawStarBinding false 100 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_101 : RawStarBinding false 101 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_102 : RawStarBinding false 102 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_103 : RawStarBinding false 103 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_104 : RawStarBinding false 104 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_105 : RawStarBinding false 105 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_106 : RawStarBinding false 106 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_107 : RawStarBinding false 107 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_108 : RawStarBinding false 108 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_109 : RawStarBinding false 109 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_110 : RawStarBinding false 110 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_111 : RawStarBinding false 111 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_0_6 : ∀ i : Fin 16, RawStarBinding false (96+i.val) := by
  exact Fin.cases raw_star_binding_0_96 (Fin.cases raw_star_binding_0_97 (Fin.cases raw_star_binding_0_98 (Fin.cases raw_star_binding_0_99 (Fin.cases raw_star_binding_0_100 (Fin.cases raw_star_binding_0_101 (Fin.cases raw_star_binding_0_102 (Fin.cases raw_star_binding_0_103 (Fin.cases raw_star_binding_0_104 (Fin.cases raw_star_binding_0_105 (Fin.cases raw_star_binding_0_106 (Fin.cases raw_star_binding_0_107 (Fin.cases raw_star_binding_0_108 (Fin.cases raw_star_binding_0_109 (Fin.cases raw_star_binding_0_110 (Fin.cases raw_star_binding_0_111 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
