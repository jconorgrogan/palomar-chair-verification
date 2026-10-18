module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_96 : RawStarBinding true 96 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_97 : RawStarBinding true 97 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_98 : RawStarBinding true 98 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_99 : RawStarBinding true 99 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_100 : RawStarBinding true 100 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_101 : RawStarBinding true 101 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_102 : RawStarBinding true 102 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_103 : RawStarBinding true 103 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_104 : RawStarBinding true 104 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_105 : RawStarBinding true 105 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_106 : RawStarBinding true 106 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_107 : RawStarBinding true 107 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_108 : RawStarBinding true 108 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_109 : RawStarBinding true 109 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_110 : RawStarBinding true 110 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_111 : RawStarBinding true 111 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_6 : ∀ i : Fin 16, RawStarBinding true (96+i.val) := by
  exact Fin.cases raw_star_binding_1_96 (Fin.cases raw_star_binding_1_97 (Fin.cases raw_star_binding_1_98 (Fin.cases raw_star_binding_1_99 (Fin.cases raw_star_binding_1_100 (Fin.cases raw_star_binding_1_101 (Fin.cases raw_star_binding_1_102 (Fin.cases raw_star_binding_1_103 (Fin.cases raw_star_binding_1_104 (Fin.cases raw_star_binding_1_105 (Fin.cases raw_star_binding_1_106 (Fin.cases raw_star_binding_1_107 (Fin.cases raw_star_binding_1_108 (Fin.cases raw_star_binding_1_109 (Fin.cases raw_star_binding_1_110 (Fin.cases raw_star_binding_1_111 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
