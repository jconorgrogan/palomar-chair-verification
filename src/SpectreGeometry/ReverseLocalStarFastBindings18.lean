module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_128 : RawStarBinding true 128 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_129 : RawStarBinding true 129 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_130 : RawStarBinding true 130 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_131 : RawStarBinding true 131 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_132 : RawStarBinding true 132 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_133 : RawStarBinding true 133 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_134 : RawStarBinding true 134 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_135 : RawStarBinding true 135 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_136 : RawStarBinding true 136 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_137 : RawStarBinding true 137 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_138 : RawStarBinding true 138 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_139 : RawStarBinding true 139 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_140 : RawStarBinding true 140 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_141 : RawStarBinding true 141 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_142 : RawStarBinding true 142 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_143 : RawStarBinding true 143 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_8 : ∀ i : Fin 16, RawStarBinding true (128+i.val) := by
  exact Fin.cases raw_star_binding_1_128 (Fin.cases raw_star_binding_1_129 (Fin.cases raw_star_binding_1_130 (Fin.cases raw_star_binding_1_131 (Fin.cases raw_star_binding_1_132 (Fin.cases raw_star_binding_1_133 (Fin.cases raw_star_binding_1_134 (Fin.cases raw_star_binding_1_135 (Fin.cases raw_star_binding_1_136 (Fin.cases raw_star_binding_1_137 (Fin.cases raw_star_binding_1_138 (Fin.cases raw_star_binding_1_139 (Fin.cases raw_star_binding_1_140 (Fin.cases raw_star_binding_1_141 (Fin.cases raw_star_binding_1_142 (Fin.cases raw_star_binding_1_143 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
