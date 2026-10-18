module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_112 : RawStarBinding true 112 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_113 : RawStarBinding true 113 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_114 : RawStarBinding true 114 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_115 : RawStarBinding true 115 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_116 : RawStarBinding true 116 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_117 : RawStarBinding true 117 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_118 : RawStarBinding true 118 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_119 : RawStarBinding true 119 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_120 : RawStarBinding true 120 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_121 : RawStarBinding true 121 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_122 : RawStarBinding true 122 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_123 : RawStarBinding true 123 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_124 : RawStarBinding true 124 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_125 : RawStarBinding true 125 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_126 : RawStarBinding true 126 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_127 : RawStarBinding true 127 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_7 : ∀ i : Fin 16, RawStarBinding true (112+i.val) := by
  exact Fin.cases raw_star_binding_1_112 (Fin.cases raw_star_binding_1_113 (Fin.cases raw_star_binding_1_114 (Fin.cases raw_star_binding_1_115 (Fin.cases raw_star_binding_1_116 (Fin.cases raw_star_binding_1_117 (Fin.cases raw_star_binding_1_118 (Fin.cases raw_star_binding_1_119 (Fin.cases raw_star_binding_1_120 (Fin.cases raw_star_binding_1_121 (Fin.cases raw_star_binding_1_122 (Fin.cases raw_star_binding_1_123 (Fin.cases raw_star_binding_1_124 (Fin.cases raw_star_binding_1_125 (Fin.cases raw_star_binding_1_126 (Fin.cases raw_star_binding_1_127 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
