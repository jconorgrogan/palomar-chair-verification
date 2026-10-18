module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_0 : RawStarBinding true 0 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_1 : RawStarBinding true 1 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_2 : RawStarBinding true 2 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_3 : RawStarBinding true 3 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_4 : RawStarBinding true 4 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_5 : RawStarBinding true 5 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_6 : RawStarBinding true 6 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_7 : RawStarBinding true 7 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_8 : RawStarBinding true 8 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_9 : RawStarBinding true 9 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_10 : RawStarBinding true 10 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_11 : RawStarBinding true 11 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_12 : RawStarBinding true 12 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_13 : RawStarBinding true 13 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_14 : RawStarBinding true 14 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_15 : RawStarBinding true 15 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_0 : ∀ i : Fin 16, RawStarBinding true (0+i.val) := by
  exact Fin.cases raw_star_binding_1_0 (Fin.cases raw_star_binding_1_1 (Fin.cases raw_star_binding_1_2 (Fin.cases raw_star_binding_1_3 (Fin.cases raw_star_binding_1_4 (Fin.cases raw_star_binding_1_5 (Fin.cases raw_star_binding_1_6 (Fin.cases raw_star_binding_1_7 (Fin.cases raw_star_binding_1_8 (Fin.cases raw_star_binding_1_9 (Fin.cases raw_star_binding_1_10 (Fin.cases raw_star_binding_1_11 (Fin.cases raw_star_binding_1_12 (Fin.cases raw_star_binding_1_13 (Fin.cases raw_star_binding_1_14 (Fin.cases raw_star_binding_1_15 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
