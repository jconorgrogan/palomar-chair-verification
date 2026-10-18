module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_0_0 : RawStarBinding false 0 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_1 : RawStarBinding false 1 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_2 : RawStarBinding false 2 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_3 : RawStarBinding false 3 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_4 : RawStarBinding false 4 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_5 : RawStarBinding false 5 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_6 : RawStarBinding false 6 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_7 : RawStarBinding false 7 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_8 : RawStarBinding false 8 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_9 : RawStarBinding false 9 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_10 : RawStarBinding false 10 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_11 : RawStarBinding false 11 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_12 : RawStarBinding false 12 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_13 : RawStarBinding false 13 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_14 : RawStarBinding false 14 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_15 : RawStarBinding false 15 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_0_0 : ∀ i : Fin 16, RawStarBinding false (0+i.val) := by
  exact Fin.cases raw_star_binding_0_0 (Fin.cases raw_star_binding_0_1 (Fin.cases raw_star_binding_0_2 (Fin.cases raw_star_binding_0_3 (Fin.cases raw_star_binding_0_4 (Fin.cases raw_star_binding_0_5 (Fin.cases raw_star_binding_0_6 (Fin.cases raw_star_binding_0_7 (Fin.cases raw_star_binding_0_8 (Fin.cases raw_star_binding_0_9 (Fin.cases raw_star_binding_0_10 (Fin.cases raw_star_binding_0_11 (Fin.cases raw_star_binding_0_12 (Fin.cases raw_star_binding_0_13 (Fin.cases raw_star_binding_0_14 (Fin.cases raw_star_binding_0_15 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
