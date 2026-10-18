module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_16 : RawStarBinding true 16 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_17 : RawStarBinding true 17 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_18 : RawStarBinding true 18 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_19 : RawStarBinding true 19 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_20 : RawStarBinding true 20 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_21 : RawStarBinding true 21 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_22 : RawStarBinding true 22 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_23 : RawStarBinding true 23 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_24 : RawStarBinding true 24 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_25 : RawStarBinding true 25 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_26 : RawStarBinding true 26 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_27 : RawStarBinding true 27 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_28 : RawStarBinding true 28 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_29 : RawStarBinding true 29 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_30 : RawStarBinding true 30 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_31 : RawStarBinding true 31 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_1 : ∀ i : Fin 16, RawStarBinding true (16+i.val) := by
  exact Fin.cases raw_star_binding_1_16 (Fin.cases raw_star_binding_1_17 (Fin.cases raw_star_binding_1_18 (Fin.cases raw_star_binding_1_19 (Fin.cases raw_star_binding_1_20 (Fin.cases raw_star_binding_1_21 (Fin.cases raw_star_binding_1_22 (Fin.cases raw_star_binding_1_23 (Fin.cases raw_star_binding_1_24 (Fin.cases raw_star_binding_1_25 (Fin.cases raw_star_binding_1_26 (Fin.cases raw_star_binding_1_27 (Fin.cases raw_star_binding_1_28 (Fin.cases raw_star_binding_1_29 (Fin.cases raw_star_binding_1_30 (Fin.cases raw_star_binding_1_31 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
