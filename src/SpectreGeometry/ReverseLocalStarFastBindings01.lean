module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_0_16 : RawStarBinding false 16 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_17 : RawStarBinding false 17 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_18 : RawStarBinding false 18 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_19 : RawStarBinding false 19 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_20 : RawStarBinding false 20 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_21 : RawStarBinding false 21 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_22 : RawStarBinding false 22 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_23 : RawStarBinding false 23 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_24 : RawStarBinding false 24 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_25 : RawStarBinding false 25 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_26 : RawStarBinding false 26 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_27 : RawStarBinding false 27 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_28 : RawStarBinding false 28 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_29 : RawStarBinding false 29 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_30 : RawStarBinding false 30 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_31 : RawStarBinding false 31 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_0_1 : ∀ i : Fin 16, RawStarBinding false (16+i.val) := by
  exact Fin.cases raw_star_binding_0_16 (Fin.cases raw_star_binding_0_17 (Fin.cases raw_star_binding_0_18 (Fin.cases raw_star_binding_0_19 (Fin.cases raw_star_binding_0_20 (Fin.cases raw_star_binding_0_21 (Fin.cases raw_star_binding_0_22 (Fin.cases raw_star_binding_0_23 (Fin.cases raw_star_binding_0_24 (Fin.cases raw_star_binding_0_25 (Fin.cases raw_star_binding_0_26 (Fin.cases raw_star_binding_0_27 (Fin.cases raw_star_binding_0_28 (Fin.cases raw_star_binding_0_29 (Fin.cases raw_star_binding_0_30 (Fin.cases raw_star_binding_0_31 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
