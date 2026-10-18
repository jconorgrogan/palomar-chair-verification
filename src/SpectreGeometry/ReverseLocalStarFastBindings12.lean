module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_32 : RawStarBinding true 32 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_33 : RawStarBinding true 33 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_34 : RawStarBinding true 34 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_35 : RawStarBinding true 35 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_36 : RawStarBinding true 36 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_37 : RawStarBinding true 37 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_38 : RawStarBinding true 38 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_39 : RawStarBinding true 39 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_40 : RawStarBinding true 40 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_41 : RawStarBinding true 41 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_42 : RawStarBinding true 42 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_43 : RawStarBinding true 43 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_44 : RawStarBinding true 44 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_45 : RawStarBinding true 45 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_46 : RawStarBinding true 46 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_47 : RawStarBinding true 47 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_2 : ∀ i : Fin 16, RawStarBinding true (32+i.val) := by
  exact Fin.cases raw_star_binding_1_32 (Fin.cases raw_star_binding_1_33 (Fin.cases raw_star_binding_1_34 (Fin.cases raw_star_binding_1_35 (Fin.cases raw_star_binding_1_36 (Fin.cases raw_star_binding_1_37 (Fin.cases raw_star_binding_1_38 (Fin.cases raw_star_binding_1_39 (Fin.cases raw_star_binding_1_40 (Fin.cases raw_star_binding_1_41 (Fin.cases raw_star_binding_1_42 (Fin.cases raw_star_binding_1_43 (Fin.cases raw_star_binding_1_44 (Fin.cases raw_star_binding_1_45 (Fin.cases raw_star_binding_1_46 (Fin.cases raw_star_binding_1_47 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
