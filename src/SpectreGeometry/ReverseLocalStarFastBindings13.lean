module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_48 : RawStarBinding true 48 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_49 : RawStarBinding true 49 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_50 : RawStarBinding true 50 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_51 : RawStarBinding true 51 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_52 : RawStarBinding true 52 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_53 : RawStarBinding true 53 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_54 : RawStarBinding true 54 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_55 : RawStarBinding true 55 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_56 : RawStarBinding true 56 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_57 : RawStarBinding true 57 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_58 : RawStarBinding true 58 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_59 : RawStarBinding true 59 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_60 : RawStarBinding true 60 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_61 : RawStarBinding true 61 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_62 : RawStarBinding true 62 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_63 : RawStarBinding true 63 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_3 : ∀ i : Fin 16, RawStarBinding true (48+i.val) := by
  exact Fin.cases raw_star_binding_1_48 (Fin.cases raw_star_binding_1_49 (Fin.cases raw_star_binding_1_50 (Fin.cases raw_star_binding_1_51 (Fin.cases raw_star_binding_1_52 (Fin.cases raw_star_binding_1_53 (Fin.cases raw_star_binding_1_54 (Fin.cases raw_star_binding_1_55 (Fin.cases raw_star_binding_1_56 (Fin.cases raw_star_binding_1_57 (Fin.cases raw_star_binding_1_58 (Fin.cases raw_star_binding_1_59 (Fin.cases raw_star_binding_1_60 (Fin.cases raw_star_binding_1_61 (Fin.cases raw_star_binding_1_62 (Fin.cases raw_star_binding_1_63 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
