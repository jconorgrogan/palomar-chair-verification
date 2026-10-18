module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_64 : RawStarBinding true 64 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_65 : RawStarBinding true 65 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_66 : RawStarBinding true 66 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_67 : RawStarBinding true 67 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_68 : RawStarBinding true 68 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_69 : RawStarBinding true 69 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_70 : RawStarBinding true 70 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_71 : RawStarBinding true 71 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_72 : RawStarBinding true 72 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_73 : RawStarBinding true 73 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_74 : RawStarBinding true 74 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_75 : RawStarBinding true 75 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_76 : RawStarBinding true 76 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_77 : RawStarBinding true 77 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_78 : RawStarBinding true 78 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_79 : RawStarBinding true 79 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_4 : ∀ i : Fin 16, RawStarBinding true (64+i.val) := by
  exact Fin.cases raw_star_binding_1_64 (Fin.cases raw_star_binding_1_65 (Fin.cases raw_star_binding_1_66 (Fin.cases raw_star_binding_1_67 (Fin.cases raw_star_binding_1_68 (Fin.cases raw_star_binding_1_69 (Fin.cases raw_star_binding_1_70 (Fin.cases raw_star_binding_1_71 (Fin.cases raw_star_binding_1_72 (Fin.cases raw_star_binding_1_73 (Fin.cases raw_star_binding_1_74 (Fin.cases raw_star_binding_1_75 (Fin.cases raw_star_binding_1_76 (Fin.cases raw_star_binding_1_77 (Fin.cases raw_star_binding_1_78 (Fin.cases raw_star_binding_1_79 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
