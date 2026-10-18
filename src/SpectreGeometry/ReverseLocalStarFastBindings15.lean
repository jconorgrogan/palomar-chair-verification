module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_1_80 : RawStarBinding true 80 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_81 : RawStarBinding true 81 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_82 : RawStarBinding true 82 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_83 : RawStarBinding true 83 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_84 : RawStarBinding true 84 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_85 : RawStarBinding true 85 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_86 : RawStarBinding true 86 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_87 : RawStarBinding true 87 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_88 : RawStarBinding true 88 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_89 : RawStarBinding true 89 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_90 : RawStarBinding true 90 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_91 : RawStarBinding true 91 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_92 : RawStarBinding true 92 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_93 : RawStarBinding true 93 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_94 : RawStarBinding true 94 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_1_95 : RawStarBinding true 95 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_1_5 : ∀ i : Fin 16, RawStarBinding true (80+i.val) := by
  exact Fin.cases raw_star_binding_1_80 (Fin.cases raw_star_binding_1_81 (Fin.cases raw_star_binding_1_82 (Fin.cases raw_star_binding_1_83 (Fin.cases raw_star_binding_1_84 (Fin.cases raw_star_binding_1_85 (Fin.cases raw_star_binding_1_86 (Fin.cases raw_star_binding_1_87 (Fin.cases raw_star_binding_1_88 (Fin.cases raw_star_binding_1_89 (Fin.cases raw_star_binding_1_90 (Fin.cases raw_star_binding_1_91 (Fin.cases raw_star_binding_1_92 (Fin.cases raw_star_binding_1_93 (Fin.cases raw_star_binding_1_94 (Fin.cases raw_star_binding_1_95 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
