module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_0_80 : RawStarBinding false 80 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_81 : RawStarBinding false 81 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_82 : RawStarBinding false 82 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_83 : RawStarBinding false 83 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_84 : RawStarBinding false 84 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_85 : RawStarBinding false 85 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_86 : RawStarBinding false 86 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_87 : RawStarBinding false 87 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_88 : RawStarBinding false 88 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_89 : RawStarBinding false 89 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_90 : RawStarBinding false 90 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_91 : RawStarBinding false 91 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_92 : RawStarBinding false 92 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_93 : RawStarBinding false 93 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_94 : RawStarBinding false 94 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_95 : RawStarBinding false 95 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_0_5 : ∀ i : Fin 16, RawStarBinding false (80+i.val) := by
  exact Fin.cases raw_star_binding_0_80 (Fin.cases raw_star_binding_0_81 (Fin.cases raw_star_binding_0_82 (Fin.cases raw_star_binding_0_83 (Fin.cases raw_star_binding_0_84 (Fin.cases raw_star_binding_0_85 (Fin.cases raw_star_binding_0_86 (Fin.cases raw_star_binding_0_87 (Fin.cases raw_star_binding_0_88 (Fin.cases raw_star_binding_0_89 (Fin.cases raw_star_binding_0_90 (Fin.cases raw_star_binding_0_91 (Fin.cases raw_star_binding_0_92 (Fin.cases raw_star_binding_0_93 (Fin.cases raw_star_binding_0_94 (Fin.cases raw_star_binding_0_95 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
