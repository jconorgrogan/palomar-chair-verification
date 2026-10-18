module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_0_64 : RawStarBinding false 64 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_65 : RawStarBinding false 65 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_66 : RawStarBinding false 66 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_67 : RawStarBinding false 67 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_68 : RawStarBinding false 68 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_69 : RawStarBinding false 69 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_70 : RawStarBinding false 70 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_71 : RawStarBinding false 71 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_72 : RawStarBinding false 72 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_73 : RawStarBinding false 73 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_74 : RawStarBinding false 74 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_75 : RawStarBinding false 75 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_76 : RawStarBinding false 76 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_77 : RawStarBinding false 77 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_78 : RawStarBinding false 78 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_79 : RawStarBinding false 79 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_0_4 : ∀ i : Fin 16, RawStarBinding false (64+i.val) := by
  exact Fin.cases raw_star_binding_0_64 (Fin.cases raw_star_binding_0_65 (Fin.cases raw_star_binding_0_66 (Fin.cases raw_star_binding_0_67 (Fin.cases raw_star_binding_0_68 (Fin.cases raw_star_binding_0_69 (Fin.cases raw_star_binding_0_70 (Fin.cases raw_star_binding_0_71 (Fin.cases raw_star_binding_0_72 (Fin.cases raw_star_binding_0_73 (Fin.cases raw_star_binding_0_74 (Fin.cases raw_star_binding_0_75 (Fin.cases raw_star_binding_0_76 (Fin.cases raw_star_binding_0_77 (Fin.cases raw_star_binding_0_78 (Fin.cases raw_star_binding_0_79 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
