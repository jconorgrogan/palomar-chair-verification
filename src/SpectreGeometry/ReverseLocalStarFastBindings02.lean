module

public import SpectreGeometry.ReverseLocalStarFastData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem raw_star_binding_0_32 : RawStarBinding false 32 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_33 : RawStarBinding false 33 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_34 : RawStarBinding false 34 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_35 : RawStarBinding false 35 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_36 : RawStarBinding false 36 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_37 : RawStarBinding false 37 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_38 : RawStarBinding false 38 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_39 : RawStarBinding false 39 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_40 : RawStarBinding false 40 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_41 : RawStarBinding false 41 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_42 : RawStarBinding false 42 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_43 : RawStarBinding false 43 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_44 : RawStarBinding false 44 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_45 : RawStarBinding false 45 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_46 : RawStarBinding false 46 := by
  unfold RawStarBinding
  decide
theorem raw_star_binding_0_47 : RawStarBinding false 47 := by
  unfold RawStarBinding
  decide
theorem raw_star_bindings_0_2 : ∀ i : Fin 16, RawStarBinding false (32+i.val) := by
  exact Fin.cases raw_star_binding_0_32 (Fin.cases raw_star_binding_0_33 (Fin.cases raw_star_binding_0_34 (Fin.cases raw_star_binding_0_35 (Fin.cases raw_star_binding_0_36 (Fin.cases raw_star_binding_0_37 (Fin.cases raw_star_binding_0_38 (Fin.cases raw_star_binding_0_39 (Fin.cases raw_star_binding_0_40 (Fin.cases raw_star_binding_0_41 (Fin.cases raw_star_binding_0_42 (Fin.cases raw_star_binding_0_43 (Fin.cases raw_star_binding_0_44 (Fin.cases raw_star_binding_0_45 (Fin.cases raw_star_binding_0_46 (Fin.cases raw_star_binding_0_47 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
