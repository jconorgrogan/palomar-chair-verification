module

public import SpectreGeometry.ReverseSourceHexIntersections

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section

def sourceHexCornerAt (c : ℤ × ℤ) (d : Fin 6) : ℝ × ℝ :=
  ((c.1:ℝ)+(sourceHexCorner d).1,(c.2:ℝ)+(sourceHexCorner d).2)

theorem sourceHex_neighbor_intersection_segment (c : ℤ × ℤ) (d : Fin 6) :
    sourceHexCarrier c ∩ sourceHexCarrier (sourceHexNeighbor c d) =
      segment ℝ (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) := by
  ext p
  simp only [Set.mem_inter_iff,sourceHexCarrier,Set.mem_setOf_eq,sourceHexNeighbor,
    Int.cast_add,sub_add_eq_sub_sub]
  rw [sourceHex_neighbor_parametric,segment_eq_image]
  constructor
  · rintro ⟨t,ht0,ht1,hx,hy⟩
    refine ⟨t,⟨ht0,ht1⟩,?_⟩
    apply Prod.ext
    · dsimp [sourceHexCornerAt]
      nlinarith [hx]
    · dsimp [sourceHexCornerAt]
      nlinarith [hy]
  · rintro ⟨t,⟨ht0,ht1⟩,hp⟩
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp [sourceHexCornerAt] at hx hy
    refine ⟨t,ht0,ht1,?_,?_⟩ <;> nlinarith

end
end SpectreGeometry.ReverseExistence
