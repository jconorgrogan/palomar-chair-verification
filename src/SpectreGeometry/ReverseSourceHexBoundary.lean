module

public import SpectreGeometry.ReverseSourceHexInteriorDisjoint
public import SpectreGeometry.ReverseMarkedBoundaryParameters
public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set ReverseClusterTriangulation ReverseFinitePL ReverseLocalStarOccurrences

theorem sourceHex_side_line_not_interior (d : Fin 6) (t : ℝ) :
    AffineMap.lineMap (sourceHexCorner d) (sourceHexCorner (d+1)) t ∉
      interior (sourceHexCarrier (0,0)) := by
  intro hp
  have hs := sourceHex_interior_strict (0,0) _ hp
  simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
    Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at hs
  fin_cases d <;> norm_num [sourceHexCorner] at hs <;>
    rcases hs with ⟨h1,h2,h3,h4,h5,h6⟩ <;> linarith

theorem normalized_boundary_vertex_not_interior (k : Fin 9) (d : Fin 6)
    (j : Nat) (hj : j < (boundaryIndices k d).length) :
    (1/(3*(sourceScale k:ℝ))) •
      integerPoint (sourceVertex k ((boundaryIndices k d).getD j 0)) ∉
        interior (sourceHexCarrier (0,0)) := by
  rw [normalized_boundary_vertex k d j hj]
  exact sourceHex_side_line_not_interior d _

theorem boundary_index_not_interior (k : Fin 9) (v : Nat)
    (hv : IsBoundaryIndex k v) :
    (1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k v) ∉
      interior (sourceHexCarrier (0,0)) := by
  obtain ⟨d,hd⟩ := hv
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hd
  have hget : (boundaryIndices k d).getD j 0 = v := by
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using he
  rw [←hget]
  exact normalized_boundary_vertex_not_interior k d j hj

end
end SpectreGeometry.ReverseExistence
