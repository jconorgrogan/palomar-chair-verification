module

public import SpectreGeometry.ReversePolygonalPathParameter
public import Mathlib.Analysis.Convex.Segment

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

def polygonalPathCarrier (ps : List (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  ⋃ j : Fin (ps.length-1), segment ℝ (ps.getD j.val 0) (ps.getD (j.val+1) 0)

theorem PathParameter.parameter_mem {ps : List (ℝ × ℝ)} {t : ℝ} {y : ℝ × ℝ}
    (h : PathParameter ps t y) : t ∈ Icc (0:ℝ) 1 := by
  obtain ⟨j,hj,u,hu,rfl,_⟩ := h
  have hn : (0:ℝ) < ((ps.length-1:Nat):ℝ) := by exact_mod_cast (show 0 < ps.length-1 by omega)
  have hjR : (j:ℝ)+1 ≤ ((ps.length-1:Nat):ℝ) := by exact_mod_cast hj
  refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg j) hu.1) (le_of_lt hn),(div_le_one hn).2 ?_⟩
  linarith [hu.2]

theorem PathParameter.mem_carrier {ps : List (ℝ × ℝ)} {t : ℝ} {y : ℝ × ℝ}
    (h : PathParameter ps t y) : y ∈ polygonalPathCarrier ps := by
  obtain ⟨j,hj,u,hu,_,rfl⟩ := h
  exact Set.mem_iUnion.mpr ⟨⟨j,hj⟩,lineMap_mem_segment ℝ _ _ hu⟩

theorem mem_polygonalPathCarrier_iff (ps : List (ℝ × ℝ)) (y : ℝ × ℝ) :
    y ∈ polygonalPathCarrier ps ↔ ∃ t ∈ Icc (0:ℝ) 1, PathParameter ps t y := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
    rw [segment_eq_image_lineMap] at hj
    obtain ⟨u,hu,hy⟩ := hj
    have hp : PathParameter ps (((j.val:ℝ)+u)/(ps.length-1:Nat)) y :=
      ⟨j.val,j.isLt,u,hu,rfl,hy.symm⟩
    exact ⟨_,hp.parameter_mem,hp⟩
  · rintro ⟨t,_,h⟩
    exact h.mem_carrier

end
end SpectreGeometry.ReverseExistence
