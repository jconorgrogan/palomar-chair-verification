module

public import SpectreGeometry.ReversePolygonalPathParameter

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

theorem PathParameter.affineMap {ps : List (ℝ×ℝ)} {t : ℝ} {y : ℝ×ℝ}
    (h : PathParameter ps t y) (A : (ℝ×ℝ) →ᵃ[ℝ] (ℝ×ℝ)) :
    PathParameter (ps.map A) t (A y) := by
  obtain ⟨j,hj,u,hu,ht,hy⟩ := h
  have hget (i : Nat) (hi : i < ps.length) : (ps.map A).getD i 0 = A (ps.getD i 0) := by
    simp [List.getD_eq_getElem?_getD,hi]
  refine ⟨j,by simpa only [List.length_map] using hj,u,hu,
    by simpa only [List.length_map] using ht,?_⟩
  rw [hget j (by omega),hget (j+1) (by omega),hy,A.apply_lineMap]

end
end SpectreGeometry.ReverseExistence
