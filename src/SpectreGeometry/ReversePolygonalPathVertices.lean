module

public import SpectreGeometry.ReversePolygonalPathEndpoints

@[expose] public section

namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

theorem pathParameter_vertex (ps : List (ℝ × ℝ)) (hn : 2 ≤ ps.length)
    (j : Nat) (hj : j < ps.length) :
    PathParameter ps ((j:ℝ)/(ps.length-1:Nat)) (ps.getD j 0) := by
  by_cases hi : j < ps.length-1
  · refine ⟨j,hi,0,by simp,by simp,?_⟩
    simp
  · have he : j = ps.length-1 := by omega
    have hne : ((ps.length-1:Nat):ℝ) ≠ 0 := by
      exact_mod_cast (show ps.length-1 ≠ 0 by omega)
    rw [he,div_self hne]
    exact pathParameter_one ps hn

end
end SpectreGeometry.ReverseExistence
