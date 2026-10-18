module

public import SpectreGeometry.ReversePolygonalPathTransforms

@[expose] public section

namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

theorem PathParameter.reverse_iff {ps : List (ℝ × ℝ)} {t : ℝ} {y : ℝ × ℝ} :
    PathParameter ps.reverse (1-t) y ↔ PathParameter ps t y := by
  constructor
  · intro h
    simpa using h.reverse
  · exact PathParameter.reverse

theorem PathParameter.translate_iff {ps : List (ℝ × ℝ)} {t : ℝ} {y : ℝ × ℝ}
    (a : ℝ × ℝ) :
    PathParameter (ps.map (· + a)) t (y+a) ↔ PathParameter ps t y := by
  constructor
  · intro h
    simpa [List.map_map,Function.comp_def] using h.translate (-a)
  · intro h
    exact h.translate a

theorem pathParameter_zero (ps : List (ℝ × ℝ)) (hn : 2 ≤ ps.length) :
    PathParameter ps 0 (ps.getD 0 0) := by
  refine ⟨0,by omega,0,by simp,?_,?_⟩ <;> simp

theorem pathParameter_one (ps : List (ℝ × ℝ)) (hn : 2 ≤ ps.length) :
    PathParameter ps 1 (ps.getD (ps.length-1) 0) := by
  have hnR : ((ps.length-1:Nat):ℝ) ≠ 0 := by exact_mod_cast (show ps.length-1 ≠ 0 by omega)
  have hi : ps.length-2+1 = ps.length-1 := by omega
  have hiR : ((ps.length-2:Nat):ℝ)+1 = ((ps.length-1:Nat):ℝ) := by exact_mod_cast hi
  refine ⟨ps.length-2,by omega,1,by simp,?_,?_⟩
  · rw [hiR,div_self hnR]
  · simp [hi]

theorem PathParameter.at_zero {ps : List (ℝ × ℝ)} {y : ℝ × ℝ}
    (h : PathParameter ps 0 y) : y = ps.getD 0 0 := by
  have hn : 2 ≤ ps.length := by obtain ⟨j,hj,_⟩ := h; omega
  exact h.unique (pathParameter_zero ps hn)

theorem PathParameter.at_one {ps : List (ℝ × ℝ)} {y : ℝ × ℝ}
    (h : PathParameter ps 1 y) : y = ps.getD (ps.length-1) 0 := by
  have hn : 2 ≤ ps.length := by obtain ⟨j,hj,_⟩ := h; omega
  exact h.unique (pathParameter_one ps hn)
end
end SpectreGeometry.ReverseExistence
