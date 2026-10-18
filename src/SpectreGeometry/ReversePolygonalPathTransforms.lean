module

public import SpectreGeometry.ReversePolygonalPathParameter

@[expose] public section

namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

private theorem getD_reverse_in_range (ps : List (ℝ × ℝ)) (i : Nat)
    (hi : i < ps.length) :
    ps.reverse.getD i 0 = ps.getD (ps.length-1-i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

private theorem getD_translate_in_range (ps : List (ℝ × ℝ)) (i : Nat)
    (hi : i < ps.length) (a : ℝ × ℝ) :
    (ps.map (· + a)).getD i 0 = ps.getD i 0 + a := by
  simp [List.getD_eq_getElem?_getD,hi]

theorem PathParameter.reverse {ps : List (ℝ × ℝ)} {t : ℝ} {y : ℝ × ℝ}
    (h : PathParameter ps t y) : PathParameter ps.reverse (1-t) y := by
  obtain ⟨j,hj,u,hu,ht,hy⟩ := h
  let k := ps.length-2-j
  have hk : k < ps.length-1 := by dsimp [k]; omega
  have hj1 : j+1 < ps.length := by omega
  have hk1 : k+1 < ps.length := by omega
  have hkj : ps.length-1-k = j+1 := by dsimp [k]; omega
  have hkj1 : ps.length-1-(k+1) = j := by dsimp [k]; omega
  have hsum : k+j+1 = ps.length-1 := by dsimp [k]; omega
  have hsumR : (k:ℝ)+(j:ℝ)+1 = ((ps.length-1:Nat):ℝ) := by exact_mod_cast hsum
  have hn : ((ps.length-1:Nat):ℝ) ≠ 0 := by exact_mod_cast (show ps.length-1 ≠ 0 by omega)
  refine ⟨k,by simpa using hk,1-u,⟨by linarith [hu.2],by linarith [hu.1]⟩,?_,?_⟩
  · rw [List.length_reverse,ht]
    field_simp
    nlinarith
  · rw [getD_reverse_in_range ps k (by omega),getD_reverse_in_range ps (k+1) hk1,hkj,hkj1,hy]
    simp only [AffineMap.lineMap_apply_module]
    ext <;> simp <;> ring

theorem PathParameter.translate {ps : List (ℝ × ℝ)} {t : ℝ} {y : ℝ × ℝ}
    (h : PathParameter ps t y) (a : ℝ × ℝ) :
    PathParameter (ps.map (· + a)) t (y+a) := by
  obtain ⟨j,hj,u,hu,ht,hy⟩ := h
  refine ⟨j,by simpa using hj,u,hu,by simpa using ht,?_⟩
  rw [getD_translate_in_range ps j (by omega),getD_translate_in_range ps (j+1) (by omega),hy]
  simp only [AffineMap.lineMap_apply_module]
  ext <;> simp <;> ring

end
end SpectreGeometry.ReverseExistence
