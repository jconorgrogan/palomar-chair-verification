module

public import SpectreGeometry.ReverseFinitePLMesh
public import SpectreGeometry.ReverseTrianglePointClassification

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set

private theorem third_index (a b : Fin 3) (hab : a ≠ b) :
    ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem hull_reorder (v : Fin 3 → Plane) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triangleHull v = convexHull ℝ {v a,v b,v c} := by
  rw [triangleHull_eq_three_points]
  congr 1
  ext x
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all only [ne_eq,not_true_eq_false,mem_insert_iff,mem_singleton_iff] <;> tauto

private theorem side_reorder_ne (v : Fin 3 → Plane) (h : triangleDet v ≠ 0)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    side (v a) (v b) (v c) ≠ 0 := by
  rw [triangleDet_eq_side] at h
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all only [ne_eq,not_true_eq_false]
  all_goals
    intro hz
    apply h
    simp only [Fin.reduceFinMk,side,RealPoint.det,RealPoint.sub] at hz ⊢
    nlinarith

namespace TriangleMeshPair
/-- The explicit interior-disjointness hypothesis is essential: TriangleMeshPair
allows duplicate triangle indices. A shared nonvertex edge is interior to the
union once genuine nonoverlap is supplied. -/
theorem target_shared_edge_interior {V ι : Type*} (D : TriangleMeshPair V ι)
    (i j : ι) (a b a' b' : Fin 3) (hab : a ≠ b) (hab' : a' ≠ b')
    (ha : D.index i a = D.index j a') (hb : D.index i b = D.index j b')
    (hd : Disjoint (interior (D.closedCharts.target i))
      (interior (D.closedCharts.target j))) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    AffineMap.lineMap (D.targetVertex (D.index i a)) (D.targetVertex (D.index i b)) t ∈
      interior (D.closedCharts.target i ∪ D.closedCharts.target j) := by
  obtain ⟨c,hac,hbc⟩ := third_index a b hab
  obtain ⟨c',hac',hbc'⟩ := third_index a' b' hab'
  have hi := hull_reorder (D.targetVertex ∘ D.index i) a b c hab hac hbc
  have hj := hull_reorder (D.targetVertex ∘ D.index j) a' b' c' hab' hac' hbc'
  have hni := side_reorder_ne (D.targetVertex ∘ D.index i) (D.target_nondegenerate i)
    a b c hab hac hbc
  have hnj := side_reorder_ne (D.targetVertex ∘ D.index j) (D.target_nondegenerate j)
    a' b' c' hab' hac' hbc'
  simp only [Function.comp_apply] at hi hj hni hnj
  rw [←ha,←hb] at hj hnj
  change Disjoint (interior (triangleHull (D.targetVertex ∘ D.index i)))
    (interior (triangleHull (D.targetVertex ∘ D.index j))) at hd
  change _ ∈ interior (triangleHull (D.targetVertex ∘ D.index i) ∪
    triangleHull (D.targetVertex ∘ D.index j))
  rw [hi,hj] at hd ⊢
  exact ReverseExistence.lineMap_mem_interior_triangle_union _ _ _ _ hni hnj hd t ht

end TriangleMeshPair
end
end SpectreGeometry.ReverseFinitePL
