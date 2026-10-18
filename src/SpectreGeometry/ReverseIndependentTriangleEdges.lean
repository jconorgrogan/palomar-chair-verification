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

/-- Two nonoverlapping nondegenerate triangles sharing an indexed edge fill a
neighborhood of each relative-open edge point. -/
theorem triangles_shared_edge_interior (v w : Fin 3 → Plane)
    (hv : triangleDet v ≠ 0) (hw : triangleDet w ≠ 0)
    (a b a' b' : Fin 3) (hab : a ≠ b) (hab' : a' ≠ b')
    (ha : v a = w a') (hb : v b = w b')
    (hd : Disjoint (interior (triangleHull v)) (interior (triangleHull w)))
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    AffineMap.lineMap (v a) (v b) t ∈ interior (triangleHull v ∪ triangleHull w) := by
  obtain ⟨c,hac,hbc⟩ := third_index a b hab
  obtain ⟨c',hac',hbc'⟩ := third_index a' b' hab'
  have hi := hull_reorder v a b c hab hac hbc
  have hj := hull_reorder w a' b' c' hab' hac' hbc'
  have hni := side_reorder_ne v hv a b c hab hac hbc
  have hnj := side_reorder_ne w hw a' b' c' hab' hac' hbc'
  rw [←ha,←hb] at hj hnj
  rw [hi,hj] at hd ⊢
  exact ReverseExistence.lineMap_mem_interior_triangle_union _ _ _ _ hni hnj hd t ht

end
end SpectreGeometry.ReverseFinitePL
