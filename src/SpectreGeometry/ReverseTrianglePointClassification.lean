module

public import SpectreGeometry.ReverseFinitePLTriangle
public import SpectreGeometry.ReverseTriangleEdgeNeighborhood

@[expose] public section


/-! Vertex, open edge, and ambient interior classification for real plane triangles. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set

private theorem positive_triangle_boundary (a b c x : RealPoint)
    (hD : 0 < side a b c) (hx : x ∈ convexHull ℝ {a,b,c}) :
    x ∈ interior (convexHull ℝ {a,b,c}) ∨
      x ∈ closedSegmentR a b ∨ x ∈ closedSegmentR b c ∨ x ∈ closedSegmentR c a := by
  obtain ⟨h1,h2,h3⟩ := (triangle_mem_iff a b c x hD).1 hx
  rcases h1.eq_or_lt with hz | h1
  · exact Or.inr (Or.inl (triangle_side_zero_segment a b c x hD hx hz.symm))
  rcases h2.eq_or_lt with hz | h2
  · right; right; left
    apply triangle_side_zero_segment b c a x
    · rwa [← side_cyclic a b c]
    · convert hx using 1
      congr 1
      ext y
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    · exact hz.symm
  rcases h3.eq_or_lt with hz | h3
  · right; right; right
    apply triangle_side_zero_segment c a b x
    · rwa [side_cyclic c a b]
    · convert hx using 1
      congr 1
      ext y
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    · exact hz.symm
  exact Or.inl ((triangle_interior_iff a b c x hD).2 ⟨h1,h2,h3⟩)

theorem triangleHull_eq_three_points (v : Fin 3 → Plane) :
    triangleHull v = convexHull ℝ {v 0,v 1,v 2} := by
  unfold triangleHull
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · simp only [mem_insert_iff,mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem triangleDet_eq_side (v : Fin 3 → Plane) :
    triangleDet v = side (v 0) (v 1) (v 2) := by
  simp only [triangleDet,side,RealPoint.det,RealPoint.sub]
  ring

theorem triangle_point_interior_or_closed_edge (v : Fin 3 → Plane)
    (hD : triangleDet v ≠ 0) {x : Plane} (hx : x ∈ triangleHull v) :
    x ∈ interior (triangleHull v) ∨
      ∃ i j : Fin 3, i ≠ j ∧ x ∈ closedSegmentR (v i) (v j) := by
  rw [triangleHull_eq_three_points] at hx ⊢
  rw [triangleDet_eq_side] at hD
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hswap : convexHull ℝ {v 0,v 2,v 1} = convexHull ℝ {v 0,v 1,v 2} := by
      congr 1
      ext y
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    have hpos : 0 < side (v 0) (v 2) (v 1) := by
      have heq : side (v 0) (v 2) (v 1) = -side (v 0) (v 1) (v 2) := by
        simp only [side,RealPoint.det,RealPoint.sub]
        ring
      rw [heq]
      linarith
    have h := positive_triangle_boundary (v 0) (v 2) (v 1) x hpos (hswap.symm ▸ hx)
    rw [hswap] at h
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨0,2,by decide,h⟩
    · exact Or.inr ⟨2,1,by decide,h⟩
    · exact Or.inr ⟨1,0,by decide,h⟩
  · rcases positive_triangle_boundary (v 0) (v 1) (v 2) x hpos hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨0,1,by decide,h⟩
    · exact Or.inr ⟨1,2,by decide,h⟩
    · exact Or.inr ⟨2,0,by decide,h⟩

/-- The three geometric point types of a nondegenerate plane triangle. -/
theorem triangle_point_classification (v : Fin 3 → Plane)
    (hD : triangleDet v ≠ 0) {x : Plane} (hx : x ∈ triangleHull v) :
    (∃ i, x = v i) ∨
      (∃ i j : Fin 3, i ≠ j ∧ ∃ t ∈ Ioo (0 : ℝ) 1,
        x = AffineMap.lineMap (v i) (v j) t) ∨
      x ∈ interior (triangleHull v) := by
  rcases triangle_point_interior_or_closed_edge v hD hx with hi | ⟨i,j,hij,t,ht0,ht1,hxt⟩
  · exact Or.inr (Or.inr hi)
  by_cases h0 : t = 0
  · left
    exact ⟨i,by simpa [h0,interpolate] using hxt⟩
  by_cases h1 : t = 1
  · left
    exact ⟨j,by simpa [h1,interpolate] using hxt⟩
  right; left
  refine ⟨i,j,hij,t,⟨lt_of_le_of_ne ht0 (Ne.symm h0),lt_of_le_of_ne ht1 h1⟩,?_⟩
  rw [hxt]
  apply Prod.ext <;>
    simp only [interpolate,AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
      Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

end
end SpectreGeometry.ReverseFinitePL
