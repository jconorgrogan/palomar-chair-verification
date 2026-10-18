module

public import SpectreGeometry.TriangleGeometry

@[expose] public section


/-! Elementary diagonal flips of a strictly convex quadrilateral, expressed
entirely by the four positive oriented triangle determinants. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem side_nonneg_triangle (a b c d e x : RealPoint)
    (hc : 0 ≤ side a b c) (hd : 0 ≤ side a b d) (he : 0 ≤ side a b e)
    (hx : x ∈ convexHull ℝ {c,d,e}) : 0 ≤ side a b x := by
  exact side_nonneg_hull a b {c,d,e}
    (by intro y hy; simp only [mem_insert_iff,mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl <;> assumption) x hx

theorem convex_quad_first_diagonal (a b c d x : RealPoint)
    (habc : 0 < side a b c) (hacd : 0 < side a c d)
    (habd : 0 < side a b d) (hbcd : 0 < side b c d) :
    x ∈ convexHull ℝ {a,b,c} ∪ convexHull ℝ {a,c,d} ↔
      0 ≤ side a b x ∧ 0 ≤ side b c x ∧ 0 ≤ side c d x ∧ 0 ≤ side d a x := by
  have hcda : 0 < side c d a := by rwa [←side_cyclic]
  have hcdb : 0 < side c d b := by rwa [←side_cyclic]
  have hdab : 0 < side d a b := by rw [side_cyclic]; exact habd
  have hdac : 0 < side d a c := by rw [side_cyclic]; exact hacd
  have hbca : 0 < side b c a := by rwa [←side_cyclic]
  constructor
  · rintro (hx | hx)
    · obtain ⟨h1,h2,h3⟩ := (triangle_mem_iff a b c x habc).1 hx
      exact ⟨h1,h2,side_nonneg_triangle c d a b c x hcda.le hcdb.le (by simp) hx,
        side_nonneg_triangle d a a b c x (by simp) hdab.le hdac.le hx⟩
    · obtain ⟨h1,h2,h3⟩ := (triangle_mem_iff a c d x hacd).1 hx
      exact ⟨side_nonneg_triangle a b a c d x (by simp) habc.le habd.le hx,
        side_nonneg_triangle b c a c d x hbca.le (by simp) hbcd.le hx,h2,h3⟩
  · rintro ⟨h1,h2,h3,h4⟩
    by_cases hdiag : 0 ≤ side a c x
    · exact Or.inr ((triangle_mem_iff a c d x hacd).2 ⟨hdiag,h3,h4⟩)
    · exact Or.inl ((triangle_mem_iff a b c x habc).2
        ⟨h1,h2,by rw [side_reverse]; exact (neg_nonneg).2 (le_of_not_ge hdiag)⟩)

theorem convex_quad_diagonal_flip (a b c d : RealPoint)
    (habc : 0 < side a b c) (hacd : 0 < side a c d)
    (habd : 0 < side a b d) (hbcd : 0 < side b c d) :
    convexHull ℝ {a,b,c} ∪ convexHull ℝ {a,c,d} =
      convexHull ℝ {a,b,d} ∪ convexHull ℝ {b,c,d} := by
  ext x
  rw [convex_quad_first_diagonal a b c d x habc hacd habd hbcd]
  have hbda : 0 < side b d a := by rwa [←side_cyclic]
  have hbca : 0 < side b c a := by rwa [←side_cyclic]
  have hcda : 0 < side c d a := by rwa [←side_cyclic]
  have h := convex_quad_first_diagonal b c d a x hbcd hbda hbca hcda
  have hs : ({b,d,a} : Set RealPoint) = {a,b,d} := by ext y; simp; tauto
  rw [hs,union_comm] at h
  rw [h]
  tauto

end
end SpectreGeometry
