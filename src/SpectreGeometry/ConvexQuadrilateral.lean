module

public import SpectreGeometry.TriangulationFlip

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem side_nonneg_four_hull (a b p q r s x : RealPoint)
    (hp : 0 ≤ side a b p) (hq : 0 ≤ side a b q)
    (hr : 0 ≤ side a b r) (hs : 0 ≤ side a b s)
    (hx : x ∈ convexHull ℝ {p,q,r,s}) : 0 ≤ side a b x := by
  exact side_nonneg_hull a b {p,q,r,s}
    (by intro y hy; simp only [mem_insert_iff,mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> assumption) x hx

theorem convex_quad_hull_mem_iff (a b c d x : RealPoint)
    (habc : 0 < side a b c) (hacd : 0 < side a c d)
    (habd : 0 < side a b d) (hbcd : 0 < side b c d) :
    x ∈ convexHull ℝ {a,b,c,d} ↔
      0 ≤ side a b x ∧ 0 ≤ side b c x ∧ 0 ≤ side c d x ∧ 0 ≤ side d a x := by
  have hcda : 0 < side c d a := by rwa [←side_cyclic]
  have hcdb : 0 < side c d b := by rwa [←side_cyclic]
  have hdab : 0 < side d a b := by rw [side_cyclic]; exact habd
  have hdac : 0 < side d a c := by rw [side_cyclic]; exact hacd
  have hbca : 0 < side b c a := by rwa [←side_cyclic]
  constructor
  · intro hx
    exact ⟨side_nonneg_four_hull a b a b c d x (by simp) (by simp) habc.le habd.le hx,
      side_nonneg_four_hull b c a b c d x hbca.le (by simp) (by simp) hbcd.le hx,
      side_nonneg_four_hull c d a b c d x hcda.le hcdb.le (by simp) (by simp) hx,
      side_nonneg_four_hull d a a b c d x (by simp) hdab.le hdac.le (by simp) hx⟩
  · intro hx
    have ht := (convex_quad_first_diagonal a b c d x habc hacd habd hbcd).2 hx
    rcases ht with ht | ht
    · exact convexHull_mono (by intro y hy; simp only [mem_insert_iff,mem_singleton_iff] at *; tauto) ht
    · exact convexHull_mono (by intro y hy; simp only [mem_insert_iff,mem_singleton_iff] at *; tauto) ht

end
end SpectreGeometry
