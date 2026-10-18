module

public import SpectreGeometry.TriangulationFlip

@[expose] public section


/-! Collapse a three-triangle radial fan whose center lies strictly inside
the outer triangle. The proof uses an exact weighted radial identity. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem three_radial_cones (a b c p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : p*a+q*b+r*c=0) :
    (0 ≤ a ∧ b ≤ 0) ∨ (0 ≤ b ∧ c ≤ 0) ∨ (0 ≤ c ∧ a ≤ 0) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : b ≤ 0
    · exact Or.inl ⟨ha,hb⟩
    · by_cases hc : c ≤ 0
      · exact Or.inr (Or.inl ⟨(lt_of_not_ge hb).le,hc⟩)
      · have hpa := mul_nonneg hp.le ha
        have hqb := mul_pos hq (lt_of_not_ge hb)
        have hrc := mul_pos hr (lt_of_not_ge hc)
        linarith
  · by_cases hc : 0 ≤ c
    · exact Or.inr (Or.inr ⟨hc,le_of_not_ge ha⟩)
    · by_cases hb : 0 ≤ b
      · exact Or.inr (Or.inl ⟨hb,le_of_not_ge hc⟩)
      · have hpa := mul_neg_of_pos_of_neg hp (lt_of_not_ge ha)
        have hqb := mul_neg_of_pos_of_neg hq (lt_of_not_ge hb)
        have hrc := mul_neg_of_pos_of_neg hr (lt_of_not_ge hc)
        linarith

theorem triangle_center_fan (o a b c : RealPoint)
    (hab : 0 < side a b o) (hbc : 0 < side b c o) (hca : 0 < side c a o) :
    convexHull ℝ {o,a,b} ∪ convexHull ℝ {o,b,c} ∪ convexHull ℝ {o,c,a} =
      convexHull ℝ {a,b,c} := by
  have hsum : side a b c = side a b o+side b c o+side c a o := by
    simp only [side,RealPoint.det,RealPoint.sub]; ring
  have hD : 0 < side a b c := by linarith
  have ho : o ∈ convexHull ℝ {a,b,c} := (triangle_mem_iff a b c o hD).2 ⟨hab.le,hbc.le,hca.le⟩
  have hOb : 0 < side o a b := by rw [side_cyclic]; exact hab
  have hOc : 0 < side o b c := by rw [side_cyclic]; exact hbc
  have hOa : 0 < side o c a := by rw [side_cyclic]; exact hca
  ext x
  constructor
  · intro hx
    have hs (u v : RealPoint) (hu : u ∈ ({a,b,c} : Set RealPoint))
        (hv : v ∈ ({a,b,c} : Set RealPoint)) :
        convexHull ℝ {o,u,v} ⊆ convexHull ℝ {a,b,c} := by
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      simp only [mem_insert_iff,mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ho
      · exact subset_convexHull ℝ _ hu
      · exact subset_convexHull ℝ _ hv
    rcases hx with (hx | hx) | hx
    · exact hs a b (by simp) (by simp) hx
    · exact hs b c (by simp) (by simp) hx
    · exact hs c a (by simp) (by simp) hx
  · intro hx
    obtain ⟨h1,h2,h3⟩ := (triangle_mem_iff a b c x hD).1 hx
    have hid : side b c o * side o a x + side c a o * side o b x +
        side a b o * side o c x = 0 := by
      simp only [side,RealPoint.det,RealPoint.sub]; ring
    rcases three_radial_cones (side o a x) (side o b x) (side o c x)
        (side b c o) (side c a o) (side a b o) hbc hca hab hid with h | h | h
    · exact Or.inl (Or.inl ((triangle_mem_iff o a b x hOb).2
        ⟨h.1,h1,by rw [side_reverse]; exact neg_nonneg.2 h.2⟩))
    · exact Or.inl (Or.inr ((triangle_mem_iff o b c x hOc).2
        ⟨h.1,h2,by rw [side_reverse]; exact neg_nonneg.2 h.2⟩))
    · exact Or.inr ((triangle_mem_iff o c a x hOa).2
        ⟨h.1,h3,by rw [side_reverse]; exact neg_nonneg.2 h.2⟩)

end
end SpectreGeometry
