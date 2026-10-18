module

public import SpectreGeometry.PolygonReal

@[expose] public section


/-! Exact intersection laws for the actual fourteen real boundary segments.
The polygon is a simple closed edge cycle, retaining the midpoint of its
straight side. No tiling registration is inferred from these local facts. -/
namespace SpectreGeometry
noncomputable section

def interpolate (a b : RealPoint) (t : ℝ) : RealPoint :=
  ((1-t)*a.1+t*b.1,(1-t)*a.2+t*b.2)

def closedSegmentR (a b : RealPoint) : Set RealPoint :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = interpolate a b t}

def polygonEdge (i : Fin 14) : Set RealPoint := closedSegmentR (realVertex i) (realVertex (next i))

theorem det_interpolate_self (a b : RealPoint) (t : ℝ) :
    RealPoint.det (RealPoint.sub b a) (RealPoint.sub (interpolate a b t) a) = 0 := by
  simp only [RealPoint.det,RealPoint.sub,interpolate]
  ring

theorem det_interpolate (v a b c : RealPoint) (t : ℝ) :
    RealPoint.det v (RealPoint.sub (interpolate b c t) a) =
      (1-t)*RealPoint.det v (RealPoint.sub b a)+t*RealPoint.det v (RealPoint.sub c a) := by
  simp only [RealPoint.det,RealPoint.sub,interpolate]
  ring

theorem convex_combo_nonzero {A B t : ℝ} (hp : 0 < A*B) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (1-t)*A+t*B ≠ 0 := by
  rcases mul_pos_iff.mp hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · apply ne_of_gt
    by_cases hz : t = 0
    · simpa [hz] using ha
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (le_of_lt ha))
        (mul_pos (lt_of_le_of_ne ht (Ne.symm hz)) hb)
  · apply ne_of_lt
    by_cases hz : t = 0
    · simpa [hz] using ha
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt ha))
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne ht (Ne.symm hz)) hb)

theorem segments_disjoint_of_separator (a b c d : RealPoint)
    (hp : 0 < RealPoint.det (RealPoint.sub b a) (RealPoint.sub c a) *
      RealPoint.det (RealPoint.sub b a) (RealPoint.sub d a)) :
    Disjoint (closedSegmentR a b) (closedSegmentR c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht,ht',hxt⟩ := hx
  obtain ⟨u,hu,hu',hxu⟩ := hy
  have hz : RealPoint.det (RealPoint.sub b a) (RealPoint.sub x a) = 0 := by
    rw [hxt]; exact det_interpolate_self a b t
  have hn : RealPoint.det (RealPoint.sub b a) (RealPoint.sub x a) ≠ 0 := by
    rw [hxu,det_interpolate]
    exact convex_combo_nonzero hp hu hu'
  exact hn hz

theorem polygon_edges_disjoint (i j : Fin 14)
    (hij : i ≠ j) (hnext : next i ≠ j) (hprev : next j ≠ i) :
    Disjoint (polygonEdge i) (polygonEdge j) := by
  rcases real_nonadjacent_separated i j hij hnext hprev with h | h
  · exact segments_disjoint_of_separator _ _ _ _ h
  · exact (segments_disjoint_of_separator _ _ _ _ h).symm

theorem adjacent_segment_intersection (a b c : RealPoint)
    (hpos : 0 < RealPoint.dot (RealPoint.sub b a) (RealPoint.sub b a))
    (hdot : 0 ≤ RealPoint.dot (RealPoint.sub b a) (RealPoint.sub c b)) :
    closedSegmentR a b ∩ closedSegmentR b c = {b} := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨⟨t,ht,ht',hxt⟩,⟨u,hu,hu',hxu⟩⟩
    have hline : (t-1)*RealPoint.dot (RealPoint.sub b a) (RealPoint.sub b a) =
        u*RealPoint.dot (RealPoint.sub b a) (RealPoint.sub c b) := by
      have h := congrArg (fun y => RealPoint.dot (RealPoint.sub b a) (RealPoint.sub y b))
        (hxt.symm.trans hxu)
      have hl : RealPoint.dot (RealPoint.sub b a) (RealPoint.sub (interpolate a b t) b) =
          (t-1)*RealPoint.dot (RealPoint.sub b a) (RealPoint.sub b a) := by
        simp only [RealPoint.dot,RealPoint.sub,interpolate]; ring
      have hr : RealPoint.dot (RealPoint.sub b a) (RealPoint.sub (interpolate b c u) b) =
          u*RealPoint.dot (RealPoint.sub b a) (RealPoint.sub c b) := by
        simp only [RealPoint.dot,RealPoint.sub,interpolate]; ring
      rwa [hl,hr] at h
    have hnonneg := mul_nonneg hu hdot
    have ht1 : t = 1 := by nlinarith
    have hx : x = b := by simpa [ht1,interpolate] using hxt
    exact hx
  · intro hx
    have hx' : x = b := hx
    subst x
    constructor
    · exact ⟨1,by norm_num,by norm_num,by simp [interpolate]⟩
    · exact ⟨0,by norm_num,by norm_num,by simp [interpolate]⟩

theorem polygon_adjacent_intersection (i : Fin 14) :
    polygonEdge i ∩ polygonEdge (next i) = {realVertex (next i)} := by
  apply adjacent_segment_intersection
  · change 0 < RealPoint.dot (realEdge i) (realEdge i)
    rw [real_edges_unit_squared]; norm_num
  · exact real_adjacent_dot_nonnegative i

end
end SpectreGeometry
