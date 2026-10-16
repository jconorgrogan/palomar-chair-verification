module

public import SpectreGeometry.FanRealGeometry

@[expose] public section


/-! Nonoverlap of the actual closed fan triangles, obtained from the finite
support-side certificates, rather than assumed from a polygon picture. -/
namespace SpectreGeometry
noncomputable section
open Set

def realTriangleSide (i : Fin 14) (e : Fin 3) (x : RealPoint) : ℝ :=
  side (realize (triangleVertex i e)) (realize (triangleVertex i (triangleNext e))) x

theorem nonpositive_real_sound (q : Quad3) (hq : Quad3.nonpositive q) : Quad3.eval q ≤ 0 := by
  rcases hq with hz | hp
  · rw [hz]; norm_num [Quad3.eval]
  · have h := Quad3.positive_sound _ hp
    rw [Quad3.eval_sub] at h
    norm_num [Quad3.eval] at h ⊢
    linarith

theorem realTriangleSide_nonneg (i : Fin 14) (e : Fin 3) (x : RealPoint)
    (hx : x ∈ triangleBody i) : 0 ≤ realTriangleSide i e x := by
  obtain ⟨h1,h2,h3⟩ := (triangleBody_mem_iff i x).1 hx
  fin_cases e
  · exact h1
  · exact h2
  · change 0 ≤ side (realVertex (next i)) realFanCenter x
    rw [side_reverse]
    exact neg_nonneg.2 h3

theorem realTriangleSide_pos (i : Fin 14) (e : Fin 3) (x : RealPoint)
    (hx : x ∈ interior (triangleBody i)) : 0 < realTriangleSide i e x := by
  obtain ⟨h1,h2,h3⟩ := (triangleBody_interior_iff i x).1 hx
  fin_cases e
  · exact h1
  · exact h2
  · change 0 < side (realVertex (next i)) realFanCenter x
    rw [side_reverse]
    exact neg_pos.2 h3

theorem real_triangle_separator (i j : Fin 14) (e : Fin 3)
    (he : TriangleSideSeparates i j e) (x : RealPoint) (hx : x ∈ triangleBody j) :
    realTriangleSide i e x ≤ 0 := by
  have hv : ∀ v : Fin 3, realTriangleSide i e (realize (triangleVertex j v)) ≤ 0 := by
    intro v
    have hh := nonpositive_real_sound _ (he v)
    have hid : realTriangleSide i e (realize (triangleVertex j v)) =
        Quad3.eval (ExactPoint.det (triangleEdge i e)
          (ExactPoint.sub (triangleVertex j v) (triangleVertex i e)))/4 := by
      unfold realTriangleSide side
      rw [←realize_sub,←realize_sub,realize_det]
      rfl
    rw [hid]
    linarith
  rw [triangleBody_cyclic] at hx
  apply side_nonpos_hull _ _ {realFanCenter,realVertex j,realVertex (next j)} _ x hx
  intro y hy
  simp only [mem_insert_iff,mem_singleton_iff] at hy
  rcases hy with hy | hy | hy
  · subst y; exact hv 0
  · subst y; exact hv 1
  · subst y; exact hv 2

theorem triangleBody_interiors_disjoint (i j : Fin 14) (hij : i ≠ j) :
    Disjoint (interior (triangleBody i)) (interior (triangleBody j)) := by
  apply Set.disjoint_left.2
  intro x hi hj
  rcases fan_pairs_separated i j hij with ⟨e,he⟩ | ⟨e,he⟩
  · have hp := realTriangleSide_pos i e x hi
    have hn := real_triangle_separator i j e he x (interior_subset hj)
    linarith
  · have hp := realTriangleSide_pos j e x hj
    have hn := real_triangle_separator j i e he x (interior_subset hi)
    linarith

theorem triangleBody_interior_disjoint_body (i j : Fin 14) (hij : i ≠ j) :
    Disjoint (interior (triangleBody i)) (triangleBody j) := by
  have h := (triangleBody_interiors_disjoint i j hij).closure_right isOpen_interior
  rwa [triangleBody_closure_interior] at h

theorem realFanCenter_mem_triangleBody (i : Fin 14) : realFanCenter ∈ triangleBody i := by
  rw [triangleBody_cyclic]
  exact subset_convexHull ℝ _ (by simp)

theorem polygonEdge_mem_triangleBody (i : Fin 14) : polygonEdge i ⊆ triangleBody i := by
  rintro x ⟨t,ht,ht',rfl⟩
  apply (triangleBody_mem_iff i _).2
  have hp := fan_real_positive i
  have hc := fan_real_positive_cyclic i
  have h1 : radialSide i (interpolate (realVertex i) (realVertex (next i)) t) =
      t * side realFanCenter (realVertex i) (realVertex (next i)) := by
    unfold radialSide
    rw [side_interpolate]
    simp
  have h2 : side (realVertex i) (realVertex (next i))
      (interpolate (realVertex i) (realVertex (next i)) t) = 0 := by
    rw [side_interpolate]; simp
  have h3 : radialSide (next i) (interpolate (realVertex i) (realVertex (next i)) t) =
      -(1-t) * side realFanCenter (realVertex i) (realVertex (next i)) := by
    unfold radialSide
    rw [side_interpolate]
    simp only [side_self_right,mul_zero,add_zero]
    have he : side realFanCenter (realVertex (next i)) (realVertex i) =
        -side realFanCenter (realVertex i) (realVertex (next i)) := by
      simp only [side,RealPoint.det,RealPoint.sub]; ring
    rw [he]; ring
  rw [h1,h2,h3]
  exact ⟨mul_nonneg ht hc.le,le_refl _,mul_nonpos_of_nonpos_of_nonneg (by linarith) hc.le⟩

end
end SpectreGeometry
