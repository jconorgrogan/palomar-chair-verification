module

public import SpectreGeometry.FanRealGeometry

@[expose] public section


/-! Coverage around the fan center and the cancellation of internal radial
segments. The antipodal certified vertices supply the only global coverage
fact needed; no polygon boundary or Jordan theorem is assumed. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem radialSide_antipodal (x : RealPoint) : radialSide 0 x + radialSide 7 x = 0 := by
  norm_num [radialSide,realFanCenter,realVertex,realize,fanCenter,vertex,vertices,
    Quad3.eval,side,RealPoint.det,RealPoint.sub]
  ring

theorem radial_cones_cover (x : RealPoint) :
    ∃ i : Fin 14, 0 ≤ radialSide i x ∧ radialSide (next i) x ≤ 0 := by
  by_contra hnone
  have hstep (i : Fin 14) (hi : 0 ≤ radialSide i x) : 0 < radialSide (next i) x := by
    by_contra hn
    exact hnone ⟨i,hi,le_of_not_gt hn⟩
  have ha := radialSide_antipodal x
  by_cases h0 : 0 ≤ radialSide 0 x
  · have h1 := hstep 0 h0
    change 0 < radialSide 1 x at h1
    have h2 := hstep 1 h1.le
    change 0 < radialSide 2 x at h2
    have h3 := hstep 2 h2.le
    change 0 < radialSide 3 x at h3
    have h4 := hstep 3 h3.le
    change 0 < radialSide 4 x at h4
    have h5 := hstep 4 h4.le
    change 0 < radialSide 5 x at h5
    have h6 := hstep 5 h5.le
    change 0 < radialSide 6 x at h6
    have h7 := hstep 6 h6.le
    change 0 < radialSide 7 x at h7
    linarith
  · have h7 : 0 < radialSide 7 x := by linarith
    have h8 := hstep 7 h7.le
    change 0 < radialSide 8 x at h8
    have h9 := hstep 8 h8.le
    change 0 < radialSide 9 x at h9
    have h10 := hstep 9 h9.le
    change 0 < radialSide 10 x at h10
    have h11 := hstep 10 h10.le
    change 0 < radialSide 11 x at h11
    have h12 := hstep 11 h11.le
    change 0 < radialSide 12 x at h12
    have h13 := hstep 12 h12.le
    change 0 < radialSide 13 x at h13
    have h14 := hstep 13 h13.le
    change 0 < radialSide 0 x at h14
    linarith

theorem realFanCenter_mem_interior_polygonBody : realFanCenter ∈ interior polygonBody := by
  let U : Set RealPoint := ⋂ i : Fin 14, {x | 0 < side (realVertex i) (realVertex (next i)) x}
  have hopen : IsOpen U := isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (side_continuous _ _)
  have hc : realFanCenter ∈ U := mem_iInter.2 fan_real_positive
  have hsub : U ⊆ polygonBody := by
    intro x hx
    obtain ⟨i,h1,h3⟩ := radial_cones_cover x
    exact mem_iUnion.2 ⟨i,(triangleBody_mem_iff i x).2 ⟨h1,(mem_iInter.1 hx i).le,h3⟩⟩
  exact (interior_maximal hsub hopen) hc

theorem next_surjective (i : Fin 14) : ∃ j : Fin 14, next j = i := by
  have hh : ∀ i : Fin 14, ∃ j : Fin 14, next j = i := by decide
  exact hh i

theorem shared_radial_mem_interior (i : Fin 14) (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    interpolate realFanCenter (realVertex (next i)) t ∈ interior polygonBody := by
  let x := interpolate realFanCenter (realVertex (next i)) t
  let U : Set RealPoint := {y | 0 < radialSide i y ∧
    0 < side (realVertex i) (realVertex (next i)) y ∧
    0 < side (realVertex (next i)) (realVertex (next (next i))) y ∧
    radialSide (next (next i)) y < 0}
  have hopen : IsOpen U := (isOpen_lt continuous_const (side_continuous _ _)).inter
    ((isOpen_lt continuous_const (side_continuous _ _)).inter
    ((isOpen_lt continuous_const (side_continuous _ _)).inter
    (isOpen_lt (side_continuous _ _) continuous_const)))
  have hsub : U ⊆ polygonBody := by
    intro y hy
    by_cases hh : radialSide (next i) y ≤ 0
    · exact mem_iUnion.2 ⟨i,(triangleBody_mem_iff i y).2 ⟨hy.1.le,hy.2.1.le,hh⟩⟩
    · exact mem_iUnion.2 ⟨next i,(triangleBody_mem_iff (next i) y).2
        ⟨(lt_of_not_ge hh).le,hy.2.2.1.le,hy.2.2.2.le⟩⟩
  have hp := fan_real_positive i
  have hq := fan_real_positive (next i)
  have h1 : radialSide i x = t * side (realVertex i) (realVertex (next i)) realFanCenter := by
    unfold radialSide x
    rw [side_interpolate,side_self_left,mul_zero,zero_add,side_cyclic]
  have h2 : side (realVertex i) (realVertex (next i)) x =
      (1-t) * side (realVertex i) (realVertex (next i)) realFanCenter := by
    unfold x
    rw [side_interpolate,side_self_right,mul_zero,add_zero]
  have h3 : side (realVertex (next i)) (realVertex (next (next i))) x =
      (1-t) * side (realVertex (next i)) (realVertex (next (next i))) realFanCenter := by
    unfold x
    rw [side_interpolate,side_self_left,mul_zero,add_zero]
  have h4 : radialSide (next (next i)) x =
      -t * side (realVertex (next i)) (realVertex (next (next i))) realFanCenter := by
    unfold radialSide x
    rw [side_interpolate,side_self_left,mul_zero,zero_add]
    have he : side realFanCenter (realVertex (next (next i))) (realVertex (next i)) =
        -side (realVertex (next i)) (realVertex (next (next i))) realFanCenter := by
      simp only [side,RealPoint.det,RealPoint.sub]; ring
    rw [he]; ring
  have hx : x ∈ U := by
    change 0 < radialSide i x ∧ _
    rw [h1,h2,h3,h4]
    exact ⟨mul_pos ht hp,mul_pos (by linarith) hp,
      mul_pos (by linarith) hq,mul_neg_of_neg_of_pos (by linarith) hq⟩
  exact (interior_maximal hsub hopen) hx

end
end SpectreGeometry
