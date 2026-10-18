module

public import SpectreGeometry.CornerGermData
public import SpectreGeometry.EdgeNeighborhood

@[expose] public section


/-! Actual local polygon geometry at every one of the fourteen vertices.
Only the two incident fan triangles occur in a sufficiently small open
neighborhood. This includes both reflex corners and the retained midpoint. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem vertex_not_nonincident_triangle (i j : Fin 14) (hji : j ≠ i) (hn : next j ≠ i) :
    realVertex i ∉ triangleBody j := by
  obtain ⟨e,he⟩ := nonincident_vertex_strict_separator i j hji hn
  have hp := Quad3.positive_sound _ he
  rw [Quad3.eval_sub] at hp
  norm_num only [Quad3.eval,Int.cast_zero,mul_zero,zero_mul,zero_add] at hp
  have hid : realTriangleSide j e (realVertex i) =
      Quad3.eval (ExactPoint.det (triangleEdge j e)
        (ExactPoint.sub (vertex i) (triangleVertex j e)))/4 := by
    unfold realTriangleSide realVertex side
    rw [←realize_sub,←realize_sub,realize_det]
    rfl
  intro hx
  have hn := realTriangleSide_nonneg j e _ hx
  rw [hid] at hn
  dsimp [Quad3.eval] at hn
  linarith

def cornerBodyCondition (i : Fin 14) (y : RealPoint) : Prop :=
  (0 ≤ side (realVertex (previous i)) (realVertex i) y ∧ radialSide i y ≤ 0) ∨
  (0 ≤ radialSide i y ∧ 0 ≤ side (realVertex i) (realVertex (next i)) y)

/-- The displayed two-wedge formula is the actual body germ. -/
theorem vertex_local_body (i : Fin 14) :
    ∃ U : Set RealPoint, IsOpen U ∧ realVertex i ∈ U ∧
      (∀ y ∈ U, y ∈ polygonBody ↔ cornerBodyCondition i y) ∧
      (∀ y ∈ U, y ∈ frontier polygonBody →
        side (realVertex (previous i)) (realVertex i) y = 0 ∨
        side (realVertex i) (realVertex (next i)) y = 0) := by
  let O : Set RealPoint := ⋃ j : {j : Fin 14 // j ≠ i ∧ j ≠ previous i}, triangleBody j.val
  let U : Set RealPoint := Oᶜ ∩ {y | 0 < radialSide (previous i) y ∧ radialSide (next i) y < 0}
  have hO : IsClosed O := isClosed_iUnion_of_finite fun j => (triangleBody_compact j.val).isClosed
  have hU : IsOpen U := hO.isOpen_compl.inter
    ((isOpen_lt continuous_const (side_continuous _ _)).inter
      (isOpen_lt (side_continuous _ _) continuous_const))
  have hnot : realVertex i ∉ O := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    apply vertex_not_nonincident_triangle i j j.property.1 _ hj
    intro he
    have hh := congrArg previous he
    rw [previous_next] at hh
    exact j.property.2 hh
  have hp : 0 < radialSide (previous i) (realVertex i) := by
    have h := fan_real_positive_cyclic (previous i)
    rw [next_previous] at h
    exact h
  have hn : radialSide (next i) (realVertex i) < 0 := by
    have h := fan_real_positive_cyclic i
    have he : radialSide (next i) (realVertex i) =
        -side realFanCenter (realVertex i) (realVertex (next i)) := by
      simp only [radialSide,side,RealPoint.det,RealPoint.sub]
      ring
    rw [he]
    exact neg_neg_of_pos h
  refine ⟨U,hU,⟨hnot,hp,hn⟩,?_,?_⟩
  · intro y hy
    constructor
    · intro hbody
      obtain ⟨j,hj⟩ := mem_iUnion.mp hbody
      by_cases he : j = i
      · subst j
        obtain ⟨hr,hs,hn⟩ := (triangleBody_mem_iff i y).1 hj
        exact Or.inr ⟨hr,hs⟩
      · by_cases he' : j = previous i
        · subst j
          obtain ⟨hr,hs,hn⟩ := (triangleBody_mem_iff (previous i) y).1 hj
          rw [next_previous] at hs hn
          exact Or.inl ⟨hs,hn⟩
        · exact False.elim (hy.1 (mem_iUnion.mpr ⟨⟨j,he,he'⟩,hj⟩))
    · intro hc
      rcases hc with ⟨hs,hr⟩ | ⟨hr,hs⟩
      · apply mem_iUnion.mpr
        refine ⟨previous i,(triangleBody_mem_iff (previous i) y).2 ?_⟩
        rw [next_previous]
        exact ⟨hy.2.1.le,hs,hr⟩
      · exact mem_iUnion.mpr ⟨i,(triangleBody_mem_iff i y).2 ⟨hr,hs,hy.2.2.le⟩⟩
  · intro y hy hf
    rw [polygonBody_frontier_eq_edges] at hf
    obtain ⟨j,hj⟩ := mem_iUnion.mp hf
    have hz : side (realVertex j) (realVertex (next j)) y = 0 := by
      obtain ⟨t,ht,ht',rfl⟩ := hj
      exact det_interpolate_self _ _ _
    by_cases he : j = i
    · exact Or.inr (he ▸ hz)
    · by_cases he' : j = previous i
      · subst j
        rw [next_previous] at hz
        exact Or.inl hz
      · exact False.elim (hy.1 (mem_iUnion.mpr ⟨⟨j,he,he'⟩,polygonEdge_mem_triangleBody j hj⟩))

/-- Away from both incident supporting lines, the same finite wedge test
characterizes actual interior membership. -/
theorem vertex_local_interior_off_lines (i : Fin 14) :
    ∃ U : Set RealPoint, IsOpen U ∧ realVertex i ∈ U ∧
      ∀ y ∈ U, side (realVertex (previous i)) (realVertex i) y ≠ 0 →
        side (realVertex i) (realVertex (next i)) y ≠ 0 →
        (y ∈ interior polygonBody ↔ cornerBodyCondition i y) := by
  obtain ⟨U,hU,hi,hbody,hfront⟩ := vertex_local_body i
  refine ⟨U,hU,hi,?_⟩
  intro y hy hprev hnext
  constructor
  · intro h
    exact (hbody y hy).1 (interior_subset h)
  · intro hc
    have hm := (hbody y hy).2 hc
    by_contra hn
    have hf : y ∈ frontier polygonBody := ⟨subset_closure hm,hn⟩
    exact (hfront y hy hf).elim hprev hnext

end
end SpectreGeometry
