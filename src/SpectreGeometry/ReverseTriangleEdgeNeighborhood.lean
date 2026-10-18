module

public import SpectreGeometry.TriangleGeometry

@[expose] public section


/-! The common relative-open edge of two nondegenerate plane triangles with
nonoverlapping interiors is interior to their union. The ambient space is
explicitly RealPoint = real two-space throughout. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Filter Topology

private theorem interpolate_swap (a b : RealPoint) (t : ℝ) :
    interpolate b a (1-t) = interpolate a b t := by
  ext <;> simp only [interpolate] <;> ring

private theorem triangle_hull_swap (a b c : RealPoint) :
    convexHull ℝ {b,a,c} = convexHull ℝ {a,b,c} := by
  congr 1
  ext y
  simp only [mem_insert_iff,mem_singleton_iff]
  tauto

private theorem open_edge_other_sides (a b c : RealPoint) (hD : 0 < side a b c)
    (t : ℝ) (ht : 0<t) (ht' : t<1) :
    0 < side b c (interpolate a b t) ∧ 0 < side c a (interpolate a b t) := by
  constructor
  · simp only [side_interpolate,side_self_left,mul_zero,add_zero]
    rw [←side_cyclic a b c]
    exact mul_pos (by linarith) hD
  · simp only [side_interpolate,side_self_right,mul_zero,zero_add]
    rw [side_cyclic c a b]
    exact mul_pos ht hD

/-- Two triangles on the same strict side of their common edge necessarily
have overlapping ordinary plane interiors. -/
theorem not_disjoint_triangle_interiors_of_same_side (a b c d : RealPoint)
    (hc : 0 < side a b c) (hd : 0 < side a b d) :
    ¬Disjoint (interior (convexHull ℝ {a,b,c}))
      (interior (convexHull ℝ {a,b,d})) := by
  intro hdisjoint
  let p := interpolate a b (1/2 : ℝ)
  let U : Set RealPoint := {y | 0 < side b c y ∧ 0 < side c a y ∧
    0 < side b d y ∧ 0 < side d a y}
  have hU : IsOpen U := (isOpen_lt continuous_const (side_continuous b c)).inter
    ((isOpen_lt continuous_const (side_continuous c a)).inter
      ((isOpen_lt continuous_const (side_continuous b d)).inter
        (isOpen_lt continuous_const (side_continuous d a))))
  have hp : p ∈ U := by
    have hpC := open_edge_other_sides a b c hc (1/2) (by norm_num) (by norm_num)
    have hpD := open_edge_other_sides a b d hd (1/2) (by norm_num) (by norm_num)
    exact ⟨hpC.1,hpC.2,hpD.1,hpD.2⟩
  let q : ℝ → RealPoint := fun t => interpolate p c t
  have hq : Continuous q := by unfold q interpolate; fun_prop
  have hq0 : q 0 = p := by ext <;> simp [q,interpolate]
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ U :=
    hq.continuousAt.preimage_mem_nhds (hU.mem_nhds (hq0.symm ▸ hp))
  obtain ⟨t,ht,htU⟩ := hevent.exists_gt
  have hz : side a b p = 0 := det_interpolate_self a b (1/2)
  have hside : 0 < side a b (q t) := by
    change 0 < side a b (interpolate p c t)
    rw [side_interpolate,hz]
    simpa using mul_pos ht hc
  exact Set.disjoint_left.mp hdisjoint
    (strict_sides_mem_interior a b c (q t) hc ⟨hside,htU.1,htU.2.1⟩)
    (strict_sides_mem_interior a b d (q t) hd ⟨hside,htU.2.2.1,htU.2.2.2⟩)

/-- Nondegeneracy plus ordinary-interior disjointness forces the second
triangle onto the opposite supporting halfplane. -/
theorem opposite_side_of_disjoint_triangle_interiors (a b c d : RealPoint)
    (hc : 0 < side a b c) (hd : side a b d ≠ 0)
    (hdisjoint : Disjoint (interior (convexHull ℝ {a,b,c}))
      (interior (convexHull ℝ {a,b,d}))) : side a b d < 0 := by
  by_contra hn
  have hp : 0 < side a b d := lt_of_le_of_ne (le_of_not_gt hn) hd.symm
  exact not_disjoint_triangle_interiors_of_same_side a b c d hc hp hdisjoint

/-- Opposite halfplanes cover a neighborhood of every relative-open-edge point. -/
theorem open_edge_mem_interior_triangle_union_of_opposite_sides (a b c d : RealPoint)
    (hc : 0 < side a b c) (hd : side a b d < 0)
    (t : ℝ) (ht : 0<t) (ht' : t<1) :
    interpolate a b t ∈ interior (convexHull ℝ {a,b,c} ∪ convexHull ℝ {a,b,d}) := by
  have hd' : 0 < side b a d := by rw [side_reverse]; linarith
  let U : Set RealPoint := {y | 0 < side b c y ∧ 0 < side c a y ∧
    0 < side a d y ∧ 0 < side d b y}
  have hU : IsOpen U := (isOpen_lt continuous_const (side_continuous b c)).inter
    ((isOpen_lt continuous_const (side_continuous c a)).inter
      ((isOpen_lt continuous_const (side_continuous a d)).inter
        (isOpen_lt continuous_const (side_continuous d b))))
  have hp : interpolate a b t ∈ U := by
    have hpC := open_edge_other_sides a b c hc t ht ht'
    have hpD := open_edge_other_sides b a d hd' (1-t) (by linarith) (by linarith)
    rw [interpolate_swap] at hpD
    exact ⟨hpC.1,hpC.2,hpD.1,hpD.2⟩
  refine (interior_maximal (t := U) (s := convexHull ℝ {a,b,c} ∪ convexHull ℝ {a,b,d}) ?_ hU) hp
  intro y hy
  by_cases hside : 0 ≤ side a b y
  · exact Or.inl ((triangle_mem_iff a b c y hc).mpr ⟨hside,hy.1.le,hy.2.1.le⟩)
  · apply Or.inr
    rw [←triangle_hull_swap a b d]
    apply (triangle_mem_iff b a d y hd').mpr
    refine ⟨?_,hy.2.2.1.le,hy.2.2.2.le⟩
    rw [side_reverse]
    exact neg_nonneg.mpr (le_of_not_ge hside)

/-- The two-dimensional nonvertex edge-star criterion. The nonzero side
hypotheses also force the two common edge endpoints to be distinct. -/
theorem open_edge_mem_interior_triangle_union (a b c d : RealPoint)
    (hc : side a b c ≠ 0) (hd : side a b d ≠ 0)
    (hdisjoint : Disjoint (interior (convexHull ℝ {a,b,c}))
      (interior (convexHull ℝ {a,b,d})))
    (t : ℝ) (ht : 0<t) (ht' : t<1) :
    interpolate a b t ∈ interior (convexHull ℝ {a,b,c} ∪ convexHull ℝ {a,b,d}) := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · have hc' : 0 < side b a c := by rw [side_reverse]; linarith
    have hd' : side b a d ≠ 0 := by rw [side_reverse]; exact neg_ne_zero.mpr hd
    have hswap : Disjoint (interior (convexHull ℝ {b,a,c}))
        (interior (convexHull ℝ {b,a,d})) := by
      rw [triangle_hull_swap a b c,triangle_hull_swap a b d]
      exact hdisjoint
    have hD := opposite_side_of_disjoint_triangle_interiors b a c d hc' hd' hswap
    have hp := open_edge_mem_interior_triangle_union_of_opposite_sides b a c d hc' hD
      (1-t) (by linarith) (by linarith)
    simpa only [interpolate_swap,triangle_hull_swap a b c,triangle_hull_swap a b d] using hp
  · exact open_edge_mem_interior_triangle_union_of_opposite_sides a b c d hc
      (opposite_side_of_disjoint_triangle_interiors a b c d hc hd hdisjoint) t ht ht'

/-- The affine line-map form of the same plane edge-star criterion. -/
theorem lineMap_mem_interior_triangle_union (a b c d : RealPoint)
    (hc : side a b c ≠ 0) (hd : side a b d ≠ 0)
    (hdisjoint : Disjoint (interior (convexHull ℝ {a,b,c}))
      (interior (convexHull ℝ {a,b,d})))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    AffineMap.lineMap a b t ∈ interior (convexHull ℝ {a,b,c} ∪ convexHull ℝ {a,b,d}) := by
  have hi : interpolate a b t = AffineMap.lineMap a b t := by
    apply Prod.ext <;> simp only [interpolate,AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
      Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  rw [←hi]
  exact open_edge_mem_interior_triangle_union a b c d hc hd hdisjoint t ht.1 ht.2

/-- Carrier-facing version: a common edge point that is neither endpoint. -/
theorem segment_nonendpoint_mem_interior_triangle_union (a b c d x : RealPoint)
    (hc : side a b c ≠ 0) (hd : side a b d ≠ 0)
    (hdisjoint : Disjoint (interior (convexHull ℝ {a,b,c}))
      (interior (convexHull ℝ {a,b,d})))
    (hx : x ∈ closedSegmentR a b) (hxa : x ≠ a) (hxb : x ≠ b) :
    x ∈ interior (convexHull ℝ {a,b,c} ∪ convexHull ℝ {a,b,d}) := by
  obtain ⟨t,ht,ht',rfl⟩ := hx
  have ht0 : t ≠ 0 := by
    intro hz
    apply hxa
    subst t
    ext <;> simp [interpolate]
  have ht1 : t ≠ 1 := by
    intro hz
    apply hxb
    subst t
    ext <;> simp [interpolate]
  exact open_edge_mem_interior_triangle_union a b c d hc hd hdisjoint t
    (lt_of_le_of_ne ht ht0.symm) (lt_of_le_of_ne ht' ht1)

end
end SpectreGeometry.ReverseExistence
