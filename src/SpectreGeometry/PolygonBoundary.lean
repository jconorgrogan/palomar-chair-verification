module

public import SpectreGeometry.FanSeparation
public import SpectreGeometry.FanCoverage

@[expose] public section


/-! The topological frontier of the actual fourteen-triangle carrier is
exactly the fourteen certified outer segments. Internal radial sides are
proved interior, and the outer segments are proved frontier points. -/
namespace SpectreGeometry
noncomputable section
open Set

@[simp] theorem interpolate_zero (a b : RealPoint) : interpolate a b 0 = a := by
  simp [interpolate]
@[simp] theorem interpolate_one (a b : RealPoint) : interpolate a b 1 = b := by
  simp [interpolate]

theorem interpolate_swap (a b : RealPoint) (t : ℝ) :
    interpolate a b t = interpolate b a (1-t) := by
  apply Prod.ext <;> simp only [interpolate] <;> ring

theorem closedSegmentR_symm (a b : RealPoint) : closedSegmentR a b = closedSegmentR b a := by
  apply Set.ext
  intro x
  constructor <;> rintro ⟨t,ht,ht',rfl⟩ <;>
    exact ⟨1-t,by linarith,by linarith,interpolate_swap _ _ _⟩

theorem radial_segment_nonvertex_interior (i : Fin 14) (x : RealPoint)
    (hx : x ∈ closedSegmentR realFanCenter (realVertex i)) (hne : x ≠ realVertex i) :
    x ∈ interior polygonBody := by
  obtain ⟨t,ht,ht',rfl⟩ := hx
  by_cases hz : t = 0
  · simpa [hz] using realFanCenter_mem_interior_polygonBody
  have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  have hp' : t < 1 := by
    by_contra hn
    have he : t = 1 := by linarith
    exact hne (by simp [he])
  obtain ⟨j,hj⟩ := next_surjective i
  have hh := shared_radial_mem_interior j t hp hp'
  rwa [hj] at hh

theorem vertex_mem_polygonEdge (i : Fin 14) : realVertex i ∈ polygonEdge i :=
  ⟨0,by norm_num,by norm_num,by simp⟩

theorem body_nonedge_mem_interior (x : RealPoint) (hx : x ∈ polygonBody)
    (hedge : x ∉ ⋃ i : Fin 14, polygonEdge i) : x ∈ interior polygonBody := by
  obtain ⟨i,hi⟩ := mem_iUnion.1 hx
  obtain ⟨h1,h2,h3⟩ := (triangleBody_mem_iff i x).1 hi
  have hbase : 0 < side (realVertex i) (realVertex (next i)) x := by
    by_contra hn
    have hz : side (realVertex i) (realVertex (next i)) x = 0 := by linarith
    have hs := triangle_side_zero_segment (realVertex i) (realVertex (next i))
      realFanCenter x (fan_real_positive i) hi hz
    exact hedge (mem_iUnion.2 ⟨i,hs⟩)
  by_cases ha : radialSide i x = 0
  · have hs := triangle_side_zero_segment realFanCenter (realVertex i) (realVertex (next i))
      x (fan_real_positive_cyclic i) (by rwa [←triangleBody_cyclic]) ha
    apply radial_segment_nonvertex_interior i x hs
    intro he
    exact hedge (mem_iUnion.2 ⟨i,he.symm ▸ vertex_mem_polygonEdge i⟩)
  by_cases hb : radialSide (next i) x = 0
  · have hrot : triangleBody i = convexHull ℝ {realVertex (next i),realFanCenter,realVertex i} := by
      rw [triangleBody_cyclic]
      congr 1
      ext y
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    have hd : 0 < side (realVertex (next i)) realFanCenter (realVertex i) := by
      rw [side_cyclic]
      exact fan_real_positive_cyclic i
    have hz : side (realVertex (next i)) realFanCenter x = 0 := by
      rw [side_reverse]
      exact neg_eq_zero.2 hb
    have hs := triangle_side_zero_segment (realVertex (next i)) realFanCenter (realVertex i)
      x hd (by rwa [←hrot]) hz
    rw [closedSegmentR_symm] at hs
    apply radial_segment_nonvertex_interior (next i) x hs
    intro he
    exact hedge (mem_iUnion.2 ⟨next i,he.symm ▸ vertex_mem_polygonEdge (next i)⟩)
  apply interior_mono (subset_iUnion triangleBody i)
  exact (triangleBody_interior_iff i x).2 ⟨lt_of_le_of_ne h1 (Ne.symm ha),hbase,
    lt_of_le_of_ne h3 hb⟩

theorem polygonBody_frontier_subset_edges : frontier polygonBody ⊆ ⋃ i : Fin 14, polygonEdge i := by
  intro x hx
  by_contra hn
  have hm : x ∈ polygonBody := by
    have hh := frontier_subset_closure hx
    rwa [polygonBody_compact.isClosed.closure_eq] at hh
  exact hx.2 (body_nonedge_mem_interior x hm hn)

theorem outer_edge_midpoint_interior (i : Fin 14) (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    interpolate realFanCenter (interpolate (realVertex i) (realVertex (next i)) t) (1/2) ∈
      interior (triangleBody i) := by
  let x := interpolate realFanCenter (interpolate (realVertex i) (realVertex (next i)) t) (1/2)
  have hp := fan_real_positive i
  have h1 : radialSide i x = t/2 * side (realVertex i) (realVertex (next i)) realFanCenter := by
    simp only [x,radialSide,interpolate,side,RealPoint.det,RealPoint.sub]; ring
  have h2 : side (realVertex i) (realVertex (next i)) x =
      side (realVertex i) (realVertex (next i)) realFanCenter / 2 := by
    simp only [x,interpolate,side,RealPoint.det,RealPoint.sub]; ring
  have h3 : radialSide (next i) x = -(1-t)/2 *
      side (realVertex i) (realVertex (next i)) realFanCenter := by
    simp only [x,radialSide,interpolate,side,RealPoint.det,RealPoint.sub]; ring
  apply (triangleBody_interior_iff i x).2
  rw [h1,h2,h3]
  exact ⟨mul_pos (by positivity) hp,by positivity,
    mul_neg_of_neg_of_pos (by linarith) hp⟩

theorem outer_open_edge_not_other_triangle (i j : Fin 14) (hij : i ≠ j)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    interpolate (realVertex i) (realVertex (next i)) t ∉ triangleBody j := by
  intro hx
  let x := interpolate (realVertex i) (realVertex (next i)) t
  have hc := realFanCenter_mem_triangleBody j
  have hy : (1/2 : ℝ) • realFanCenter + (1/2 : ℝ) • x ∈ triangleBody j :=
    (convex_convexHull ℝ {realVertex j,realVertex (next j),realize fanCenter})
      hc hx (by norm_num) (by norm_num) (by norm_num)
  have he : (1/2 : ℝ) • realFanCenter + (1/2 : ℝ) • x = interpolate realFanCenter x (1/2) := by
    apply Prod.ext <;> simp only [interpolate,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  rw [he] at hy
  exact Set.disjoint_left.1 (triangleBody_interior_disjoint_body i j hij)
    (outer_edge_midpoint_interior i t ht ht') hy

theorem outer_open_edge_mem_frontier (i : Fin 14) (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    interpolate (realVertex i) (realVertex (next i)) t ∈ frontier polygonBody := by
  let x := interpolate (realVertex i) (realVertex (next i)) t
  have hx : x ∈ polygonEdge i := ⟨t,ht.le,ht'.le,rfl⟩
  have hm : x ∈ polygonBody := mem_iUnion.2 ⟨i,polygonEdge_mem_triangleBody i hx⟩
  have hn : x ∉ interior polygonBody := by
    intro hi
    let O : Set RealPoint := ⋃ j : {j : Fin 14 // j ≠ i}, triangleBody j.val
    have hc : IsClosed O := isClosed_iUnion_of_finite fun j => (triangleBody_compact j.val).isClosed
    have hnot : x ∉ O := by
      intro hh
      obtain ⟨j,hj⟩ := mem_iUnion.1 hh
      exact outer_open_edge_not_other_triangle i j.val (Ne.symm j.property) t ht ht' hj
    have hsub : interior polygonBody ∩ Oᶜ ⊆ triangleBody i := by
      rintro y ⟨hy,ho⟩
      obtain ⟨j,hj⟩ := mem_iUnion.1 (interior_subset hy)
      by_cases he : j = i
      · simpa [he] using hj
      · exact False.elim (ho (mem_iUnion.2 ⟨⟨j,he⟩,hj⟩))
    have hix : x ∈ interior (triangleBody i) :=
      (interior_maximal hsub (isOpen_interior.inter hc.isOpen_compl)) ⟨hi,hnot⟩
    have hp := ((triangleBody_interior_iff i x).1 hix).2.1
    have hz : side (realVertex i) (realVertex (next i)) x = 0 := by
      unfold x
      rw [side_interpolate]
      simp
    linarith
  exact ⟨subset_closure hm,hn⟩

theorem polygonEdge_subset_frontier (i : Fin 14) : polygonEdge i ⊆ frontier polygonBody := by
  let f : ℝ → RealPoint := interpolate (realVertex i) (realVertex (next i))
  have hf : Continuous f := by unfold f interpolate; fun_prop
  have hc : IsClosed (f ⁻¹' frontier polygonBody) := isClosed_frontier.preimage hf
  have hs : Ioo (0 : ℝ) 1 ⊆ f ⁻¹' frontier polygonBody := by
    intro t ht
    exact outer_open_edge_mem_frontier i t ht.1 ht.2
  have hh := closure_minimal hs hc
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hh
  rintro x ⟨t,ht,ht',rfl⟩
  exact hh ⟨ht,ht'⟩

theorem polygonBody_frontier_eq_edges : frontier polygonBody = ⋃ i : Fin 14, polygonEdge i := by
  apply Subset.antisymm polygonBody_frontier_subset_edges
  exact iUnion_subset polygonEdge_subset_frontier

end
end SpectreGeometry
