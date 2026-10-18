module

public import SpectreGeometry.DeformationTriangulationReal
public import SpectreGeometry.ConvexZeroFace
public import SpectreGeometry.FanSeparation

@[expose] public section


/-! Exact common-face intersections for the twelve source triangles. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

def sourceVertices (i : Fin 12) : Set RealPoint := Set.range (fun v : Fin 3 => realVertex (triangleIndex i v))

theorem sourceTriangle_eq_hull (i : Fin 12) : sourceTriangle i = convexHull ℝ (sourceVertices i) := by
  unfold sourceTriangle
  apply congrArg (convexHull ℝ)
  ext x
  simp only [sourceVertices,mem_range,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false,
    mem_insert_iff,mem_singleton_iff]
  change (x=realVertex (triangle i).1 ∨ x=realVertex (triangle i).2.1 ∨ x=realVertex (triangle i).2.2) ↔
    (realVertex (triangle i).1=x ∨ realVertex (triangle i).2.1=x ∨ realVertex (triangle i).2.2=x)
  tauto

theorem sourceTriangle_cyclic (i : Fin 12) (e : Fin 3) : sourceTriangle i =
    convexHull ℝ {realVertex (triangleIndex i e),realVertex (triangleIndex i (triangleNext e)),
      realVertex (triangleIndex i (triangleNext (triangleNext e)))} := by
  unfold sourceTriangle
  apply congrArg (convexHull ℝ)
  fin_cases e <;> ext x <;>
    simp [triangleIndex,triangleNext,or_comm,or_left_comm,or_assoc]

theorem sourceTriangle_cyclic_positive (i : Fin 12) (e : Fin 3) :
    0 < side (realVertex (triangleIndex i e)) (realVertex (triangleIndex i (triangleNext e)))
      (realVertex (triangleIndex i (triangleNext (triangleNext e)))) := by
  fin_cases e
  · exact sourceTriangle_positive i
  · change 0 < side (realVertex (triangle i).2.1) (realVertex (triangle i).2.2) (realVertex (triangle i).1)
    rw [←side_cyclic]
    exact sourceTriangle_positive i
  · change 0 < side (realVertex (triangle i).2.2) (realVertex (triangle i).1) (realVertex (triangle i).2.1)
    rw [side_cyclic]
    exact sourceTriangle_positive i

theorem sourceTriangle_side_nonnegative (i : Fin 12) (e : Fin 3) (x : RealPoint)
    (hx : x ∈ sourceTriangle i) :
    0 ≤ side (realVertex (triangleIndex i e)) (realVertex (triangleIndex i (triangleNext e))) x := by
  rw [sourceTriangle_cyclic i e] at hx
  exact ((triangle_mem_iff _ _ _ x (sourceTriangle_cyclic_positive i e)).1 hx).1

theorem nonpositive_quad_zero (q : Quad3) (h : Quad3.nonpositive q) (hz : Quad3.eval q = 0) : q=(0,0) := by
  rcases h with h | h
  · exact h
  · have hp := Quad3.positive_sound _ h
    rw [Quad3.eval_sub,hz] at hp
    norm_num [Quad3.eval] at hp

theorem commonFaceSupport_real (i j : Fin 12) (e : Fin 3) (h : CommonFaceSupport i j e)
    (y : RealPoint) (hy : y ∈ sourceVertices j) :
    side (realVertex (triangleIndex i e)) (realVertex (triangleIndex i (triangleNext e))) y ≤ 0 ∧
      (side (realVertex (triangleIndex i e)) (realVertex (triangleIndex i (triangleNext e))) y = 0 →
        y ∈ sourceVertices i ∩ sourceVertices j) := by
  obtain ⟨v,rfl⟩ := hy
  obtain ⟨hn,hz⟩ := h v
  have he := exactSide_real (vertex (triangleIndex i e)) (vertex (triangleIndex i (triangleNext e)))
    (vertex (triangleIndex j v))
  change side (realVertex (triangleIndex i e)) (realVertex (triangleIndex i (triangleNext e)))
    (realVertex (triangleIndex j v)) = _ at he
  refine ⟨?_,?_⟩
  · rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (nonpositive_real_sound _ hn) (by norm_num)
  · intro hzero
    have hq : Quad3.eval (exactSide (vertex (triangleIndex i e)) (vertex (triangleIndex i (triangleNext e)))
        (vertex (triangleIndex j v))) = 0 := by rw [he] at hzero; linarith
    have hi : realVertex (triangleIndex j v) ∈ sourceVertices i := by
      rcases hz (nonpositive_quad_zero _ hn hq) with hv | hv
      · exact ⟨e,congrArg realVertex hv.symm⟩
      · exact ⟨triangleNext e,congrArg realVertex hv.symm⟩
    exact ⟨hi,⟨v,rfl⟩⟩

theorem supported_sourceTriangle_intersection (i j : Fin 12) (e : Fin 3)
    (h : CommonFaceSupport i j e) (x : RealPoint)
    (hi : x ∈ sourceTriangle i) (hj : x ∈ sourceTriangle j) :
    x ∈ convexHull ℝ (sourceVertices i ∩ sourceVertices j) := by
  have hnonneg := sourceTriangle_side_nonnegative i e x hi
  rw [sourceTriangle_eq_hull] at hj
  have hnonpos := side_nonpos_hull (realVertex (triangleIndex i e))
    (realVertex (triangleIndex i (triangleNext e))) (sourceVertices j)
    (fun y hy => (commonFaceSupport_real i j e h y hy).1) x hj
  exact convexHull_nonpositive_zero_face (realVertex (triangleIndex i e))
    (realVertex (triangleIndex i (triangleNext e))) (sourceVertices j) (sourceVertices i ∩ sourceVertices j)
    (fun y hy => (commonFaceSupport_real i j e h y hy).1)
    (fun y hy => (commonFaceSupport_real i j e h y hy).2) x hj (le_antisymm hnonpos hnonneg)

theorem sourceTriangles_common_face (i j : Fin 12) :
    sourceTriangle i ∩ sourceTriangle j = convexHull ℝ (sourceVertices i ∩ sourceVertices j) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hi,hj⟩
    by_cases hij : i=j
    · subst j
      rw [Set.inter_self,←sourceTriangle_eq_hull]
      exact hi
    rcases all_common_faces i j hij with ⟨e,he⟩ | ⟨e,he⟩
    · exact supported_sourceTriangle_intersection i j e he x hi hj
    · rw [Set.inter_comm]
      exact supported_sourceTriangle_intersection j i e he x hj hi
  · intro x hx
    constructor
    · rw [sourceTriangle_eq_hull]
      exact convexHull_mono Set.inter_subset_left hx
    · rw [sourceTriangle_eq_hull]
      exact convexHull_mono Set.inter_subset_right hx

end
end SpectreGeometry.Deformation
