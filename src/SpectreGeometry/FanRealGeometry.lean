module

public import SpectreGeometry.TriangleGeometry

@[expose] public section


/-! The exact fan certificates realized as closed, regular real triangles. -/
namespace SpectreGeometry
noncomputable section
open Set

def realFanCenter : RealPoint := realize fanCenter

theorem triangleBody_cyclic (i : Fin 14) :
    triangleBody i = convexHull ℝ {realFanCenter,realVertex i,realVertex (next i)} := by
  unfold triangleBody realFanCenter
  congr 1
  ext x
  simp only [mem_insert_iff,mem_singleton_iff]
  tauto

theorem fan_real_positive (i : Fin 14) :
    0 < side (realVertex i) (realVertex (next i)) realFanCenter := by
  have hp := Quad3.positive_sound _ (fan_center_strictly_left i)
  have he : side (realVertex i) (realVertex (next i)) realFanCenter =
      Quad3.eval (ExactPoint.det (edge i) (ExactPoint.sub fanCenter (vertex i)))/4 := by
    unfold side realVertex realFanCenter
    rw [←realize_sub,←realize_sub,realize_det]
    rfl
  rw [he]
  positivity

theorem fan_real_positive_cyclic (i : Fin 14) :
    0 < side realFanCenter (realVertex i) (realVertex (next i)) := by
  rw [side_cyclic]
  exact fan_real_positive i

def radialSide (i : Fin 14) (x : RealPoint) : ℝ := side realFanCenter (realVertex i) x

theorem triangleBody_mem_iff (i : Fin 14) (x : RealPoint) :
    x ∈ triangleBody i ↔ 0 ≤ radialSide i x ∧
      0 ≤ side (realVertex i) (realVertex (next i)) x ∧ radialSide (next i) x ≤ 0 := by
  rw [triangleBody_cyclic,triangle_mem_iff _ _ _ _ (fan_real_positive_cyclic i)]
  unfold radialSide
  rw [side_reverse realFanCenter (realVertex (next i)) x]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h1,h2,by linarith⟩

theorem triangleBody_interior_iff (i : Fin 14) (x : RealPoint) :
    x ∈ interior (triangleBody i) ↔ 0 < radialSide i x ∧
      0 < side (realVertex i) (realVertex (next i)) x ∧ radialSide (next i) x < 0 := by
  rw [triangleBody_cyclic,triangle_interior_iff _ _ _ _ (fan_real_positive_cyclic i)]
  unfold radialSide
  rw [side_reverse realFanCenter (realVertex (next i)) x]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h1,h2,by linarith⟩

theorem triangleBody_interior_nonempty (i : Fin 14) : (interior (triangleBody i)).Nonempty := by
  rw [triangleBody_cyclic]
  exact triangle_interior_nonempty _ _ _ (fan_real_positive_cyclic i)

theorem triangleBody_closure_interior (i : Fin 14) : closure (interior (triangleBody i)) = triangleBody i := by
  have h := (convex_convexHull ℝ {realVertex i,realVertex (next i),realize fanCenter}).closure_interior_eq_closure_of_nonempty_interior
    (triangleBody_interior_nonempty i)
  exact h.trans (triangleBody_compact i).isClosed.closure_eq

theorem polygonBody_closure_interior : closure (interior polygonBody) = polygonBody := by
  apply Subset.antisymm
  · exact polygonBody_compact.isClosed.closure_interior_subset
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.1 hx
    have hh : triangleBody i ⊆ polygonBody := subset_iUnion _ i
    rw [←triangleBody_closure_interior i] at hi
    exact closure_mono (interior_mono hh) hi

end
end SpectreGeometry
