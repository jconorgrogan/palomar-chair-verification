module

public import SpectreGeometry.DeformationTriangulationData
public import SpectreGeometry.TriangleFanCollapse
public import SpectreGeometry.FanRealGeometry

@[expose] public section


namespace SpectreGeometry.Deformation
noncomputable section
open Set

def sourceTriangle (i : Fin 12) : Set RealPoint :=
  let t := triangle i
  convexHull ℝ {realVertex t.1,realVertex t.2.1,realVertex t.2.2}

def radialTriangle (a b : Fin 14) : Set RealPoint :=
  convexHull ℝ {realFanCenter,realVertex a,realVertex b}

def earTriangle (i : Fin 11) : Set RealPoint :=
  let t := ear i
  convexHull ℝ {realVertex t.1,realVertex t.2.1,realVertex t.2.2}

theorem exactSide_real (a b c : ExactPoint) :
    side (realize a) (realize b) (realize c) = Quad3.eval (exactSide a b c)/4 := by
  unfold side exactSide
  rw [←realize_sub,←realize_sub,realize_det]

theorem exactSide_positive_real (a b c : ExactPoint) (h : Quad3.positive (exactSide a b c)) :
    0 < side (realize a) (realize b) (realize c) := by
  rw [exactSide_real]
  exact div_pos (Quad3.positive_sound _ h) (by norm_num)

theorem sourceTriangle_positive (i : Fin 12) :
    0 < side (realVertex (triangle i).1) (realVertex (triangle i).2.1) (realVertex (triangle i).2.2) := by
  exact exactSide_positive_real _ _ _ (all_triangle_orientations i)

theorem ear_flip (i : Fin 11) :
    radialTriangle (ear i).1 (ear i).2.1 ∪ radialTriangle (ear i).2.1 (ear i).2.2 =
      radialTriangle (ear i).1 (ear i).2.2 ∪ earTriangle i := by
  obtain ⟨h1,h2,h3,h4⟩ := all_ear_certificates i
  exact convex_quad_diagonal_flip realFanCenter (realVertex (ear i).1)
    (realVertex (ear i).2.1) (realVertex (ear i).2.2)
    (exactSide_positive_real _ _ _ h1) (exactSide_positive_real _ _ _ h2)
    (exactSide_positive_real _ _ _ h3) (exactSide_positive_real _ _ _ h4)

theorem final_fan_collapse :
    radialTriangle 1 8 ∪ radialTriangle 8 13 ∪ radialTriangle 13 1 = sourceTriangle 10 := by
  exact triangle_center_fan realFanCenter (realVertex 1) (realVertex 8) (realVertex 13)
    (exactSide_positive_real _ _ _ final_center_inside.1)
    (exactSide_positive_real _ _ _ final_center_inside.2.1)
    (exactSide_positive_real _ _ _ final_center_inside.2.2)

end
end SpectreGeometry.Deformation
