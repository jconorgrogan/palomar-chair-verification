module

public import SpectreGeometry.DeformationTriangulationReal

@[expose] public section


/-! The exact twelve-triangle carrier equality, by eleven verified ear
flips followed by the final three-fan collapse. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

theorem polygonBody_radial_union : polygonBody =
    radialTriangle 0 1 ∪ radialTriangle 1 2 ∪ radialTriangle 2 3 ∪ radialTriangle 3 4 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 ∪ radialTriangle 13 0 := by
  ext x
  simp only [polygonBody,mem_iUnion,triangleBody_cyclic,mem_union,
    Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  all_goals tauto

theorem sourceTriangle_union_explicit : (⋃ i : Fin 12, sourceTriangle i) =
    sourceTriangle 0 ∪ sourceTriangle 1 ∪ sourceTriangle 2 ∪ sourceTriangle 3 ∪ sourceTriangle 4 ∪ sourceTriangle 5 ∪ sourceTriangle 6 ∪ sourceTriangle 7 ∪ sourceTriangle 8 ∪ sourceTriangle 9 ∪ sourceTriangle 10 ∪ sourceTriangle 11 := by
  ext x
  simp only [mem_iUnion,mem_union,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  all_goals tauto

theorem explicit_ear_flip_0 : radialTriangle 13 0 ∪ radialTriangle 0 1 =
    radialTriangle 13 1 ∪ sourceTriangle 11 := by
  have h := ear_flip 0
  change radialTriangle 13 0 ∪ radialTriangle 0 1 = radialTriangle 13 1 ∪ earTriangle 0 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 13,realVertex 0,realVertex 1} =
    convexHull ℝ {realVertex 0,realVertex 1,realVertex 13}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_1 : radialTriangle 2 3 ∪ radialTriangle 3 4 =
    radialTriangle 2 4 ∪ sourceTriangle 0 := by
  have h := ear_flip 1
  change radialTriangle 2 3 ∪ radialTriangle 3 4 = radialTriangle 2 4 ∪ earTriangle 1 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 2,realVertex 3,realVertex 4} =
    convexHull ℝ {realVertex 2,realVertex 3,realVertex 4}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_2 : radialTriangle 1 2 ∪ radialTriangle 2 4 =
    radialTriangle 1 4 ∪ sourceTriangle 1 := by
  have h := ear_flip 2
  change radialTriangle 1 2 ∪ radialTriangle 2 4 = radialTriangle 1 4 ∪ earTriangle 2 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 1,realVertex 2,realVertex 4} =
    convexHull ℝ {realVertex 1,realVertex 2,realVertex 4}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_3 : radialTriangle 4 5 ∪ radialTriangle 5 6 =
    radialTriangle 4 6 ∪ sourceTriangle 2 := by
  have h := ear_flip 3
  change radialTriangle 4 5 ∪ radialTriangle 5 6 = radialTriangle 4 6 ∪ earTriangle 3 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 4,realVertex 5,realVertex 6} =
    convexHull ℝ {realVertex 4,realVertex 5,realVertex 6}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_4 : radialTriangle 6 7 ∪ radialTriangle 7 8 =
    radialTriangle 6 8 ∪ sourceTriangle 3 := by
  have h := ear_flip 4
  change radialTriangle 6 7 ∪ radialTriangle 7 8 = radialTriangle 6 8 ∪ earTriangle 4 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 6,realVertex 7,realVertex 8} =
    convexHull ℝ {realVertex 6,realVertex 7,realVertex 8}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_5 : radialTriangle 4 6 ∪ radialTriangle 6 8 =
    radialTriangle 4 8 ∪ sourceTriangle 4 := by
  have h := ear_flip 5
  change radialTriangle 4 6 ∪ radialTriangle 6 8 = radialTriangle 4 8 ∪ earTriangle 5 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 4,realVertex 6,realVertex 8} =
    convexHull ℝ {realVertex 4,realVertex 6,realVertex 8}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_6 : radialTriangle 1 4 ∪ radialTriangle 4 8 =
    radialTriangle 1 8 ∪ sourceTriangle 5 := by
  have h := ear_flip 6
  change radialTriangle 1 4 ∪ radialTriangle 4 8 = radialTriangle 1 8 ∪ earTriangle 6 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 1,realVertex 4,realVertex 8} =
    convexHull ℝ {realVertex 1,realVertex 4,realVertex 8}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_7 : radialTriangle 8 9 ∪ radialTriangle 9 10 =
    radialTriangle 8 10 ∪ sourceTriangle 6 := by
  have h := ear_flip 7
  change radialTriangle 8 9 ∪ radialTriangle 9 10 = radialTriangle 8 10 ∪ earTriangle 7 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 8,realVertex 9,realVertex 10} =
    convexHull ℝ {realVertex 8,realVertex 9,realVertex 10}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_8 : radialTriangle 10 11 ∪ radialTriangle 11 12 =
    radialTriangle 10 12 ∪ sourceTriangle 7 := by
  have h := ear_flip 8
  change radialTriangle 10 11 ∪ radialTriangle 11 12 = radialTriangle 10 12 ∪ earTriangle 8 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 10,realVertex 11,realVertex 12} =
    convexHull ℝ {realVertex 10,realVertex 11,realVertex 12}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_9 : radialTriangle 10 12 ∪ radialTriangle 12 13 =
    radialTriangle 10 13 ∪ sourceTriangle 8 := by
  have h := ear_flip 9
  change radialTriangle 10 12 ∪ radialTriangle 12 13 = radialTriangle 10 13 ∪ earTriangle 9 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 10,realVertex 12,realVertex 13} =
    convexHull ℝ {realVertex 10,realVertex 12,realVertex 13}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem explicit_ear_flip_10 : radialTriangle 8 10 ∪ radialTriangle 10 13 =
    radialTriangle 8 13 ∪ sourceTriangle 9 := by
  have h := ear_flip 10
  change radialTriangle 8 10 ∪ radialTriangle 10 13 = radialTriangle 8 13 ∪ earTriangle 10 at h
  rw [h]
  congr 1
  all_goals unfold earTriangle sourceTriangle
  all_goals change convexHull ℝ {realVertex 8,realVertex 10,realVertex 13} =
    convexHull ℝ {realVertex 8,realVertex 10,realVertex 13}
  all_goals congr 1
  all_goals ext x
  all_goals simp only [mem_insert_iff,mem_singleton_iff]
  all_goals tauto

theorem sourceTriangles_cover_polygonBody : polygonBody = ⋃ i : Fin 12, sourceTriangle i := by
  rw [sourceTriangle_union_explicit]
  calc
    polygonBody = radialTriangle 0 1 ∪ radialTriangle 1 2 ∪ radialTriangle 2 3 ∪ radialTriangle 3 4 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 ∪ radialTriangle 13 0 := polygonBody_radial_union
    _ = (radialTriangle 13 0 ∪ radialTriangle 0 1) ∪ radialTriangle 1 2 ∪ radialTriangle 2 3 ∪ radialTriangle 3 4 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 13 1 ∪ sourceTriangle 11) ∪ radialTriangle 1 2 ∪ radialTriangle 2 3 ∪ radialTriangle 3 4 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_0]
    _ = (radialTriangle 2 3 ∪ radialTriangle 3 4) ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 1 2 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 2 4 ∪ sourceTriangle 0) ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 1 2 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_1]
    _ = (radialTriangle 1 2 ∪ radialTriangle 2 4) ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 1 4 ∪ sourceTriangle 1) ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 4 5 ∪ radialTriangle 5 6 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_2]
    _ = (radialTriangle 4 5 ∪ radialTriangle 5 6) ∪ radialTriangle 1 4 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 4 6 ∪ sourceTriangle 2) ∪ radialTriangle 1 4 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 6 7 ∪ radialTriangle 7 8 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_3]
    _ = (radialTriangle 6 7 ∪ radialTriangle 7 8) ∪ radialTriangle 4 6 ∪ sourceTriangle 2 ∪ radialTriangle 1 4 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 6 8 ∪ sourceTriangle 3) ∪ radialTriangle 4 6 ∪ sourceTriangle 2 ∪ radialTriangle 1 4 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_4]
    _ = (radialTriangle 4 6 ∪ radialTriangle 6 8) ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ radialTriangle 1 4 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 4 8 ∪ sourceTriangle 4) ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ radialTriangle 1 4 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_5]
    _ = (radialTriangle 1 4 ∪ radialTriangle 4 8) ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 1 8 ∪ sourceTriangle 5) ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 8 9 ∪ radialTriangle 9 10 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_6]
    _ = (radialTriangle 8 9 ∪ radialTriangle 9 10) ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 8 10 ∪ sourceTriangle 6) ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 10 11 ∪ radialTriangle 11 12 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_7]
    _ = (radialTriangle 10 11 ∪ radialTriangle 11 12) ∪ radialTriangle 8 10 ∪ sourceTriangle 6 ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 12 13 := by ac_rfl
    _ = (radialTriangle 10 12 ∪ sourceTriangle 7) ∪ radialTriangle 8 10 ∪ sourceTriangle 6 ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 ∪ radialTriangle 12 13 := by rw [explicit_ear_flip_8]
    _ = (radialTriangle 10 12 ∪ radialTriangle 12 13) ∪ sourceTriangle 7 ∪ radialTriangle 8 10 ∪ sourceTriangle 6 ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 := by ac_rfl
    _ = (radialTriangle 10 13 ∪ sourceTriangle 8) ∪ sourceTriangle 7 ∪ radialTriangle 8 10 ∪ sourceTriangle 6 ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 := by rw [explicit_ear_flip_9]
    _ = (radialTriangle 8 10 ∪ radialTriangle 10 13) ∪ sourceTriangle 8 ∪ sourceTriangle 7 ∪ sourceTriangle 6 ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 := by ac_rfl
    _ = (radialTriangle 8 13 ∪ sourceTriangle 9) ∪ sourceTriangle 8 ∪ sourceTriangle 7 ∪ sourceTriangle 6 ∪ radialTriangle 1 8 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ radialTriangle 13 1 ∪ sourceTriangle 11 := by rw [explicit_ear_flip_10]
    _ = (radialTriangle 1 8 ∪ radialTriangle 8 13 ∪ radialTriangle 13 1) ∪ sourceTriangle 9 ∪ sourceTriangle 8 ∪ sourceTriangle 7 ∪ sourceTriangle 6 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ sourceTriangle 11 := by ac_rfl
    _ = sourceTriangle 10 ∪ sourceTriangle 9 ∪ sourceTriangle 8 ∪ sourceTriangle 7 ∪ sourceTriangle 6 ∪ sourceTriangle 5 ∪ sourceTriangle 4 ∪ sourceTriangle 3 ∪ sourceTriangle 2 ∪ sourceTriangle 1 ∪ sourceTriangle 0 ∪ sourceTriangle 11 := by rw [final_fan_collapse]
    _ = sourceTriangle 0 ∪ sourceTriangle 1 ∪ sourceTriangle 2 ∪ sourceTriangle 3 ∪ sourceTriangle 4 ∪ sourceTriangle 5 ∪ sourceTriangle 6 ∪ sourceTriangle 7 ∪ sourceTriangle 8 ∪ sourceTriangle 9 ∪ sourceTriangle 10 ∪ sourceTriangle 11 := by ac_rfl

end
end SpectreGeometry.Deformation
