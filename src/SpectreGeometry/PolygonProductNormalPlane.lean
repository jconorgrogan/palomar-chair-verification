module

public import SpectreGeometry.NormalPlaneRankObstruction
public import SpectreGeometry.PolygonProductBoundaryNormals

@[expose] public section


/-! An actual nonstraight corner in one polygon factor excludes every
boundary normal from the orthogonal factor from the same two-dimensional
root-normal plane. All containment assumptions are explicit. -/
namespace SpectreGeometry
noncomputable section

theorem native_left_corner_excludes_right_normal
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (i j : Fin 14) (hi : i ≠ 10)
    (hp : nativeLeftNormal (previous i) ∈ Set.range L)
    (hn : nativeLeftNormal i ∈ Set.range L) :
    nativeRightNormal j ∉ Set.range L := by
  intro hj
  exact normal_plane_rank_obstruction L
    (native_left_corner_normals_independent i hi) (nativeRightNormal_ne_zero j)
    (native_product_normals_orthogonal (previous i) j)
    (native_product_normals_orthogonal i j) hp hn hj

theorem native_right_corner_excludes_left_normal
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (i j : Fin 14) (hi : i ≠ 10)
    (hp : nativeRightNormal (previous i) ∈ Set.range L)
    (hn : nativeRightNormal i ∈ Set.range L) :
    nativeLeftNormal j ∉ Set.range L := by
  intro hj
  apply normal_plane_rank_obstruction L
    (native_right_corner_normals_independent i hi) (nativeLeftNormal_ne_zero j)
    (ha := hp) (hb := hn) (hc := hj)
  · rw [real_inner_comm]
    exact native_product_normals_orthogonal j (previous i)
  · rw [real_inner_comm]
    exact native_product_normals_orthogonal j i

end
end SpectreGeometry
