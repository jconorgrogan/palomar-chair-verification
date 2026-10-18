module

public import SpectreGeometry.ReverseFinitePLScaling
public import SpectreGeometry.ReverseClusterTriangulationBoundaryOwners
public import SpectreGeometry.ReverseSourceHexSegments
public import SpectreGeometry.ReverseUnitSubdivision

@[expose] public section


/-! Exact parametrization of the common-mesh source boundary. These identities
bind the rational source vertices to the literal six marked paths. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation
open SpectreGeometry.ReverseExistence

private theorem hexCorners_real (d : Fin 6) :
    (1/3:ℝ) • integerPoint (hexCorners.getD d.val (0,0)) = sourceHexCorner d := by
  fin_cases d <;> norm_num [hexCorners,integerPoint,sourceHexCorner]

private theorem nextCorner_index (d : Fin 6) :
    hexCorners.getD ((d.val+1)%6) (0,0) = hexCorners.getD (d+1).val (0,0) := by
  fin_cases d <;> rfl

theorem boundary_subdivision_pos (k : Fin 9) (d : Fin 6) :
    0 < (boundaryIndices k d).length-1 := by
  have h := (all_boundary_linear_checks k d).1
  omega

/-- Every source boundary vertex occurs at its prescribed uniform parameter. -/
theorem normalized_boundary_vertex (k : Fin 9) (d : Fin 6) (j : Nat)
    (hj : j < (boundaryIndices k d).length) :
    (1/(3*(sourceScale k:ℝ))) •
      integerPoint (sourceVertex k ((boundaryIndices k d).getD j 0)) =
      AffineMap.lineMap (sourceHexCorner d) (sourceHexCorner (d+1))
        ((j:ℝ)/((boundaryIndices k d).length-1)) := by
  have hlen := (all_boundary_linear_checks k d).1
  have hh := (all_boundary_linear_checks k d).2 j (List.mem_range.mpr hj)
  dsimp only at hh
  have hx : ((boundaryIndices k d).length-1:ℝ) *
      (sourceVertex k ((boundaryIndices k d).getD j 0)).1 =
      (sourceScale k:ℝ)*((((boundaryIndices k d).length:ℝ)-1-j)*
        (hexCorners.getD d.val (0,0)).1+(j:ℝ)*(hexCorners.getD ((d.val+1)%6) (0,0)).1) := by
    exact_mod_cast hh.1
  have hy : ((boundaryIndices k d).length-1:ℝ) *
      (sourceVertex k ((boundaryIndices k d).getD j 0)).2 =
      (sourceScale k:ℝ)*((((boundaryIndices k d).length:ℝ)-1-j)*
        (hexCorners.getD d.val (0,0)).2+(j:ℝ)*(hexCorners.getD ((d.val+1)%6) (0,0)).2) := by
    exact_mod_cast hh.2
  rw [nextCorner_index] at hx hy
  have hs : (sourceScale k:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast all_source_scales_positive k)
  have hn : ((boundaryIndices k d).length:ℝ)-1 ≠ 0 := by
    have h : (1:ℝ) < (boundaryIndices k d).length := by exact_mod_cast hlen
    linarith
  rw [←hexCorners_real d,←hexCorners_real (d+1)]
  apply Prod.ext
  · simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,Prod.fst_add,
      Prod.fst_sub,Prod.smul_fst,smul_eq_mul,integerPoint]
    field_simp
    nlinarith [hx]
  · simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,Prod.snd_add,
      Prod.snd_sub,Prod.smul_snd,smul_eq_mul,integerPoint]
    field_simp
    nlinarith [hy]

end
end SpectreGeometry.ReverseFinitePL
