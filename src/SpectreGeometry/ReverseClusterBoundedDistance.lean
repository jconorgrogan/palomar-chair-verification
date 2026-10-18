module

public import SpectreGeometry.ReverseMarkedAnchor
public import SpectreGeometry.ReverseAnchorBounds
public import SpectreGeometry.ReverseSourceHexCover
public import SpectreGeometry.ReverseClusterTriangulationRawBoundsReal
public import SpectreGeometry.GridAffineGeometry

@[expose] public section


/-! Concrete bounded-distance control for any actual marked-cluster carrier
realization. This module uses the ordinary product metric solely for properness;
it is separate from the Euclidean Hilbert norm in inverse deformation. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open SpectreFinite SpectreFinite.HexSearch SpectreClusters.ReverseExistence
open SpectreGeometry.ReverseClusterTriangulation

theorem sourceHex_dist_center_le (c : ℤ×ℤ) (p : RealPoint) (hp : p ∈ sourceHexCarrier c) :
    dist p (integerPoint c) ≤ 1 := by
  change sourceHexOffset (p.1-c.1) (p.2-c.2) at hp
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hp
  rw [dist_eq_norm,Prod.norm_def,max_le_iff]
  simp only [Prod.fst_sub,Prod.snd_sub,integerPoint,Real.norm_eq_abs]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem gridRotation_norm_le (r : SpectreClusters.Turn) (p : RealPoint) :
    ‖gridRotation r p‖ ≤ 2*‖p‖ := by
  have hx : |p.1| ≤ ‖p‖ := by rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]; exact le_max_left _ _
  have hy : |p.2| ≤ ‖p‖ := by rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]; exact le_max_right _ _
  obtain ⟨hx1,hx2⟩ := abs_le.mp hx
  obtain ⟨hy1,hy2⟩ := abs_le.mp hy
  have hn := norm_nonneg p
  rw [Prod.norm_def,max_le_iff]
  fin_cases r <;> simp only [gridRotation,Real.norm_eq_abs] <;>
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith

/-- Explicit carrier inclusion suffices; no tiling or global injectivity is
assumed in this quantitative estimate. -/
theorem markedCluster_distance_to_anchor (f : Position → State) (hf : GloballyLegal f)
    (F : RealPoint → RealPoint)
    (hcarrier : ∀ c p, p ∈ sourceHexCarrier c →
      ∃ q ∈ rawClusterBody (clusterOfMark (f c).1),
        F p = markedAnchor f hf c+gridRotation (f c).2 q)
    (p : RealPoint) : dist (F p) (markedAnchorHomeomorph f hf p) ≤ 54 := by
  have hnear : ∀ x, ∃ n m : ℤ, dist x ((n:ℝ),(m:ℝ)) ≤ 1 ∧
      dist (F x) (markedAnchor f hf (n,m)) ≤ 22 := by
    intro x
    obtain ⟨c,hc⟩ := sourceHex_plane_cover x
    obtain ⟨q,hq,hF⟩ := hcarrier c x hc
    refine ⟨c.1,c.2,sourceHex_dist_center_le c x hc,?_⟩
    rw [hF,dist_eq_norm,add_sub_cancel_left]
    exact (gridRotation_norm_le (f c).2 q).trans (by
      have hh := rawClusterBody_norm_le (f c).1 q hq
      linarith)
  have h := distance_from_anchorInterpolation (markedAnchor f hf)
    (markedAnchor_residualBounds f hf) F 22 1 hnear p
  simpa only [markedAnchorHomeomorph,anchorHomeomorph_apply,show (22:ℝ)+32*1=54 by norm_num] using h

end
end SpectreGeometry.ReverseExistence
