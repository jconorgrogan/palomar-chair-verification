module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import SpectreGeometry.ReverseClusterTriangulationRawBoundsData
public import SpectreGeometry.ReverseClusterTriangulationScaleReal

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

/-- A uniform coordinate bound for every point of the actual closed raw kites,
    independent of any finite mesh or assumed physical tiling. -/
theorem rawClusterBody_coordinates_bounded (k : Fin 9) (x : RealPoint)
    (hx : x ∈ rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k)) :
    -5 ≤ x.1 ∧ x.1 ≤ 11 ∧ -11 ≤ x.2 ∧ x.2 ≤ 7 := by
  obtain ⟨c,hc,hxc⟩ := by simpa only [rawClusterBody,mem_iUnion] using hx
  have hcell := List.all_eq_true.mp (all_raw_cluster_boxes_checked k) c hc
  have h := verticesSatisfyB_sound (cellVertices c) rawClusterBoxFacets hcell x hxc
  have hh : 0 ≤ x.1+5 ∧ 0 ≤ -x.1+11 ∧ 0 ≤ x.2+11 ∧ 0 ≤ -x.2+7 := by
    simpa [rawClusterBoxFacets,Satisfies,evalConstraint] using h
  obtain ⟨h1,h2,h3,h4⟩ := hh
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- Product-sup-norm bound used by the global properness estimate. -/
theorem rawClusterBody_norm_le (k : Fin 9) (x : RealPoint)
    (hx : x ∈ rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k)) :
    ‖x‖ ≤ 11 := by
  obtain ⟨h1,h2,h3,h4⟩ := rawClusterBody_coordinates_bounded k x hx
  rw [Prod.norm_def,max_le_iff,Real.norm_eq_abs,Real.norm_eq_abs]
  exact ⟨abs_le.mpr ⟨by linarith,h2⟩,abs_le.mpr ⟨h3,by linarith⟩⟩

end
end SpectreGeometry.ReverseClusterTriangulation
