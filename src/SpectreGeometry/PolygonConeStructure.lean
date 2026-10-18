module

public import SpectreGeometry.PolygonLocalConeGerms

@[expose] public section


/-! Closedness and genuine positive homogeneity of the literal polygon cones.
These do not identify their angular measure. -/
namespace SpectreGeometry
noncomputable section
open Set

private theorem det_smul_right (a v : RealPoint) (t : ℝ) :
    RealPoint.det a (t • v) = t * RealPoint.det a v := by
  simp only [RealPoint.det,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

private theorem positive_mul_nonpos_iff {t a : ℝ} (ht : 0 < t) :
    t*a ≤ 0 ↔ a ≤ 0 := by
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos ht.le h

theorem polygonVertexCone_pos_smul_iff (i : Fin 14) (v : RealPoint)
    (t : ℝ) (ht : 0 < t) : t • v ∈ polygonVertexCone i ↔ v ∈ polygonVertexCone i := by
  simp only [polygonVertexCone,Set.mem_setOf_eq,det_smul_right,
    mul_nonneg_iff_of_pos_left ht,positive_mul_nonpos_iff ht]

theorem polygonBoundaryCone_pos_smul_iff (b : BoundarySlot) (v : RealPoint)
    (t : ℝ) (ht : 0 < t) : t • v ∈ polygonBoundaryCone b ↔ v ∈ polygonBoundaryCone b := by
  cases b with
  | inl i => exact polygonVertexCone_pos_smul_iff i v t ht
  | inr i =>
      simp only [polygonBoundaryCone,Set.mem_setOf_eq,det_smul_right,
        mul_nonneg_iff_of_pos_left ht]

theorem polygonBoundaryCone_zero (b : BoundarySlot) : (0 : RealPoint) ∈ polygonBoundaryCone b := by
  cases b <;> simp [polygonBoundaryCone,polygonVertexCone,RealPoint.det]

private theorem continuous_det_right (a : RealPoint) : Continuous (RealPoint.det a) := by
  unfold RealPoint.det
  fun_prop

theorem polygonVertexCone_isClosed (i : Fin 14) : IsClosed (polygonVertexCone i) := by
  exact ((isClosed_le continuous_const (continuous_det_right (realEdge (previous i)))).inter
    (isClosed_le (continuous_det_right (RealPoint.sub (realVertex i) realFanCenter)) continuous_const)).union
    ((isClosed_le continuous_const (continuous_det_right (RealPoint.sub (realVertex i) realFanCenter))).inter
      (isClosed_le continuous_const (continuous_det_right (realEdge i))))

theorem polygonBoundaryCone_isClosed (b : BoundarySlot) : IsClosed (polygonBoundaryCone b) := by
  cases b with
  | inl i => exact polygonVertexCone_isClosed i
  | inr i => exact isClosed_le continuous_const (continuous_det_right (realEdge i))

end
end SpectreGeometry
