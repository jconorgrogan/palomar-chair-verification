module

public import SpectreGeometry.CornerSectorReal
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section


/-! The genuine adjacent boundary edges and their Euclidean normals are
independent at each nonstraight native polygon vertex. At the retained
midpoint 10 the two edges, hence the two normals, agree. The auxiliary radial
fan separator is not included among the boundary normals. No angular measure
or product-rank conclusion is asserted in this module. -/
namespace SpectreGeometry
noncomputable section

private theorem corner_edge_det_signs : ∀ i : Fin 14,
    Quad3.signCertified (ExactPoint.det (edge (previous i)) (edge i)) := by decide

private theorem corner_edge_det_zero_iff : ∀ i : Fin 14,
    ExactPoint.det (edge (previous i)) (edge i) = (0,0) ↔ i = 10 := by decide

/-- Every actual nonstraight native corner has two independent incident
edge directions, as witnessed by its nonzero real determinant. -/
theorem real_corner_det_ne_zero (i : Fin 14) (hi : i ≠ 10) :
    RealPoint.det (realEdge (previous i)) (realEdge i) ≠ 0 := by
  rw [← realize_edge, ← realize_edge, realize_det]
  apply div_ne_zero
  · apply certified_eval_ne_zero _ (corner_edge_det_signs i)
    intro hz
    exact hi ((corner_edge_det_zero_iff i).mp hz)
  · norm_num

/-- The retained midpoint is genuinely straight: its two directed unit
boundary edges agree, rather than merely being parallel. -/
theorem real_midpoint_edges_eq : realEdge (previous 10) = realEdge 10 := by
  have h : edge (previous 10) = edge 10 := by decide
  rw [← realize_edge, ← realize_edge, h]

/-- The inward Euclidean normal to an oriented native boundary edge. -/
def nativeEdgeNormal (i : Fin 14) : RealPoint :=
  (-(realEdge i).2, (realEdge i).1)

theorem native_edge_normal_ne_zero (i : Fin 14) : nativeEdgeNormal i ≠ 0 := by
  intro hn
  have hx : (realEdge i).1 = 0 := by
    simpa only [nativeEdgeNormal, Prod.snd_zero] using congrArg Prod.snd hn
  have hy : (realEdge i).2 = 0 := by
    simpa only [nativeEdgeNormal, Prod.fst_zero, neg_eq_zero] using congrArg Prod.fst hn
  have hu := real_edges_unit_squared i
  simp only [RealPoint.dot, hx, hy, mul_zero, zero_add] at hu
  norm_num at hu

private theorem native_normal_det (i j : Fin 14) :
    RealPoint.det (nativeEdgeNormal i) (nativeEdgeNormal j) =
      RealPoint.det (realEdge i) (realEdge j) := by
  simp only [nativeEdgeNormal, RealPoint.det]
  ring

/-- Only the normals to the two actual incident boundary edges enter this
independence statement; the fan's radial separator is absent. -/
theorem native_corner_normals_independent (i : Fin 14) (hi : i ≠ 10) :
    LinearIndependent ℝ ![nativeEdgeNormal (previous i), nativeEdgeNormal i] := by
  apply linearIndependent_fin2.mpr
  change nativeEdgeNormal i ≠ 0 ∧
    ∀ a : ℝ, a • nativeEdgeNormal i ≠ nativeEdgeNormal (previous i)
  refine ⟨native_edge_normal_ne_zero i, ?_⟩
  intro a ha
  apply real_corner_det_ne_zero i hi
  rw [← native_normal_det, ← ha]
  simp only [RealPoint.det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem native_midpoint_normals_eq : nativeEdgeNormal (previous 10) = nativeEdgeNormal 10 := by
  simp only [nativeEdgeNormal, real_midpoint_edges_eq]

end
end SpectreGeometry
