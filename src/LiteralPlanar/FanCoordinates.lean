module

public import LiteralPlanar.FanDomain
public import SpectreGeometry.PolygonBoundary
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! Exact affine inverse coordinates and vanishing on internal fan overlaps.
These are constructive compatibility facts for the forward polynomial map. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry

def affineFan (i : Fin 14) (a b : ℝ) : RealPoint :=
  center + a • radial i + b • radial (next i)

theorem affineFan_reconstruct (i : Fin 14) (p : RealPoint) :
    affineFan i (alpha i p) (beta i p) = p := by
  apply Prod.ext <;>
    simp only [affineFan, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  all_goals
    simp only [alpha, beta]
    field_simp [(areaDeterminant_pos i).ne']
    simp only [areaDeterminant, radial, RealPoint.det, Prod.fst_sub, Prod.snd_sub]
    ring

theorem alpha_affineFan (i : Fin 14) (a b : ℝ) :
    alpha i (affineFan i a b) = a := by
  unfold alpha
  apply (div_eq_iff (areaDeterminant_pos i).ne').mpr
  simp only [affineFan, areaDeterminant, radial, RealPoint.det,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem beta_affineFan (i : Fin 14) (a b : ℝ) :
    beta i (affineFan i a b) = b := by
  unfold beta
  apply (div_eq_iff (areaDeterminant_pos i).ne').mpr
  simp only [affineFan, areaDeterminant, radial, RealPoint.det,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem affineFan_outer (i : Fin 14) (a b : ℝ) (hab : a + b = 1) :
    affineFan i a b = interpolate (realVertex i) (realVertex (next i)) b := by
  have ha : a = 1 - b := by linarith
  rw [ha]
  apply Prod.ext <;>
    simp only [affineFan, radial, interpolate, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem outer_coordinate_reconstruct (i : Fin 14) (p : RealPoint)
    (hp : alpha i p + beta i p = 1) :
    p = interpolate (realVertex i) (realVertex (next i)) (beta i p) := by
  rw [←affineFan_outer i (alpha i p) (beta i p) hp, affineFan_reconstruct]

/-- Distinct original fan triangles meet only where each fan's polynomial
normal displacement is zero. The outer-open-edge exclusion is used explicitly. -/
theorem fanHeight_zero_on_overlap (i j : Fin 14) (hij : i ≠ j)
    (p : RealPoint) (hi : p ∈ triangleBody i) (hj : p ∈ triangleBody j) :
    Quintic.fanHeight Quintic.amplitude (alpha i p) (beta i p) = 0 := by
  have hc : p ∈ sourceDomain i := by rwa [sourceDomain_eq_triangleBody]
  obtain ⟨ha,hb,hs⟩ := hc
  by_cases hza : alpha i p = 0
  · simp [hza]
  by_cases hzb : beta i p = 0
  · simp [hzb]
  have hpa : 0 < alpha i p := lt_of_le_of_ne ha (Ne.symm hza)
  have hpb : 0 < beta i p := lt_of_le_of_ne hb (Ne.symm hzb)
  have hd := areaDeterminant_pos i
  have hsum : alpha i p + beta i p = 1 := by
    by_contra hn
    have hlt : alpha i p + beta i p < 1 := lt_of_le_of_ne hs hn
    have hpint : p ∈ interior (triangleBody i) := by
      rw [triangleBody_interior_iff, radialSide_beta, outerSide_barycentric,
        radialSide_next_alpha]
      exact ⟨mul_pos hd hpb, mul_pos hd (by linarith), by linarith [mul_pos hd hpa]⟩
    exact Set.disjoint_left.mp (triangleBody_interior_disjoint_body i j hij) hpint hj
  have he := outer_coordinate_reconstruct i p hsum
  rw [he] at hj
  exact False.elim (outer_open_edge_not_other_triangle i j hij (beta i p)
    hpb (by linarith) hj)

end
end LiteralPlanar.FanBounds
