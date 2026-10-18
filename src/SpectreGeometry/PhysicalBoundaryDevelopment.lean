module

public import SpectreGeometry.PhysicalEdgeOrientation

@[expose] public section


/-! Any single-valued assignment on actual vertices extends consistently
by affine interpolation across all shared physical boundary edges. This
uses the derived whole-edge registration and excludes T-junctions. -/
namespace SpectreGeometry
noncomputable section

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)

include hdirect hdisjoint hcover in
theorem physical_edge_value_at_vertex (V : EPlane → RealPoint)
    (i j : ι) (hij : i ≠ j) (e v : Fin 14) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (he : f i (euclideanVertex e) =
      f j (euclideanCoordinates (interpolate (realVertex v) (realVertex (next v)) u))) :
    interpolate (V (f j (euclideanVertex v))) (V (f j (euclideanVertex (next v)))) u =
      V (f i (euclideanVertex e)) := by
  by_cases h0 : u = 0
  · subst u
    simp only [interpolate_zero,euclideanVertex] at he ⊢
    rw [he]
  by_cases h1 : u = 1
  · subst u
    simp only [interpolate_one,euclideanVertex] at he ⊢
    rw [he]
  exact False.elim (homochiral_no_vertex_in_unit_edge f hdirect hdisjoint hcover
    j i hij v e u (lt_of_le_of_ne hu (Ne.symm h0)) (lt_of_le_of_ne hu' h1) he.symm)

theorem physical_reversed_edge_parameters (i j : ι) (e v : Fin 14) (t u : ℝ)
    (he : f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)) =
      f j (euclideanCoordinates (interpolate (realVertex v) (realVertex (next v)) u)))
    (ha : f i (euclideanVertex e) = f j (euclideanVertex (next v)))
    (hb : f i (euclideanVertex (next e)) = f j (euclideanVertex v)) : t = 1-u := by
  rw [placed_edge_interpolate,placed_edge_interpolate,placedEdgeVector,placedEdgeVector,←ha,←hb] at he
  have hr : f i (euclideanVertex (next e))+u •
      (f i (euclideanVertex e)-f i (euclideanVertex (next e))) =
      f i (euclideanVertex e)+(1-u) •
        (f i (euclideanVertex (next e))-f i (euclideanVertex e)) := by
    simp only [sub_smul,one_smul,smul_sub]
    abel
  have hn : f i (euclideanVertex (next e))-f i (euclideanVertex e) ≠ 0 := by
    intro hz
    have hh := placedEdgeVector_unit (f i) e
    change ‖f i (euclideanVertex (next e))-f i (euclideanVertex e)‖ = 1 at hh
    rw [hz,norm_zero] at hh
    norm_num at hh
  exact (smul_left_injective ℝ hn) (add_left_cancel (he.trans hr))

include hdirect hdisjoint hcover in
/-- Closed-edge formulas agree at every common point, including endpoints. -/
theorem physical_shared_edge_values (V : EPlane → RealPoint)
    (i j : ι) (hij : i ≠ j) (e v : Fin 14) (t u : ℝ)
    (ht : 0 ≤ t) (ht' : t ≤ 1) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (he : f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)) =
      f j (euclideanCoordinates (interpolate (realVertex v) (realVertex (next v)) u))) :
    interpolate (V (f i (euclideanVertex e))) (V (f i (euclideanVertex (next e)))) t =
      interpolate (V (f j (euclideanVertex v))) (V (f j (euclideanVertex (next v)))) u := by
  by_cases ht0 : t = 0
  · subst t
    simp only [interpolate_zero,euclideanVertex] at he ⊢
    exact (physical_edge_value_at_vertex f hdirect hdisjoint hcover V i j hij e v u hu hu' he).symm
  by_cases ht1 : t = 1
  · subst t
    simp only [interpolate_one,euclideanVertex] at he ⊢
    exact (physical_edge_value_at_vertex f hdirect hdisjoint hcover V i j hij (next e) v u hu hu' he).symm
  by_cases hu0 : u = 0
  · subst u
    simp only [interpolate_zero,euclideanVertex] at he ⊢
    exact physical_edge_value_at_vertex f hdirect hdisjoint hcover V j i (Ne.symm hij) v e t ht ht' he.symm
  by_cases hu1 : u = 1
  · subst u
    simp only [interpolate_one,euclideanVertex] at he ⊢
    exact physical_edge_value_at_vertex f hdirect hdisjoint hcover V j i (Ne.symm hij) (next v) e t ht ht' he.symm
  have hts : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hts' : t < 1 := lt_of_le_of_ne ht' ht1
  have hus : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hus' : u < 1 := lt_of_le_of_ne hu' hu1
  obtain ⟨ha,hb⟩ := homochiral_contact_unit_edges_reversed f hdirect hdisjoint hcover i j
    (Ne.symm hij) e v t u hts hts' hus hus'
    (f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) rfl he
  have hp := physical_reversed_edge_parameters f i j e v t u he ha hb
  rw [←ha,←hb,hp]
  exact (interpolate_swap _ _ u).symm

end Tiling
end
end SpectreGeometry
