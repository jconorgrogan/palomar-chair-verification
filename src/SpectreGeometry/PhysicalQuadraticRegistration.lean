module

public import SpectreGeometry.QuadraticPointReal
public import SpectreGeometry.WholeEdgeRegistration

@[expose] public section


/-! A genuine homochiral tiling has rational sqrt(3) vertex coordinates
relative to any one placed tile. This is propagated over the actual
nonvertex contact graph, not imposed on admissible translations. -/
namespace SpectreGeometry
noncomputable section

theorem relative_sourcePoint (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate k q))
    (q : RealPoint) :
    sourcePoint root (f (euclideanCoordinates q)) = sourcePoint root (f 0)+rotate k q := by
  have hh := congrArg coordinateLinearEquiv (hframe q)
  change coordinateLinearEquiv (coordinateLinearEquiv.symm
    (f.toRealLinearIsometryEquiv (euclideanCoordinates q))) =
    coordinateLinearEquiv (coordinateLinearEquiv.symm
      (root.toRealLinearIsometryEquiv (euclideanCoordinates (rotate k q)))) at hh
  simp only [coordinateLinearEquiv.apply_symm_apply] at hh
  have he := pullback_linear_part root (rotate k q)
  rw [←hh,IsometryEquiv.toRealLinearIsometryEquiv_apply,displacementPullback_sub] at he
  exact (eq_add_of_sub_eq he).trans (add_comm _ _)

theorem relative_vertex_mem_quadraticPlane (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate k q))
    (horigin : sourcePoint root (f 0) ∈ quadraticPlane) (e : Fin 14) :
    sourcePoint root (f (euclideanVertex e)) ∈ quadraticPlane := by
  change sourcePoint root (f (euclideanCoordinates (realVertex e))) ∈ quadraticPlane
  rw [relative_sourcePoint root f k hframe]
  exact quadraticPlane.add_mem horigin (rotate_mem_quadraticPlane k (realVertex_mem_quadraticPlane e))

theorem shared_vertex_origin_mem_quadraticPlane (root f g : EPlane ≃ᵢ EPlane)
    (a b : Fin 12)
    (ha : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate a q))
    (hb : ∀ q : RealPoint, coordinateAction g q = coordinateAction root (rotate b q))
    (hf : sourcePoint root (f 0) ∈ quadraticPlane) (e j : Fin 14)
    (hshared : f (euclideanVertex e) = g (euclideanVertex j)) :
    sourcePoint root (g 0) ∈ quadraticPlane := by
  have hv := relative_vertex_mem_quadraticPlane root f a ha hf e
  rw [hshared] at hv
  change sourcePoint root (g (euclideanCoordinates (realVertex j))) ∈ quadraticPlane at hv
  rw [relative_sourcePoint root g b hb] at hv
  have hm := quadraticPlane.sub_mem hv (rotate_mem_quadraticPlane b (realVertex_mem_quadraticPlane j))
  simpa only [add_sub_cancel_right] using hm

theorem nonvertex_contact_origin_mem_quadraticPlane {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root : ι) {i j : ι}
    (hi : sourcePoint (f root) (f i 0) ∈ quadraticPlane)
    (hc : CompactTilingIncidence.ContactAway
      (fun k => f k '' euclideanBody) (CompactTilingIncidence.placedVertices f) i j) :
    sourcePoint (f root) (f j 0) ∈ quadraticPlane := by
  by_cases hij : i = j
  · simpa only [←hij] using hi
  obtain ⟨x,hxi,hxj,hnot⟩ := hc
  have hvertex : ∀ k : ι, ∀ e : Fin 14, x ≠ f k (euclideanVertex e) := by
    intro k e he
    exact hnot ⟨(k,e),he.symm⟩
  obtain ⟨⟨e,t,ht,ht',hxe⟩,⟨v,u,hu,hu',hxv⟩⟩ :=
    packing_nonvertex_contact_open_edges f hdisjoint hij hxi hxj hvertex
  obtain ⟨a,ha⟩ := homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i
  obtain ⟨b,hb⟩ := homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root j
  have hs := homochiral_contact_unit_edges_whole f hdirect hdisjoint hcover i j
    (Ne.symm hij) e v t u ht ht' hu hu' x hxe hxv
  rcases hs with hs | hs
  · exact shared_vertex_origin_mem_quadraticPlane (f root) (f i) (f j) a b ha hb hi e v hs.1
  · exact shared_vertex_origin_mem_quadraticPlane (f root) (f i) (f j) a b ha hb hi e (next v) hs.1

/-- The registration lattice is derived from physical coverage and packing. -/
theorem homochiral_origin_mem_quadraticPlane {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root i : ι) :
    sourcePoint (f root) (f i 0) ∈ quadraticPlane := by
  have hp := CompactTilingIncidence.polygon_tiling_nonvertex_contact_connected f hdisjoint hcover root i
  induction hp with
  | refl =>
      have hz : sourcePoint (f root) (f root 0) = 0 := by
        simp only [sourcePoint, (f root).symm_apply_apply]
        exact coordinateLinearEquiv.symm.map_zero
      rw [hz]
      exact quadraticPlane.zero_mem
  | @tail a b hab hc ih =>
      exact nonvertex_contact_origin_mem_quadraticPlane f hdirect hdisjoint hcover root ih hc

theorem homochiral_vertex_mem_quadraticPlane {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root i : ι) (e : Fin 14) :
    sourcePoint (f root) (f i (euclideanVertex e)) ∈ quadraticPlane := by
  obtain ⟨k,hk⟩ := homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i
  exact relative_vertex_mem_quadraticPlane (f root) (f i) k hk
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i) e

end
end SpectreGeometry
