module

public import LiteralPlanar.EdgeDeformation
public import LiteralPlanar.SourceTiling
public import LiteralPlanar.OrientedSourceEdges

@[expose] public section


/-! Compatibility at every physical source contact. Endpoint contacts and
strict edge contacts are handled separately; no edge-to-edge premise is added. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry FanBounds

def placedTileMap (f : EPlane ≃ᵢ EPlane) (x : EPlane) : EPlane :=
  f (tileMap (f.symm x))

def placedTileResidual (f : EPlane ≃ᵢ EPlane) (x : EPlane) : EPlane :=
  f.toRealLinearIsometryEquiv (tileResidual (f.symm x))

theorem placedTileMap_eq_add (f : EPlane ≃ᵢ EPlane) (x : EPlane) :
    placedTileMap f x = x + placedTileResidual f x := by
  have he (z : EPlane) : f z = f.toRealLinearIsometryEquiv z + f 0 := by
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]
    exact (sub_add_cancel _ _).symm
  unfold placedTileMap tileMap placedTileResidual
  rw [he (f.symm x + tileResidual (f.symm x)), map_add,
    IsometryEquiv.toRealLinearIsometryEquiv_apply, IsometryEquiv.apply_symm_apply]
  abel

theorem placedTileMap_at_vertex (f : EPlane ≃ᵢ EPlane) (e : Fin 14) :
    placedTileMap f (f (euclideanVertex e)) = f (euclideanVertex e) := by
  simp only [placedTileMap, IsometryEquiv.symm_apply_apply, tileMap,
    tileResidual_at_vertex, add_zero]

theorem source_contact_vertex_iff {I : Type*} (p : I → EPlane ≃ᵢ EPlane)
    (T : SourceTiling p) {i j : I} (hij : i ≠ j) {x : EPlane}
    (hi : x ∈ p i '' euclideanBody) (hj : x ∈ p j '' euclideanBody) :
    (∃ e : Fin 14, x = p i (euclideanVertex e)) ↔
      (∃ e : Fin 14, x = p j (euclideanVertex e)) := by
  have hr : ∀ k, p k '' euclideanBody ⊆ closure (interior (p k '' euclideanBody)) := by
    intro k
    rw [placed_body_closure_interior]
  have hf := CompactTilingIncidence.common_point_frontiers (fun k => p k '' euclideanBody)
    (fun k => (euclideanBody_compact.image (p k).continuous).isClosed)
    hr T.interiors_disjoint hij hi hj
  constructor
  · rintro ⟨e,he⟩
    by_contra hn
    have hnv : ∀ q, x ≠ p j (euclideanVertex q) := by simpa only [not_exists] using hn
    obtain ⟨q,t,ht,ht',hx⟩ := nonvertex_frontier_open_edge (p j) hf.2 hnv
    exact homochiral_no_vertex_in_unit_edge p T.direct T.interiors_disjoint T.covers
      j i hij q e t ht ht' (hx.symm.trans he)
  · rintro ⟨e,he⟩
    by_contra hn
    have hnv : ∀ q, x ≠ p i (euclideanVertex q) := by simpa only [not_exists] using hn
    obtain ⟨q,t,ht,ht',hx⟩ := nonvertex_frontier_open_edge (p i) hf.1 hnv
    exact homochiral_no_vertex_in_unit_edge p T.direct T.interiors_disjoint T.covers
      i j (Ne.symm hij) q e t ht ht' (hx.symm.trans he)

/-- The piecewise polynomial map has a single value at all source contacts. -/
theorem placedTileMap_agrees {I : Type*} (p : I → EPlane ≃ᵢ EPlane)
    (T : SourceTiling p) (i j : I) (x : EPlane)
    (hi : x ∈ p i '' euclideanBody) (hj : x ∈ p j '' euclideanBody) :
    placedTileMap (p i) x = placedTileMap (p j) x := by
  by_cases hij : i = j
  · rw [hij]
  by_cases hv : ∃ e : Fin 14, x = p i (euclideanVertex e)
  · obtain ⟨a,ha⟩ := hv
    obtain ⟨b,hb⟩ := (source_contact_vertex_iff p T hij hi hj).mp ⟨a,ha⟩
    rw [ha,placedTileMap_at_vertex]
    rw [←ha,hb,placedTileMap_at_vertex]
  have hr : ∀ k, p k '' euclideanBody ⊆ closure (interior (p k '' euclideanBody)) := by
    intro k
    rw [placed_body_closure_interior]
  have hf := CompactTilingIncidence.common_point_frontiers (fun k => p k '' euclideanBody)
    (fun k => (euclideanBody_compact.image (p k).continuous).isClosed)
    hr T.interiors_disjoint hij hi hj
  have hvi : ∀ e, x ≠ p i (euclideanVertex e) := by simpa only [not_exists] using hv
  have hvj : ∀ e, x ≠ p j (euclideanVertex e) := by
    intro e he
    exact hv ((source_contact_vertex_iff p T hij hi hj).mpr ⟨e,he⟩)
  obtain ⟨a,t,ht,ht',hxa⟩ := nonvertex_frontier_open_edge (p i) hf.1 hvi
  obtain ⟨b,u,hu,hu',hxb⟩ := nonvertex_frontier_open_edge (p j) hf.2 hvj
  obtain ⟨ha,hb⟩ := homochiral_contact_unit_edges_reversed p T.direct
    T.interiors_disjoint T.covers i j (Ne.symm hij) a b t u ht ht' hu hu' x hxa hxb
  have hxrev : p j (euclideanCoordinates
      (interpolate (realVertex b) (realVertex (next b)) (1-t))) = x := by
    rw [placed_edge_interpolate, placedEdgeVector, ←hb, ←ha, hxa,
      placed_edge_interpolate, placedEdgeVector]
    simp only [sub_smul,one_smul,smul_sub]
    abel
  have hpre : (p j).symm x = euclideanCoordinates
      (interpolate (realVertex b) (realVertex (next b)) (1-t)) := by
    rw [←hxrev,IsometryEquiv.symm_apply_apply]
  unfold placedTileMap
  rw [hpre,hxa,IsometryEquiv.symm_apply_apply]
  exact placed_tileMap_on_reversed_edge (p i) (p j) (T.direct i) (T.direct j)
    a b ha hb t ht.le ht'.le

theorem placedTileResidual_agrees {I : Type*} (p : I → EPlane ≃ᵢ EPlane)
    (T : SourceTiling p) (i j : I) (x : EPlane)
    (hi : x ∈ p i '' euclideanBody) (hj : x ∈ p j '' euclideanBody) :
    placedTileResidual (p i) x = placedTileResidual (p j) x := by
  have h := placedTileMap_agrees p T i j x hi hj
  simpa only [placedTileMap_eq_add, add_right_inj] using h

end
end LiteralPlanar.Forward
