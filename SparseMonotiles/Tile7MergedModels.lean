module

public import SparseMonotiles.AlignedBindings7
public import SparseMonotiles.Tile7KeyAtlas
public import SparseMonotiles.Tile7CandidateUniverse
public import SparseMonotiles.KeyBasePlaneAlignment

@[expose] public section

/-! Exact physical base-plane pruning for every frozen literal key.
No base membrane is inserted into the closed dent construction. -/
namespace SparseMonotiles

open Contact Canonical Set Filter
open scoped Topology

/-- The exact atlas pose aligns the carrier plane and gives the pruned key model. -/
theorem T7_aligned_key_model {k : KeyData 7} (hk : k ∈ keys7)
    {x : Point 7} (hx : x ∈ keyCoordinateSupport k) :
    ∃ q : Pose 7, keySolid k = q.euclidean '' referenceSolid7 ∧
      LocalSetEq x T7
        (closure (mergedKeyRegion (posedHalfspaceSlack7 q) (.inl false) k.bump)) := by
  obtain ⟨i, b, hb, q, hm, hd⟩ := everyKey7_has_aligned_atlas_pose k hk
  have hc : x ∈ gridFacetCollar (IndexedData7.geometry.facet i).gridFacet :=
    BoxKey.coordinateSupport_subset_collar (by decide)
      ((atlas7_checked i).2.1 b hb) (hd.symm ▸ hx)
  have hT := (IndexedData7.geometry.facet i).localSetEq_body_isolated_halfspace
    (IndexedData7.owned_checked i) (atlas7_checked i).1 hk hc
    (T7_key_isolated hk hx) (LocalSetEq.refl x (keySolid k))
  exact ⟨q, canonical7_of_box_match q hm hd,
    localSetEq_merged7 q hm hd (T7_indexed_keys_oriented i b hb) hT⟩

/-- Complete local material inventory with the duplicate carrier/base plane removed. -/
theorem T7_local_merged_key_inventory (x : Point 7) :
    LocalSetEq x T7 (carrier 7) ∨
      ∃ k ∈ keys7, ∃ q : Pose 7, keySolid k = q.euclidean '' referenceSolid7 ∧
        LocalSetEq x T7
          (closure (mergedKeyRegion (posedHalfspaceSlack7 q) (.inl false) k.bump)) := by
  by_cases hx : ∃ k ∈ keys7, x ∈ keyCoordinateSupport k
  · obtain ⟨k, hk, hsupport⟩ := hx
    obtain ⟨q, hq, hm⟩ := T7_aligned_key_model hk hsupport
    exact Or.inr ⟨k, hk, q, hq, hm⟩
  · apply Or.inl
    apply localSetEq_body_carrier_away_keys
    apply away_keys_of_closed_supports keyCoordinateSupport
      (fun j _ => keySolid_subset_coordinateSupport j)
      (fun j _ => keyCoordinateSupport_isClosed j)
    intro j hj hpj
    exact hx ⟨j, hj, hpj⟩

#print axioms T7_aligned_key_model
#print axioms T7_local_merged_key_inventory

end SparseMonotiles
