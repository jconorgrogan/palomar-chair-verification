module

public import SparseMonotiles.AlignedBindings5
public import SparseMonotiles.Tile5KeyAtlas
public import SparseMonotiles.Tile5CandidateUniverse
public import SparseMonotiles.KeyBasePlaneAlignment

@[expose] public section

/-! Exact physical base-plane pruning for every frozen literal key.
No base membrane is inserted into the closed dent construction. -/
namespace SparseMonotiles

open Contact Canonical Set Filter
open scoped Topology

/-- The exact atlas pose aligns the carrier plane and gives the pruned key model. -/
theorem T5_aligned_key_model {k : KeyData 5} (hk : k ∈ keys5)
    {x : Point 5} (hx : x ∈ keyCoordinateSupport k) :
    ∃ q : Pose 5, keySolid k = q.euclidean '' referenceSolid5 ∧
      LocalSetEq x T5
        (closure (mergedKeyRegion (posedHalfspaceSlack5 q) (.inl false) k.bump)) := by
  obtain ⟨i, b, hb, q, hm, hd⟩ := everyKey5_has_aligned_atlas_pose k hk
  have hc : x ∈ gridFacetCollar (IndexedData5.geometry.facet i).gridFacet :=
    BoxKey.coordinateSupport_subset_collar (by decide)
      ((atlas5_checked i).2.1 b hb) (hd.symm ▸ hx)
  have hT := (IndexedData5.geometry.facet i).localSetEq_body_isolated_halfspace
    (IndexedData5.owned_checked i) (atlas5_checked i).1 hk hc
    (T5_key_isolated hk hx) (LocalSetEq.refl x (keySolid k))
  exact ⟨q, canonical5_of_box_match q hm hd,
    localSetEq_merged5 q hm hd (T5_indexed_keys_oriented i b hb) hT⟩

/-- Complete local material inventory with the duplicate carrier/base plane removed. -/
theorem T5_local_merged_key_inventory (x : Point 5) :
    LocalSetEq x T5 (carrier 5) ∨
      ∃ k ∈ keys5, ∃ q : Pose 5, keySolid k = q.euclidean '' referenceSolid5 ∧
        LocalSetEq x T5
          (closure (mergedKeyRegion (posedHalfspaceSlack5 q) (.inl false) k.bump)) := by
  by_cases hx : ∃ k ∈ keys5, x ∈ keyCoordinateSupport k
  · obtain ⟨k, hk, hsupport⟩ := hx
    obtain ⟨q, hq, hm⟩ := T5_aligned_key_model hk hsupport
    exact Or.inr ⟨k, hk, q, hq, hm⟩
  · apply Or.inl
    apply localSetEq_body_carrier_away_keys
    apply away_keys_of_closed_supports keyCoordinateSupport
      (fun j _ => keySolid_subset_coordinateSupport j)
      (fun j _ => keyCoordinateSupport_isClosed j)
    intro j hj hpj
    exact hx ⟨j, hj, hpj⟩

#print axioms T5_aligned_key_model
#print axioms T5_local_merged_key_inventory

end SparseMonotiles
