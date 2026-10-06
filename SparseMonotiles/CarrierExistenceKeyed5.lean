module

public import SparseMonotiles.CarrierExistenceConcrete5
public import SparseMonotiles.CarrierExistenceProfileRules
public import SparseMonotiles.Tile5KeyAtlas
public import SparseMonotiles.CanonicalBindings5
public import SparseMonotiles.ReferenceKeyHalfspaces

@[expose] public section

/-! T5-only static instantiation of literal-body gluing. This keeps the actual
five-dimensional existence closure independent of the seven-dimensional
static certificate replay. -/
namespace SparseMonotiles.CarrierHierarchy.Existence.Catalog5World
open Contact Set Canonical

theorem exposed_support_facet (k : KeyData 5) (hk : k ∈ keys5) :
    ∃ f : Facet 5, IsChairCell f.cell ∧ ¬ IsChairCell f.neighbor ∧
      keyCoordinateSupport k ⊆ gridFacetCollar f.gridFacet := by
  obtain ⟨i, b, hb, he⟩ := everyKey5_in_atlas k hk
  refine ⟨IndexedData5.geometry.facet i, IndexedData5.owned_checked i, (atlas5_checked i).1, ?_⟩
  rw [← he]
  exact BoxKey.coordinateSupport_subset_collar (by decide) ((atlas5_checked i).2.1 b hb)

noncomputable def facets : KeyFacetAssignment keys5 where
  facet k hk := (exposed_support_facet k hk).choose
  owner k hk := (exposed_support_facet k hk).choose_spec.1
  exposed k hk := (exposed_support_facet k hk).choose_spec.2.1
  support k hk := (exposed_support_facet k hk).choose_spec.2.2

private theorem reference_closed : IsClosed referenceSolid5 := by
  have he : referenceSolid5 =
      ⋂ j : PyramidHalfspaceIndex 4, {x : Point 5 | 0 ≤ referenceHalfspaceSlack5 j x} := by
    ext x
    simp only [mem_referenceSolid5_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [he]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_referenceHalfspaceSlack5 j))

theorem literal_key_closed (k : KeyData 5) (hk : k ∈ keys5) : IsClosed (keySolid k) := by
  obtain ⟨p, hp⟩ := everyKey5_isCanonical k hk
  rw [hp]
  exact p.euclidean.toHomeomorph.isClosedMap _ reference_closed

theorem hasTiling_of_rules (forward : ForwardRules CoarseContactCertificates5.C M5)
    (profiles : ComplementaryProfiles facets M5) : HasTiling T5 := by
  refine ⟨(fun p : Pose 5 => p.euclidean '' T5) '' registered.tiles, ?_⟩
  exact realize_body_of_profiles keys5 facets M5 profiles
    (fun k hk j hj hne => T5_keySupports_disjoint hk hj hne.symm)
    literal_key_closed registered (legal forward)

#print axioms literal_key_closed
#print axioms hasTiling_of_rules
end SparseMonotiles.CarrierHierarchy.Existence.Catalog5World
