module
public import SparseMonotiles.T7ExistenceRepresentatives
public import SparseMonotiles.CarrierExistenceLegality
public import SparseMonotiles.Tile7KeyAtlas
public import SparseMonotiles.CanonicalBindings7
public import SparseMonotiles.ReferenceKeyHalfspaces
@[expose] public section

/-! Supported-toolchain compact T7 existence endpoint. The carrier world is
constructed; its M7 legality still requires exact finite forward rules. Literal
profile matching still requires the207 unchecked inverse representatives. -/
namespace SparseMonotiles.CarrierHierarchy.Existence.Catalog7World
open Contact ContactInverseReuse Set Canonical
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem empty_child : Catalog7.childPerm (fun _ => false) = Equiv.refl _ := by decide

def children7 : Finset (Pose 7) :=
  insert (centralPose 7) ((Finset.univ.filter (fun a : Bits 7 => Proper a)).image
    (fun a => outerPose a (Catalog7.childPerm a)))

theorem children7_covers : CoversCanonicalChildren Catalog7.childPerm children7 := by
  constructor
  · exact Finset.mem_insert_self _ _
  · intro a ha
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)

theorem children7_count : children7.card = 128 := by decide +kernel

def registered : RegisteredWorld 7 := Existence.world (by decide) Catalog7.childPerm empty_child

theorem legal (rules : ForwardRules children7 M7) : registered.Legal M7 :=
  world_legal (by decide) Catalog7.childPerm empty_child children7 M7 children7_covers rules

private theorem reference_closed : IsClosed referenceSolid7 := by
  have he : referenceSolid7 =
      ⋂ j : PyramidHalfspaceIndex 6, {x : Point 7 | 0 ≤ referenceHalfspaceSlack7 j x} := by
    ext x
    simp only [mem_referenceSolid7_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [he]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_referenceHalfspaceSlack7 j))

theorem literal_key_closed (k : KeyData 7) (hk : k ∈ keys7) : IsClosed (keySolid k) := by
  obtain ⟨p, hp⟩ := everyKey7_isCanonical k hk
  rw [hp]
  exact p.euclidean.toHomeomorph.isClosedMap _ reference_closed

/-- Actual literal-body tiling, conditional on forward rules and exact profiles.
No pre-existing M7-legal world or physical contact law is assumed. -/
theorem hasTiling_of_forward_profiles
    (forward : ForwardRules children7 M7)
    (profiles : ComplementaryProfiles ProfileBridge7.facets M7) : HasTiling T7 := by
  refine ⟨(fun p : Pose 7 => p.euclidean '' T7) '' registered.tiles, ?_⟩
  exact realize_body_of_profiles keys7 ProfileBridge7.facets M7 profiles
    (fun k hk j hj hne => T7_keySupports_disjoint hk hj hne.symm)
    literal_key_closed registered (legal forward)

/-- The remaining existence obligations are explicit finite forward rules
and legal-contact certificates for207 exact inverse representatives. -/
theorem hasTiling_of_forward_and_remaining_representatives
    (forward : ForwardRules children7 M7)
    (hlegal : ∀ i ∈ ProfileBridge7.remainingAcceptanceRepresentatives,
      IndexedData7.geometry.LegalContact (catalogRow i)) : HasTiling T7 :=
  hasTiling_of_forward_profiles forward
    (ProfileBridge7.complementaryProfiles_of_remaining_representatives hlegal ProfileBridge7.facets)

#print axioms children7_count
#print axioms registered
#print axioms legal
#print axioms literal_key_closed
#print axioms hasTiling_of_forward_profiles
#print axioms hasTiling_of_forward_and_remaining_representatives
end SparseMonotiles.CarrierHierarchy.Existence.Catalog7World
