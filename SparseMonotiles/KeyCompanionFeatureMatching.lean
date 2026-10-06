module

public import SparseMonotiles.KeyCompanionFeatureMatchingRecognition
public import SparseMonotiles.KeyCompanionFeatureMatchingFrontier
public import SparseMonotiles.KeySideCompanionPropagation

@[expose] public section

/-! # Complete K3 in an arbitrary physical tiling
K1/K2 supply one physical companion across all closed sides. The actual body
boundary inventory forces a common key apex and exhausts the side planes;
closed support continuation, convexity and compact congruence give solid equality.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_all_closed_sides_companion_matches_key
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A B : tiles) (hBA : B ≠ A)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k=q.euclidean '' referenceSolid5)
    (hcover : ∀ (i : Fin 4) (b : Bool),
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,b)) x=0}) ⊆ (B : Set (Point 5))) :
    ∃ l ∈ keys5, ∃ r : Contact.Pose 5,
      keySolid l=r.euclidean '' referenceSolid5 ∧ g A '' keySolid k=g B '' keySolid l := by
  let k₀ := (referenceBox5 true).toKeyData 19200
  let W : Point 5 ≃ᵃⁱ[ℝ] Point 5 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := W.trans (g B).symm.toRealAffineIsometryEquiv
  have hBAset : (B : Set (Point 5)) ≠ (A : Set (Point 5)) := fun h => hBA (Subtype.ext h)
  have hfront : ∀ i b, W '' keySideClosedFace k₀ i b ⊆ frontier (g B '' T5) := by
    intro i b
    have h := T5_closed_key_side_subset_companion_frontier ht g hg A hk q hq i b
      B.property hBAset (hcover i b)
    rw [T5_world_closed_key_side_eq_reference (g A) q hq,hg B] at h
    exact h
  have hnative : ∀ i b, e '' keySideClosedFace k₀ i b ⊆ frontier T5 :=
    key_closed_sides_pullback_frontier k₀ W (g B) T5 hfront
  obtain ⟨l,hl,r,hr,heq⟩ := T5_boundary_side_cover_recognizes_whole_key e hnative
  refine ⟨l,hl,r,hr,?_⟩
  have hpush := congrArg (fun S : Set (Point 5) => g B '' S) heq
  have hleft : g B '' (e '' referenceSolid5)=g A '' keySolid k := by
    rw [Set.image_image,hq,Set.image_image]
    apply Set.image_congr
    intro x hx
    change g B ((g B).symm (g A (q.euclidean x)))=g A (q.euclidean x)
    exact (g B).apply_symm_apply _
  change g B '' (e '' referenceSolid5)=g B '' keySolid l at hpush
  rw [hleft] at hpush
  exact hpush

/-- Complete literal K3: the companion and its actual matching key are derived
from the physical tiling, without a side-cover or feature-matching premise. -/
theorem T5_literal_key_has_whole_key_companion
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k=q.euclidean '' referenceSolid5) :
    ∃ B : tiles, B ≠ A ∧ ∃ l ∈ keys5, ∃ r : Contact.Pose 5,
      keySolid l=r.euclidean '' referenceSolid5 ∧ g A '' keySolid k=g B '' keySolid l := by
  obtain ⟨B,hB,hBA,hcover⟩ := T5_entire_key_sides_one_companion ht g hg A hk q hq
  let B' : tiles := ⟨B,hB⟩
  have hBA' : B' ≠ A := fun h => hBA (congrArg Subtype.val h)
  obtain ⟨l,hl,r,hr,heq⟩ := T5_all_closed_sides_companion_matches_key ht g hg A B' hBA' hk q hq hcover
  exact ⟨B',hBA',l,hl,r,hr,heq⟩

/-- Every actual key in every physical tile has an entire matching key in a
distinct physical companion. Even the root canonical pose is selected internally. -/
theorem T5_key_has_whole_key_companion
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) :
    ∃ B : tiles, B ≠ A ∧ ∃ l ∈ keys5, g A '' keySolid k=g B '' keySolid l := by
  obtain ⟨q,hq⟩ := everyKey5_isCanonical k hk
  obtain ⟨B,hBA,l,hl,r,hr,heq⟩ := T5_literal_key_has_whole_key_companion ht g hg A hk q hq
  exact ⟨B,hBA,l,hl,heq⟩

#print axioms T5_all_closed_sides_companion_matches_key
#print axioms T5_literal_key_has_whole_key_companion
#print axioms T5_key_has_whole_key_companion

theorem T7_all_closed_sides_companion_matches_key
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A B : tiles) (hBA : B ≠ A)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k=q.euclidean '' referenceSolid7)
    (hcover : ∀ (i : Fin 6) (b : Bool),
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,b)) x=0}) ⊆ (B : Set (Point 7))) :
    ∃ l ∈ keys7, ∃ r : Contact.Pose 7,
      keySolid l=r.euclidean '' referenceSolid7 ∧ g A '' keySolid k=g B '' keySolid l := by
  let k₀ := (referenceBox7 true).toKeyData 188160
  let W : Point 7 ≃ᵃⁱ[ℝ] Point 7 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := W.trans (g B).symm.toRealAffineIsometryEquiv
  have hBAset : (B : Set (Point 7)) ≠ (A : Set (Point 7)) := fun h => hBA (Subtype.ext h)
  have hfront : ∀ i b, W '' keySideClosedFace k₀ i b ⊆ frontier (g B '' T7) := by
    intro i b
    have h := T7_closed_key_side_subset_companion_frontier ht g hg A hk q hq i b
      B.property hBAset (hcover i b)
    rw [T7_world_closed_key_side_eq_reference (g A) q hq,hg B] at h
    exact h
  have hnative : ∀ i b, e '' keySideClosedFace k₀ i b ⊆ frontier T7 :=
    key_closed_sides_pullback_frontier k₀ W (g B) T7 hfront
  obtain ⟨l,hl,r,hr,heq⟩ := T7_boundary_side_cover_recognizes_whole_key e hnative
  refine ⟨l,hl,r,hr,?_⟩
  have hpush := congrArg (fun S : Set (Point 7) => g B '' S) heq
  have hleft : g B '' (e '' referenceSolid7)=g A '' keySolid k := by
    rw [Set.image_image,hq,Set.image_image]
    apply Set.image_congr
    intro x hx
    change g B ((g B).symm (g A (q.euclidean x)))=g A (q.euclidean x)
    exact (g B).apply_symm_apply _
  change g B '' (e '' referenceSolid7)=g B '' keySolid l at hpush
  rw [hleft] at hpush
  exact hpush

/-- Complete literal K3: the companion and its actual matching key are derived
from the physical tiling, without a side-cover or feature-matching premise. -/
theorem T7_literal_key_has_whole_key_companion
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k=q.euclidean '' referenceSolid7) :
    ∃ B : tiles, B ≠ A ∧ ∃ l ∈ keys7, ∃ r : Contact.Pose 7,
      keySolid l=r.euclidean '' referenceSolid7 ∧ g A '' keySolid k=g B '' keySolid l := by
  obtain ⟨B,hB,hBA,hcover⟩ := T7_entire_key_sides_one_companion ht g hg A hk q hq
  let B' : tiles := ⟨B,hB⟩
  have hBA' : B' ≠ A := fun h => hBA (congrArg Subtype.val h)
  obtain ⟨l,hl,r,hr,heq⟩ := T7_all_closed_sides_companion_matches_key ht g hg A B' hBA' hk q hq hcover
  exact ⟨B',hBA',l,hl,r,hr,heq⟩

/-- Every actual key in every physical tile has an entire matching key in a
distinct physical companion. Even the root canonical pose is selected internally. -/
theorem T7_key_has_whole_key_companion
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) :
    ∃ B : tiles, B ≠ A ∧ ∃ l ∈ keys7, g A '' keySolid k=g B '' keySolid l := by
  obtain ⟨q,hq⟩ := everyKey7_isCanonical k hk
  obtain ⟨B,hBA,l,hl,r,hr,heq⟩ := T7_literal_key_has_whole_key_companion ht g hg A hk q hq
  exact ⟨B,hBA,l,hl,heq⟩

#print axioms T7_all_closed_sides_companion_matches_key
#print axioms T7_literal_key_has_whole_key_companion
#print axioms T7_key_has_whole_key_companion

end SparseMonotiles
