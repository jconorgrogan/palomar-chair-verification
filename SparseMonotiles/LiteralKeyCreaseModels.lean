module

public import SparseMonotiles.KeyRidgeAngles

@[expose] public section

/-! # Literal canonical key creases give the actual material wedge germ -/
namespace SparseMonotiles
open Set Canonical

/-- Canonical rigidity lets every valid canonical key frame use the proved
literal aligned carrier/base model. -/
theorem T5_local_merged_of_canonical_key
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    {p : Point 5} (hp : p ∈ keySolid k) :
    LocalSetEq p T5 (closure (mergedKeyRegion (posedHalfspaceSlack5 q) (.inl false) k.bump)) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  obtain ⟨r,hr,hlocal⟩ := T5_aligned_key_model (keys5.get_mem i)
    (keySolid_subset_coordinateSupport _ hp)
  have heq : r.euclidean = q.euclidean :=
    (chosenKeyPose5_euclidean_eq i r hr).symm.trans (chosenKeyPose5_euclidean_eq i q hq)
  have hslack : posedHalfspaceSlack5 r = posedHalfspaceSlack5 q := by
    funext j x
    change referenceHalfspaceSlack5 j (r.euclidean.symm x) = _
    rw [heq]
    rfl
  simpa only [hslack] using hlocal

/-- Explicit base/side crease coordinates yield the actual T5 wedge. -/
theorem T5_literal_base_side_crease_germ
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i : Fin 4) (si : Bool) {p : Point 5}
    (hb : posedHalfspaceSlack5 q (.inl false) p = 0)
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) p = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inl false → j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j p) :
    LocalSetEq p T5
      (closedBaseSideWedge (posedHalfspaceSlack5 q) (.inl false) (.inr (i,si)) k.bump) := by
  have hpk : p ∈ keySolid k := by
    apply (mem_keySolid5_iff_posed_halfspaces q hq p).mpr
    intro j
    by_cases h0 : j = .inl false
    · subst j; exact hb.ge
    · by_cases h1 : j = .inr (i,si)
      · subst j; exact hs.ge
      · exact (ho j h0 h1).le
  exact localSetEq_base_side_wedge5 q i si k.bump ho
    (T5_local_merged_of_canonical_key hk q hq hpk)

/-- Explicit distinct-side crease coordinates yield the actual T5 wedge. -/
theorem T5_literal_side_side_crease_germ
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i j : Fin 4) (si sj : Bool) {p : Point 5}
    (hi : posedHalfspaceSlack5 q (.inr (i,si)) p = 0)
    (hj : posedHalfspaceSlack5 q (.inr (j,sj)) p = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 4, l ≠ .inr (i,si) → l ≠ .inr (j,sj) →
      0 < posedHalfspaceSlack5 q l p) :
    LocalSetEq p T5
      (closedSideSideWedge (posedHalfspaceSlack5 q) (.inr (i,si)) (.inr (j,sj)) k.bump) := by
  have hpk : p ∈ keySolid k := by
    apply (mem_keySolid5_iff_posed_halfspaces q hq p).mpr
    intro l
    by_cases h0 : l = .inr (i,si)
    · subst l; exact hi.ge
    · by_cases h1 : l = .inr (j,sj)
      · subst l; exact hj.ge
      · exact (ho l h0 h1).le
  exact localSetEq_side_side_wedge5 q i j si sj k.bump (ho (.inl false) (by simp) (by simp))
    (fun l _ hli hlj => ho l hli hlj) (T5_local_merged_of_canonical_key hk q hq hpk)

#print axioms T5_local_merged_of_canonical_key
#print axioms T5_literal_base_side_crease_germ
#print axioms T5_literal_side_side_crease_germ

/-- Canonical rigidity lets every valid canonical key frame use the proved
literal aligned carrier/base model. -/
theorem T7_local_merged_of_canonical_key
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    {p : Point 7} (hp : p ∈ keySolid k) :
    LocalSetEq p T7 (closure (mergedKeyRegion (posedHalfspaceSlack7 q) (.inl false) k.bump)) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  obtain ⟨r,hr,hlocal⟩ := T7_aligned_key_model (keys7.get_mem i)
    (keySolid_subset_coordinateSupport _ hp)
  have heq : r.euclidean = q.euclidean :=
    (chosenKeyPose7_euclidean_eq i r hr).symm.trans (chosenKeyPose7_euclidean_eq i q hq)
  have hslack : posedHalfspaceSlack7 r = posedHalfspaceSlack7 q := by
    funext j x
    change referenceHalfspaceSlack7 j (r.euclidean.symm x) = _
    rw [heq]
    rfl
  simpa only [hslack] using hlocal

/-- Explicit base/side crease coordinates yield the actual T7 wedge. -/
theorem T7_literal_base_side_crease_germ
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i : Fin 6) (si : Bool) {p : Point 7}
    (hb : posedHalfspaceSlack7 q (.inl false) p = 0)
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) p = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inl false → j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j p) :
    LocalSetEq p T7
      (closedBaseSideWedge (posedHalfspaceSlack7 q) (.inl false) (.inr (i,si)) k.bump) := by
  have hpk : p ∈ keySolid k := by
    apply (mem_keySolid7_iff_posed_halfspaces q hq p).mpr
    intro j
    by_cases h0 : j = .inl false
    · subst j; exact hb.ge
    · by_cases h1 : j = .inr (i,si)
      · subst j; exact hs.ge
      · exact (ho j h0 h1).le
  exact localSetEq_base_side_wedge7 q i si k.bump ho
    (T7_local_merged_of_canonical_key hk q hq hpk)

/-- Explicit distinct-side crease coordinates yield the actual T7 wedge. -/
theorem T7_literal_side_side_crease_germ
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i j : Fin 6) (si sj : Bool) {p : Point 7}
    (hi : posedHalfspaceSlack7 q (.inr (i,si)) p = 0)
    (hj : posedHalfspaceSlack7 q (.inr (j,sj)) p = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 6, l ≠ .inr (i,si) → l ≠ .inr (j,sj) →
      0 < posedHalfspaceSlack7 q l p) :
    LocalSetEq p T7
      (closedSideSideWedge (posedHalfspaceSlack7 q) (.inr (i,si)) (.inr (j,sj)) k.bump) := by
  have hpk : p ∈ keySolid k := by
    apply (mem_keySolid7_iff_posed_halfspaces q hq p).mpr
    intro l
    by_cases h0 : l = .inr (i,si)
    · subst l; exact hi.ge
    · by_cases h1 : l = .inr (j,sj)
      · subst l; exact hj.ge
      · exact (ho l h0 h1).le
  exact localSetEq_side_side_wedge7 q i j si sj k.bump (ho (.inl false) (by simp) (by simp))
    (fun l _ hli hlj => ho l hli hlj) (T7_local_merged_of_canonical_key hk q hq hpk)

#print axioms T7_local_merged_of_canonical_key
#print axioms T7_literal_base_side_crease_germ
#print axioms T7_literal_side_side_crease_germ

end SparseMonotiles
