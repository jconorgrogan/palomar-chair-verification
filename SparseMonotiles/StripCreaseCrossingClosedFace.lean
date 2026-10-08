module

public import SparseMonotiles.StripCreaseCrossingFaceCompanion
public import SparseMonotiles.KeySideFacePatchTransport

@[expose] public section

/-! # Complete K1 for the entire actual closed side of every literal key
All generic-face, side-patch, seam-exclusion, opposite-germ and continuation
premises are discharged. No face-to-face or companion premise is assumed.
-/
namespace SparseMonotiles
open Set Canonical

/-- One distinct physical tile contains the entire closed side face of any
actual T5 key, including all its crease and apex boundary points. -/
theorem T5_entire_closed_key_side_companion
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5) (i : Fin 4) (si : Bool) :
    ∃ B ∈ tiles, B ≠ (A : Set (Point 5)) ∧
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x = 0}) ⊆ B := by
  let k₀ := (referenceBox5 true).toKeyData 19200
  let W : Point 5 ≃ᵃⁱ[ℝ] Point 5 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let P := posedKeySidePlane k₀ i si W
  let O := posedKeySidePatch k₀ i si W
  have hc : k₀.centre (Fin.last 4) = 0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 4) = 0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
    exact_mod_cast referenceBox5_height_pos true
  have hd : ∀ j b, 0 < keySideDistance k₀ j b := referenceSideDistance5_pos
  have hside : ∀ x ∈ O,
      posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm x) = 0 ∧
      ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) → 0 < posedHalfspaceSlack5 q j ((g A).symm x) := by
    rintro x ⟨y,hy,rfl⟩
    have hf (j : PyramidHalfspaceIndex 4) :
        posedHalfspaceSlack5 q j ((g A).symm (W y)) = keyPyramidHalfspaceSlack k₀ j y := by
      simp [W,posedHalfspaceSlack5,referenceHalfspaceSlack5,k₀]
    refine ⟨(hf _).trans hy.1,?_⟩
    intro j hj
    rw [hf]
    exact hy.2 j hj
  obtain ⟨G,hGO,hpath,hcl,B,hB,hBA,hcover,hlocal,hunique⟩ :=
    T5_key_side_patch_whole_companion ht g hg A hk q hq i si P
      (posedKeySidePlane_nonempty k₀ i si W) (posedKeySidePlane_finrank k₀ i si W) O
      (posedKeySidePatch_bounded k₀ hc hr hh i si W)
      (isOpen_posedKeySidePatch_in_plane k₀ hd i si W) (convex_posedKeySidePatch k₀ i si W)
      (posedKeySidePatch_nonempty_in_plane k₀ hh hd i si W) hside
  have hclosed : W '' keySideClosedFace k₀ i si ⊆ B := by
    rw [← posedKeySidePatch_intrinsic_closure k₀ hc hr hh hd i si W]
    exact hcover
  refine ⟨B,hB,hBA,?_⟩
  rintro x ⟨z,⟨hz,hzs⟩,rfl⟩
  rw [hq] at hz
  obtain ⟨y,hy,rfl⟩ := hz
  apply hclosed
  refine ⟨y,⟨hy,?_⟩,rfl⟩
  simpa [posedHalfspaceSlack5, referenceHalfspaceSlack5, k₀] using hzs

#print axioms T5_entire_closed_key_side_companion

/-- One distinct physical tile contains the entire closed side face of any
actual T7 key, including all its crease and apex boundary points. -/
theorem T7_entire_closed_key_side_companion
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7) (i : Fin 6) (si : Bool) :
    ∃ B ∈ tiles, B ≠ (A : Set (Point 7)) ∧
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x = 0}) ⊆ B := by
  let k₀ := (referenceBox7 true).toKeyData 188160
  let W : Point 7 ≃ᵃⁱ[ℝ] Point 7 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let P := posedKeySidePlane k₀ i si W
  let O := posedKeySidePatch k₀ i si W
  have hc : k₀.centre (Fin.last 6) = 0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 6) = 0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
    exact_mod_cast referenceBox7_height_pos true
  have hd : ∀ j b, 0 < keySideDistance k₀ j b := referenceSideDistance7_pos
  have hside : ∀ x ∈ O,
      posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm x) = 0 ∧
      ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) → 0 < posedHalfspaceSlack7 q j ((g A).symm x) := by
    rintro x ⟨y,hy,rfl⟩
    have hf (j : PyramidHalfspaceIndex 6) :
        posedHalfspaceSlack7 q j ((g A).symm (W y)) = keyPyramidHalfspaceSlack k₀ j y := by
      simp [W,posedHalfspaceSlack7,referenceHalfspaceSlack7,k₀]
    refine ⟨(hf _).trans hy.1,?_⟩
    intro j hj
    rw [hf]
    exact hy.2 j hj
  obtain ⟨G,hGO,hpath,hcl,B,hB,hBA,hcover,hlocal,hunique⟩ :=
    T7_key_side_patch_whole_companion ht g hg A hk q hq i si P
      (posedKeySidePlane_nonempty k₀ i si W) (posedKeySidePlane_finrank k₀ i si W) O
      (posedKeySidePatch_bounded k₀ hc hr hh i si W)
      (isOpen_posedKeySidePatch_in_plane k₀ hd i si W) (convex_posedKeySidePatch k₀ i si W)
      (posedKeySidePatch_nonempty_in_plane k₀ hh hd i si W) hside
  have hclosed : W '' keySideClosedFace k₀ i si ⊆ B := by
    rw [← posedKeySidePatch_intrinsic_closure k₀ hc hr hh hd i si W]
    exact hcover
  refine ⟨B,hB,hBA,?_⟩
  rintro x ⟨z,⟨hz,hzs⟩,rfl⟩
  rw [hq] at hz
  obtain ⟨y,hy,rfl⟩ := hz
  apply hclosed
  refine ⟨y,⟨hy,?_⟩,rfl⟩
  simpa [posedHalfspaceSlack7, referenceHalfspaceSlack7, k₀] using hzs

#print axioms T7_entire_closed_key_side_companion

end SparseMonotiles
