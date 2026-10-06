module

public import SparseMonotiles.StripCreaseCrossingClosedFace
public import SparseMonotiles.KeyCompanionFeatureMatchingApexPatches

@[expose] public section

/-! # Closed key sides lie in the actual companion's frontier
The root's proved halfspace germ supplies adherence to its interior. Disjoint
physical tile interiors then exclude every companion interior point. Closure
extends the result from strict side patches to all their apex/crease points.
-/
namespace SparseMonotiles
open Set Canonical

theorem key_side_material_regular_at_zero {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (p : Point (n+1))
    (i : Fin n) (si b : Bool) (hs : keyPyramidHalfspaceSlack k (.inr (i,si)) (e p)=0) :
    p ∈ closure (interior (sideMaterialHalfspace
      (fun x => keyPyramidHalfspaceSlack k (.inr (i,si)) (e x)) b)) := by
  let R : AffineSubspace ℝ (Point (n+1)) := AffineSubspace.mk' p ⊥
  have hp : p ∈ R := by simp [R,AffineSubspace.mem_mk']
  apply key_side_material_regular_at_ridge k hd e R hp i si b
  intro x hx
  have hxp : x=p := by simpa [R,AffineSubspace.mem_mk',sub_eq_zero] using hx
  simpa only [hxp] using hs

theorem T5_world_closed_key_side_eq_reference
    (g : Point 5 ≃ᵢ Point 5) {k : KeyData 5} (q : Contact.Pose 5)
    (hq : keySolid k=q.euclidean '' referenceSolid5) (i : Fin 4) (si : Bool) :
    g '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) =
      (q.euclidean.trans g.toRealAffineIsometryEquiv) ''
        keySideClosedFace ((referenceBox5 true).toKeyData 19200) i si := by
  ext x
  constructor
  · rintro ⟨z,⟨hz,hs⟩,rfl⟩
    rw [hq] at hz
    obtain ⟨y,hy,rfl⟩ := hz
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    simpa [referenceHalfspaceSlack5,posedHalfspaceSlack5] using hs
  · rintro ⟨y,⟨hy,hs⟩,rfl⟩
    refine ⟨q.euclidean y,⟨?_,?_⟩,rfl⟩
    · rw [hq]; exact ⟨y,hy,rfl⟩
    · simpa [referenceHalfspaceSlack5,posedHalfspaceSlack5] using hs

/-- A covering physical companion has the entire actual closed key side in
its frontier, not just in the underlying closed tile. -/
theorem T5_closed_key_side_subset_companion_frontier
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k=q.euclidean '' referenceSolid5) (i : Fin 4) (si : Bool)
    {B : Set (Point 5)} (hB : B ∈ tiles) (hBA : B ≠ (A : Set (Point 5)))
    (hcover : g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) ⊆ B) :
    g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) ⊆ frontier B := by
  let k₀ := (referenceBox5 true).toKeyData 19200
  let W : Point 5 ≃ᵃⁱ[ℝ] Point 5 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := (g A).symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hc : k₀.centre (Fin.last 4)=0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 4)=0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
    exact_mod_cast referenceBox5_height_pos true
  have hd : ∀ j b, 0 < keySideDistance k₀ j b := referenceSideDistance5_pos
  rw [T5_world_closed_key_side_eq_reference (g A) q hq] at hcover ⊢
  change W '' keySideClosedFace k₀ i si ⊆ frontier B
  rw [← closure_posedKeySidePatch k₀ hc hr hh hd]
  apply closure_minimal _ isClosed_frontier
  rintro x ⟨y,hy,rfl⟩
  have hf (j : PyramidHalfspaceIndex 4) :
      posedHalfspaceSlack5 q j ((g A).symm (W y))=keyPyramidHalfspaceSlack k₀ j y := by
    simp [W,posedHalfspaceSlack5,referenceHalfspaceSlack5,k₀]
  have hs : posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm (W y))=0 := (hf _).trans hy.1
  have ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j ((g A).symm (W y)) := by
    intro j hj
    rw [hf]
    exact hy.2 j hj
  have hl := (T5_copy_literal_side_relativeInterior_germ (g A) hk q hq i si hs ho).2
  rw [← hg A] at hl
  have hreg := key_side_material_regular_at_zero k₀ hd e (W y) i si k.bump hs
  have hregA : W y ∈ closure (interior (A : Set (Point 5))) :=
    hl.interior.closure.mem_iff.mpr hreg
  rw [frontier,(ht.tile_isClosed T5_isCompact hB).closure_eq]
  exact ⟨hcover ⟨y,keySideStrictPatch_subset_face k₀ hc hr hh i si hy,rfl⟩,
    not_mem_interior_of_disjoint_root (ht.2.2 B hB A A.property hBA) hregA⟩

#print axioms T5_closed_key_side_subset_companion_frontier

theorem T7_world_closed_key_side_eq_reference
    (g : Point 7 ≃ᵢ Point 7) {k : KeyData 7} (q : Contact.Pose 7)
    (hq : keySolid k=q.euclidean '' referenceSolid7) (i : Fin 6) (si : Bool) :
    g '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) =
      (q.euclidean.trans g.toRealAffineIsometryEquiv) ''
        keySideClosedFace ((referenceBox7 true).toKeyData 188160) i si := by
  ext x
  constructor
  · rintro ⟨z,⟨hz,hs⟩,rfl⟩
    rw [hq] at hz
    obtain ⟨y,hy,rfl⟩ := hz
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    simpa [referenceHalfspaceSlack7,posedHalfspaceSlack7] using hs
  · rintro ⟨y,⟨hy,hs⟩,rfl⟩
    refine ⟨q.euclidean y,⟨?_,?_⟩,rfl⟩
    · rw [hq]; exact ⟨y,hy,rfl⟩
    · simpa [referenceHalfspaceSlack7,posedHalfspaceSlack7] using hs

/-- A covering physical companion has the entire actual closed key side in
its frontier, not just in the underlying closed tile. -/
theorem T7_closed_key_side_subset_companion_frontier
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k=q.euclidean '' referenceSolid7) (i : Fin 6) (si : Bool)
    {B : Set (Point 7)} (hB : B ∈ tiles) (hBA : B ≠ (A : Set (Point 7)))
    (hcover : g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) ⊆ B) :
    g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) ⊆ frontier B := by
  let k₀ := (referenceBox7 true).toKeyData 188160
  let W : Point 7 ≃ᵃⁱ[ℝ] Point 7 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := (g A).symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hc : k₀.centre (Fin.last 6)=0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 6)=0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
    exact_mod_cast referenceBox7_height_pos true
  have hd : ∀ j b, 0 < keySideDistance k₀ j b := referenceSideDistance7_pos
  rw [T7_world_closed_key_side_eq_reference (g A) q hq] at hcover ⊢
  change W '' keySideClosedFace k₀ i si ⊆ frontier B
  rw [← closure_posedKeySidePatch k₀ hc hr hh hd]
  apply closure_minimal _ isClosed_frontier
  rintro x ⟨y,hy,rfl⟩
  have hf (j : PyramidHalfspaceIndex 6) :
      posedHalfspaceSlack7 q j ((g A).symm (W y))=keyPyramidHalfspaceSlack k₀ j y := by
    simp [W,posedHalfspaceSlack7,referenceHalfspaceSlack7,k₀]
  have hs : posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm (W y))=0 := (hf _).trans hy.1
  have ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j ((g A).symm (W y)) := by
    intro j hj
    rw [hf]
    exact hy.2 j hj
  have hl := (T7_copy_literal_side_relativeInterior_germ (g A) hk q hq i si hs ho).2
  rw [← hg A] at hl
  have hreg := key_side_material_regular_at_zero k₀ hd e (W y) i si k.bump hs
  have hregA : W y ∈ closure (interior (A : Set (Point 7))) :=
    hl.interior.closure.mem_iff.mpr hreg
  rw [frontier,(ht.tile_isClosed T7_isCompact hB).closure_eq]
  exact ⟨hcover ⟨y,keySideStrictPatch_subset_face k₀ hc hr hh i si hy,rfl⟩,
    not_mem_interior_of_disjoint_root (ht.2.2 B hB A A.property hBA) hregA⟩

#print axioms T7_closed_key_side_subset_companion_frontier

end SparseMonotiles
