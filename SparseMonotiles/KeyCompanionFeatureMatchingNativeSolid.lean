module

public import SparseMonotiles.KeyCompanionFeatureMatchingSolid
public import SparseMonotiles.CarrierBoundaryPlaneCover
public import SparseMonotiles.Tile5KeyAtlas
public import SparseMonotiles.Tile7KeyAtlas

@[expose] public section

/-! # Canonical actual-body solid matching from a native apex/side-plane match
All finite support, carrier-plane exclusion, compactness and congruence inputs
are discharged for the two fixed bodies. The remaining apex/plane match is
supplied by the actual local boundary-plane inventory and counting theorem.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_native_whole_key_coincidence_of_apex_side_planes
    (W : Point 5 ≃ᵃⁱ[ℝ] Point 5)
    (hside : ∀ i b, W '' keySideClosedFace ((referenceBox5 true).toKeyData 19200) i b ⊆ frontier T5)
    {l : KeyData 5} (hl : l ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid l=q.euclidean '' referenceSolid5)
    (hapex : W (rationalPoint ((referenceBox5 true).toKeyData 19200).apex)=
      q.euclidean (rationalPoint ((referenceBox5 true).toKeyData 19200).apex))
    (σ : (Fin 4 × Bool) ≃ (Fin 4 × Bool))
    (hplanes : ∀ a, posedKeySidePlane ((referenceBox5 true).toKeyData 19200) a.1 a.2 W=
      posedKeySidePlane ((referenceBox5 true).toKeyData 19200) (σ a).1 (σ a).2 q.euclidean) :
    W '' referenceSolid5=keySolid l := by
  let k₀ := (referenceBox5 true).toKeyData 19200
  have hc : k₀.centre (Fin.last 4)=0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 4)=0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
    exact_mod_cast referenceBox5_height_pos true
  have hclosed : ∀ a ∈ keys5, IsClosed (keySolid a) := by
    intro a ha
    obtain ⟨r,hrbind⟩ := everyKey5_isCanonical a ha
    exact keySolid_isClosed_of_canonical a k₀ hc hr hh r hrbind
  have hid : q.euclidean.trans (IsometryEquiv.refl (Point 5)).toRealAffineIsometryEquiv=q.euclidean := by
    ext x
    rfl
  have heq := whole_key_coincidence_of_common_apex_side_planes k₀ hc hr hh referenceSideDistance5_pos
    0 keys5 T5 hclosed (fun a ha c hc hac => T5_keySolids_disjoint ha hc hac)
    (fun x hx => T5_frontier_key_or_carrier_plane hx) hl q hq (IsometryEquiv.refl (Point 5)) W
    (by
      intro i b
      change W '' keySideClosedFace k₀ i b ⊆ frontier (id '' _)
      rw [Set.image_id]
      exact hside i b) (by exact hapex) σ (by
      intro a
      rw [hid]
      exact hplanes a)
  change W '' referenceSolid5=id '' keySolid l at heq
  simpa only [Set.image_id] using heq

#print axioms T5_native_whole_key_coincidence_of_apex_side_planes

theorem T7_native_whole_key_coincidence_of_apex_side_planes
    (W : Point 7 ≃ᵃⁱ[ℝ] Point 7)
    (hside : ∀ i b, W '' keySideClosedFace ((referenceBox7 true).toKeyData 188160) i b ⊆ frontier T7)
    {l : KeyData 7} (hl : l ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid l=q.euclidean '' referenceSolid7)
    (hapex : W (rationalPoint ((referenceBox7 true).toKeyData 188160).apex)=
      q.euclidean (rationalPoint ((referenceBox7 true).toKeyData 188160).apex))
    (σ : (Fin 6 × Bool) ≃ (Fin 6 × Bool))
    (hplanes : ∀ a, posedKeySidePlane ((referenceBox7 true).toKeyData 188160) a.1 a.2 W=
      posedKeySidePlane ((referenceBox7 true).toKeyData 188160) (σ a).1 (σ a).2 q.euclidean) :
    W '' referenceSolid7=keySolid l := by
  let k₀ := (referenceBox7 true).toKeyData 188160
  have hc : k₀.centre (Fin.last 6)=0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 6)=0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
    exact_mod_cast referenceBox7_height_pos true
  have hclosed : ∀ a ∈ keys7, IsClosed (keySolid a) := by
    intro a ha
    obtain ⟨r,hrbind⟩ := everyKey7_isCanonical a ha
    exact keySolid_isClosed_of_canonical a k₀ hc hr hh r hrbind
  have hid : q.euclidean.trans (IsometryEquiv.refl (Point 7)).toRealAffineIsometryEquiv=q.euclidean := by
    ext x
    rfl
  have heq := whole_key_coincidence_of_common_apex_side_planes k₀ hc hr hh referenceSideDistance7_pos
    0 keys7 T7 hclosed (fun a ha c hc hac => T7_keySolids_disjoint ha hc hac)
    (fun x hx => T7_frontier_key_or_carrier_plane hx) hl q hq (IsometryEquiv.refl (Point 7)) W
    (by
      intro i b
      change W '' keySideClosedFace k₀ i b ⊆ frontier (id '' _)
      rw [Set.image_id]
      exact hside i b) (by exact hapex) σ (by
      intro a
      rw [hid]
      exact hplanes a)
  change W '' referenceSolid7=id '' keySolid l at heq
  simpa only [Set.image_id] using heq

#print axioms T7_native_whole_key_coincidence_of_apex_side_planes

end SparseMonotiles
