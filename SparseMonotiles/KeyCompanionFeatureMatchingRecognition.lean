module

public import SparseMonotiles.KeyCompanionFeatureMatchingNativeSolid
public import SparseMonotiles.KeyCompanionFeatureMatchingApexCount
public import SparseMonotiles.KeyCompanionBoundaryPlaneInventory

@[expose] public section

/-! # Actual whole-key recognition from closed-side boundary coverage
The apex and every side plane are derived from the actual local boundary
inventory. No feature correspondence, carrier exclusion, or base match is assumed.
-/
namespace SparseMonotiles
open Set Filter Canonical
open scoped Topology

theorem T5_boundary_side_cover_matches_apex_side_planes
    (W : Point 5 ≃ᵃⁱ[ℝ] Point 5)
    (hside : ∀ i b, W '' keySideClosedFace ((referenceBox5 true).toKeyData 19200) i b ⊆ frontier T5) :
    ∃ l ∈ keys5, ∃ q : Contact.Pose 5,
      keySolid l=q.euclidean '' referenceSolid5 ∧
      W (rationalPoint ((referenceBox5 true).toKeyData 19200).apex)=
        q.euclidean (rationalPoint ((referenceBox5 true).toKeyData 19200).apex) ∧
      ∃ σ : (Fin 4 × Bool) ≃ (Fin 4 × Bool), ∀ a,
        posedKeySidePlane ((referenceBox5 true).toKeyData 19200) a.1 a.2 W=
        posedKeySidePlane ((referenceBox5 true).toKeyData 19200) (σ a).1 (σ a).2 q.euclidean := by
  let k₀ := (referenceBox5 true).toKeyData 19200
  have hc : k₀.centre (Fin.last 4)=0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 4)=0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
    exact_mod_cast referenceBox5_height_pos true
  have hd : ∀ i b, 0 < keySideDistance k₀ i b := referenceSideDistance5_pos
  have hp : W (rationalPoint k₀.apex) ∈ frontier T5 :=
    hside 0 false (posed_key_apex_mem_closed_side k₀ 0 false W)
  rcases T5_boundary_local_small_or_key_apex hp with hsmall | ⟨l,hl,q,hq,ha,hplanes⟩
  · exact False.elim ((key_apex_not_small_local_boundary_cover (by omega : 4+1 < 2*4)
      k₀ hc hr hh hd W T5 hside) hsmall)
  · obtain ⟨U,hUc,hU,hpU⟩ := mem_nhds_iff.mp hplanes
    have hcover : ∀ x ∈ U, x ∈ frontier T5 → ∃ a : Fin 4 × Bool,
        x ∈ posedKeySidePlane k₀ a.1 a.2 q.euclidean := by
      intro x hx hf
      obtain ⟨i,b,hib⟩ := hUc hx hf
      refine ⟨(i,b),(mem_posedKeySidePlane_iff k₀ i b q.euclidean x).mpr ?_⟩
      exact (mem_keySideAffinePlane_iff k₀ hd i b _).mpr hib
    obtain ⟨σ,hσ⟩ := key_apex_local_boundary_side_plane_equiv k₀ k₀ hc hr hh hd
      W q.euclidean (frontier T5) hside hU hpU hcover
    exact ⟨l,hl,q,hq,ha,σ,hσ⟩

/-- A full canonical key side surface in the actual body boundary is exactly
one of that body's literal key solids. All feature matching is concluded. -/
theorem T5_boundary_side_cover_recognizes_whole_key
    (W : Point 5 ≃ᵃⁱ[ℝ] Point 5)
    (hside : ∀ i b, W '' keySideClosedFace ((referenceBox5 true).toKeyData 19200) i b ⊆ frontier T5) :
    ∃ l ∈ keys5, ∃ q : Contact.Pose 5,
      keySolid l=q.euclidean '' referenceSolid5 ∧ W '' referenceSolid5=keySolid l := by
  obtain ⟨l,hl,q,hq,ha,σ,hplanes⟩ := T5_boundary_side_cover_matches_apex_side_planes W hside
  exact ⟨l,hl,q,hq,T5_native_whole_key_coincidence_of_apex_side_planes W hside hl q hq ha σ hplanes⟩

#print axioms T5_boundary_side_cover_matches_apex_side_planes
#print axioms T5_boundary_side_cover_recognizes_whole_key

theorem T7_boundary_side_cover_matches_apex_side_planes
    (W : Point 7 ≃ᵃⁱ[ℝ] Point 7)
    (hside : ∀ i b, W '' keySideClosedFace ((referenceBox7 true).toKeyData 188160) i b ⊆ frontier T7) :
    ∃ l ∈ keys7, ∃ q : Contact.Pose 7,
      keySolid l=q.euclidean '' referenceSolid7 ∧
      W (rationalPoint ((referenceBox7 true).toKeyData 188160).apex)=
        q.euclidean (rationalPoint ((referenceBox7 true).toKeyData 188160).apex) ∧
      ∃ σ : (Fin 6 × Bool) ≃ (Fin 6 × Bool), ∀ a,
        posedKeySidePlane ((referenceBox7 true).toKeyData 188160) a.1 a.2 W=
        posedKeySidePlane ((referenceBox7 true).toKeyData 188160) (σ a).1 (σ a).2 q.euclidean := by
  let k₀ := (referenceBox7 true).toKeyData 188160
  have hc : k₀.centre (Fin.last 6)=0 := by simp [k₀,Fin.last]
  have hr : k₀.radius (Fin.last 6)=0 := by simp [k₀,Fin.last]
  have hh : 0 < keyPyramidHeight k₀ := by
    change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
    exact_mod_cast referenceBox7_height_pos true
  have hd : ∀ i b, 0 < keySideDistance k₀ i b := referenceSideDistance7_pos
  have hp : W (rationalPoint k₀.apex) ∈ frontier T7 :=
    hside 0 false (posed_key_apex_mem_closed_side k₀ 0 false W)
  rcases T7_boundary_local_small_or_key_apex hp with hsmall | ⟨l,hl,q,hq,ha,hplanes⟩
  · exact False.elim ((key_apex_not_small_local_boundary_cover (by omega : 6+1 < 2*6)
      k₀ hc hr hh hd W T7 hside) hsmall)
  · obtain ⟨U,hUc,hU,hpU⟩ := mem_nhds_iff.mp hplanes
    have hcover : ∀ x ∈ U, x ∈ frontier T7 → ∃ a : Fin 6 × Bool,
        x ∈ posedKeySidePlane k₀ a.1 a.2 q.euclidean := by
      intro x hx hf
      obtain ⟨i,b,hib⟩ := hUc hx hf
      refine ⟨(i,b),(mem_posedKeySidePlane_iff k₀ i b q.euclidean x).mpr ?_⟩
      exact (mem_keySideAffinePlane_iff k₀ hd i b _).mpr hib
    obtain ⟨σ,hσ⟩ := key_apex_local_boundary_side_plane_equiv k₀ k₀ hc hr hh hd
      W q.euclidean (frontier T7) hside hU hpU hcover
    exact ⟨l,hl,q,hq,ha,σ,hσ⟩

/-- A full canonical key side surface in the actual body boundary is exactly
one of that body's literal key solids. All feature matching is concluded. -/
theorem T7_boundary_side_cover_recognizes_whole_key
    (W : Point 7 ≃ᵃⁱ[ℝ] Point 7)
    (hside : ∀ i b, W '' keySideClosedFace ((referenceBox7 true).toKeyData 188160) i b ⊆ frontier T7) :
    ∃ l ∈ keys7, ∃ q : Contact.Pose 7,
      keySolid l=q.euclidean '' referenceSolid7 ∧ W '' referenceSolid7=keySolid l := by
  obtain ⟨l,hl,q,hq,ha,σ,hplanes⟩ := T7_boundary_side_cover_matches_apex_side_planes W hside
  exact ⟨l,hl,q,hq,T7_native_whole_key_coincidence_of_apex_side_planes W hside hl q hq ha σ hplanes⟩

#print axioms T7_boundary_side_cover_matches_apex_side_planes
#print axioms T7_boundary_side_cover_recognizes_whole_key

end SparseMonotiles
