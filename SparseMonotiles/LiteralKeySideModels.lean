module

public import SparseMonotiles.LiteralKeyCreaseCompanions

@[expose] public section

/-! Exact oriented material germs on the relative interior of literal key sides.
The native/body membership and the actual transverse angle π are derived from
one zero side slack and strict positivity of every other exact key slack. -/
namespace SparseMonotiles
open Set Canonical

/-- The material orientation of one side of a bump or dent. -/
def sideMaterialHalfspace {X : Type*} (f : X → ℝ) (b : Bool) : Set X :=
  if b then {x | 0 ≤ f x} else {x | f x ≤ 0}

private theorem sideMaterial_image {d : ℕ} (G : Point d ≃ᵢ Point d)
    (f : Point d → ℝ) (b : Bool) :
    G '' sideMaterialHalfspace f b = sideMaterialHalfspace (fun x => f (G.symm x)) b := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    cases b <;> simpa [sideMaterialHalfspace] using hy
  · intro hx
    refine ⟨G.symm x,?_,G.apply_symm_apply x⟩
    cases b <;> simpa [sideMaterialHalfspace] using hx

theorem T5_literal_side_relativeInterior_germ
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i : Fin 4) (si : Bool) {p : Point 5}
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) p = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j p) :
    p ∈ T5 ∧ LocalSetEq p T5
      (sideMaterialHalfspace (posedHalfspaceSlack5 q (.inr (i,si))) k.bump) := by
  have hpk : p ∈ keySolid k := by
    apply (mem_keySolid5_iff_posed_halfspaces q hq p).mpr
    intro j
    by_cases hj : j = .inr (i,si)
    · subst j; exact hs.ge
    · exact (ho j hj).le
  have hlocal := (T5_local_merged_of_canonical_key hk q hq hpk).trans
    (localSetEq_closure_merged_single_side (posedHalfspaceSlack5 q) (.inl false)
      (.inr (i,si)) k.bump p (by simp) (continuous_posedHalfspaceSlack5 q)
      (ho _ (by simp)) (fun j _ hj => ho j hj)
      (closure_key_side_negative_posed ((referenceBox5 true).toKeyData 19200)
        (by change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ);
            exact_mod_cast referenceBox5_height_pos true) q i si))
  refine ⟨hlocal.mem_iff.mpr ?_,hlocal⟩
  cases k.bump <;> simp only [Bool.false_eq_true,if_false,if_true,Set.mem_setOf_eq,hs,le_refl]

theorem T5_copy_literal_side_relativeInterior_germ
    (G : Point 5 ≃ᵢ Point 5)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i : Fin 4) (si : Bool) {p : Point 5}
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) (G.symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j (G.symm p)) :
    p ∈ G '' T5 ∧ LocalSetEq p (G '' T5)
      (sideMaterialHalfspace (fun x => posedHalfspaceSlack5 q (.inr (i,si)) (G.symm x)) k.bump) := by
  obtain ⟨hmem,hlocal⟩ := T5_literal_side_relativeInterior_germ hk q hq i si hs ho
  refine ⟨⟨G.symm p,hmem,G.apply_symm_apply p⟩,?_⟩
  have h := hlocal.image_isometry G
  rw [G.apply_symm_apply,sideMaterial_image] at h
  exact h

theorem T5_literal_side_relativeInterior_sector
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i : Fin 4) (si : Bool)
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j ((g ⟨root,root.property.1⟩).symm p)) :
    LocalSetEq p (root : Set (Point 5))
      (sideMaterialHalfspace
        (fun x => posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm x)) k.bump) ∧
    SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) Real.pi ∧
    p ∈ frontier (root : Set (Point 5)) := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T5_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  have hlocal := (T5_copy_literal_side_relativeInterior_germ G hk q hq i si hs ho).2
  rw [← hg ⟨root,root.property.1⟩] at hlocal
  have hangle := key_facet_halfspace_normal_model_sector_angle ((referenceBox5 true).toKeyData 19200)
    referenceSideDistance5_pos e R hp (some (i,si)) (hzero (.inr (i,si)) hs) k.bump
    (hpart.2.2.1 root).2.1 (hpart.2.2.1 root).2.2 hlocal
  exact ⟨hlocal,hangle.1,mem_frontier_of_normal_sector R p hpart.2.1 hangle.1
    Real.pi_pos (by linarith [Real.pi_pos]) (hpart.2.2.1 root).2.2⟩

#print axioms T5_literal_side_relativeInterior_germ
#print axioms T5_copy_literal_side_relativeInterior_germ
#print axioms T5_literal_side_relativeInterior_sector

theorem T7_literal_side_relativeInterior_germ
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i : Fin 6) (si : Bool) {p : Point 7}
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) p = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j p) :
    p ∈ T7 ∧ LocalSetEq p T7
      (sideMaterialHalfspace (posedHalfspaceSlack7 q (.inr (i,si))) k.bump) := by
  have hpk : p ∈ keySolid k := by
    apply (mem_keySolid7_iff_posed_halfspaces q hq p).mpr
    intro j
    by_cases hj : j = .inr (i,si)
    · subst j; exact hs.ge
    · exact (ho j hj).le
  have hlocal := (T7_local_merged_of_canonical_key hk q hq hpk).trans
    (localSetEq_closure_merged_single_side (posedHalfspaceSlack7 q) (.inl false)
      (.inr (i,si)) k.bump p (by simp) (continuous_posedHalfspaceSlack7 q)
      (ho _ (by simp)) (fun j _ hj => ho j hj)
      (closure_key_side_negative_posed ((referenceBox7 true).toKeyData 188160)
        (by change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ);
            exact_mod_cast referenceBox7_height_pos true) q i si))
  refine ⟨hlocal.mem_iff.mpr ?_,hlocal⟩
  cases k.bump <;> simp only [Bool.false_eq_true,if_false,if_true,Set.mem_setOf_eq,hs,le_refl]

theorem T7_copy_literal_side_relativeInterior_germ
    (G : Point 7 ≃ᵢ Point 7)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i : Fin 6) (si : Bool) {p : Point 7}
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) (G.symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j (G.symm p)) :
    p ∈ G '' T7 ∧ LocalSetEq p (G '' T7)
      (sideMaterialHalfspace (fun x => posedHalfspaceSlack7 q (.inr (i,si)) (G.symm x)) k.bump) := by
  obtain ⟨hmem,hlocal⟩ := T7_literal_side_relativeInterior_germ hk q hq i si hs ho
  refine ⟨⟨G.symm p,hmem,G.apply_symm_apply p⟩,?_⟩
  have h := hlocal.image_isometry G
  rw [G.apply_symm_apply,sideMaterial_image] at h
  exact h

theorem T7_literal_side_relativeInterior_sector
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i : Fin 6) (si : Bool)
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j ((g ⟨root,root.property.1⟩).symm p)) :
    LocalSetEq p (root : Set (Point 7))
      (sideMaterialHalfspace
        (fun x => posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm x)) k.bump) ∧
    SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) Real.pi ∧
    p ∈ frontier (root : Set (Point 7)) := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T7_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  have hlocal := (T7_copy_literal_side_relativeInterior_germ G hk q hq i si hs ho).2
  rw [← hg ⟨root,root.property.1⟩] at hlocal
  have hangle := key_facet_halfspace_normal_model_sector_angle ((referenceBox7 true).toKeyData 188160)
    referenceSideDistance7_pos e R hp (some (i,si)) (hzero (.inr (i,si)) hs) k.bump
    (hpart.2.2.1 root).2.1 (hpart.2.2.1 root).2.2 hlocal
  exact ⟨hlocal,hangle.1,mem_frontier_of_normal_sector R p hpart.2.1 hangle.1
    Real.pi_pos (by linarith [Real.pi_pos]) (hpart.2.2.1 root).2.2⟩

#print axioms T7_literal_side_relativeInterior_germ
#print axioms T7_copy_literal_side_relativeInterior_germ
#print axioms T7_literal_side_relativeInterior_sector


private theorem zero_iff_of_halfspace_orientations {X E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : X → ℝ) (π : X → E) (n : E)
    (hpos : {x | 0 ≤ f x} = π ⁻¹' SectorAngleSum.normalHalfspace n)
    (hneg : {x | f x ≤ 0} = π ⁻¹' SectorAngleSum.normalHalfspace (-n)) :
    ∀ x, f x = 0 ↔ inner (𝕜 := ℝ) n (π x) = 0 := by
  intro x
  have hp := Set.ext_iff.mp hpos x
  have hn := Set.ext_iff.mp hneg x
  simp only [Set.mem_setOf_eq,Set.mem_preimage,SectorAngleSum.normalHalfspace,
    inner_neg_left,neg_nonneg] at hp hn
  constructor
  · intro h
    exact le_antisymm (hn.mp h.le) (hp.mp h.ge)
  · intro h
    exact le_antisymm (hn.mpr h.le) (hp.mpr h.ge)

theorem T5_literal_side_relativeInterior_normal
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i : Fin 4) (si : Bool)
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j ((g ⟨root,root.property.1⟩).symm p)) :
    ∃ N : R.directionᗮ, N ≠ 0 ∧
      T5IncidentNormalCone g R p root = SectorAngleSum.normalHalfspace N ∧
      (∀ x, posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm x) = 0 ↔
        inner (𝕜 := ℝ) N (ridgeNormalProjection R p x) = 0) := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  let f : Point 5 → ℝ := fun x => posedHalfspaceSlack5 q (.inr (i,si)) (G.symm x)
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T5_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  obtain ⟨N,_,hN,hpos,hneg⟩ := key_facet_normal_space_adapter
    ((referenceBox5 true).toKeyData 19200) referenceSideDistance5_pos e R hp
    (some (i,si)) (hzero (.inr (i,si)) hs)
  have hpos' : {x | 0 ≤ f x} = ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace N := hpos
  have hneg' : {x | f x ≤ 0} = ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace (-N) := hneg
  have hz := zero_iff_of_halfspace_orientations f (ridgeNormalProjection R p) N hpos' hneg'
  have hlocal : LocalSetEq p (root : Set (Point 5)) (sideMaterialHalfspace f k.bump) :=
    (T5_literal_side_relativeInterior_sector ht R hp hcodim g hg hactive root hk q hq i si hs ho).1
  cases hb : k.bump
  · have hQ : SectorAngleSum.HasSectorAngle (SectorAngleSum.normalHalfspace (-N)) Real.pi :=
      .halfplane (-N) (neg_ne_zero.mpr hN) rfl
    have hl : LocalSetEq p (root : Set (Point 5))
        (ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace (-N)) := by
      simpa only [sideMaterialHalfspace,hb,Bool.false_eq_true,if_false,hneg'] using hlocal
    refine ⟨-N,neg_ne_zero.mpr hN,
      normalCones_eq_of_localSetEq R p (hpart.2.2.1 root).2.1 hQ.positive
        ((hpart.2.2.1 root).2.2.symm.trans hl),?_⟩
    intro x
    simpa only [inner_neg_left,neg_eq_zero] using hz x
  · have hQ : SectorAngleSum.HasSectorAngle (SectorAngleSum.normalHalfspace N) Real.pi :=
      .halfplane N hN rfl
    have hl : LocalSetEq p (root : Set (Point 5))
        (ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace N) := by
      simpa only [sideMaterialHalfspace,hb,if_true,hpos'] using hlocal
    exact ⟨N,hN,normalCones_eq_of_localSetEq R p (hpart.2.2.1 root).2.1 hQ.positive
      ((hpart.2.2.1 root).2.2.symm.trans hl),hz⟩

#print axioms T5_literal_side_relativeInterior_normal
theorem T7_literal_side_relativeInterior_normal
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i : Fin 6) (si : Bool)
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j ((g ⟨root,root.property.1⟩).symm p)) :
    ∃ N : R.directionᗮ, N ≠ 0 ∧
      T7IncidentNormalCone g R p root = SectorAngleSum.normalHalfspace N ∧
      (∀ x, posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm x) = 0 ↔
        inner (𝕜 := ℝ) N (ridgeNormalProjection R p x) = 0) := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  let f : Point 7 → ℝ := fun x => posedHalfspaceSlack7 q (.inr (i,si)) (G.symm x)
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T7_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  obtain ⟨N,_,hN,hpos,hneg⟩ := key_facet_normal_space_adapter
    ((referenceBox7 true).toKeyData 188160) referenceSideDistance7_pos e R hp
    (some (i,si)) (hzero (.inr (i,si)) hs)
  have hpos' : {x | 0 ≤ f x} = ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace N := hpos
  have hneg' : {x | f x ≤ 0} = ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace (-N) := hneg
  have hz := zero_iff_of_halfspace_orientations f (ridgeNormalProjection R p) N hpos' hneg'
  have hlocal : LocalSetEq p (root : Set (Point 7)) (sideMaterialHalfspace f k.bump) :=
    (T7_literal_side_relativeInterior_sector ht R hp hcodim g hg hactive root hk q hq i si hs ho).1
  cases hb : k.bump
  · have hQ : SectorAngleSum.HasSectorAngle (SectorAngleSum.normalHalfspace (-N)) Real.pi :=
      .halfplane (-N) (neg_ne_zero.mpr hN) rfl
    have hl : LocalSetEq p (root : Set (Point 7))
        (ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace (-N)) := by
      simpa only [sideMaterialHalfspace,hb,Bool.false_eq_true,if_false,hneg'] using hlocal
    refine ⟨-N,neg_ne_zero.mpr hN,
      normalCones_eq_of_localSetEq R p (hpart.2.2.1 root).2.1 hQ.positive
        ((hpart.2.2.1 root).2.2.symm.trans hl),?_⟩
    intro x
    simpa only [inner_neg_left,neg_eq_zero] using hz x
  · have hQ : SectorAngleSum.HasSectorAngle (SectorAngleSum.normalHalfspace N) Real.pi :=
      .halfplane N hN rfl
    have hl : LocalSetEq p (root : Set (Point 7))
        (ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace N) := by
      simpa only [sideMaterialHalfspace,hb,if_true,hpos'] using hlocal
    exact ⟨N,hN,normalCones_eq_of_localSetEq R p (hpart.2.2.1 root).2.1 hQ.positive
      ((hpart.2.2.1 root).2.2.symm.trans hl),hz⟩

#print axioms T7_literal_side_relativeInterior_normal
end SparseMonotiles
