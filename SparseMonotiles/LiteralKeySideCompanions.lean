module

public import SparseMonotiles.LiteralKeySideModels
public import SparseMonotiles.TwoTileHalfspaceCompanion

@[expose] public section

/-! The actual two-incident conclusion identifies the companion with the fixed
opposite oriented ambient side halfspace, ready for face continuation. -/
namespace SparseMonotiles
open Set Canonical SectorAngleSum

theorem T5_two_incident_literal_side_opposite_germ
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
      0 < posedHalfspaceSlack5 q j ((g ⟨root,root.property.1⟩).symm p))
    (hcard : Nat.card (incidentTiles tiles p) = 2) :
    ∃ B : incidentTiles tiles p, B ≠ root ∧
      LocalSetEq p (B : Set (Point 5))
        (sideMaterialHalfspace
          (fun x => posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm x)) (!k.bump)) := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  let f : Point 5 → ℝ := fun x => posedHalfspaceSlack5 q (.inr (i,si)) (G.symm x)
  have hzero := T5_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  obtain ⟨nR,_,hn,hpos,hneg⟩ := key_facet_normal_space_adapter
    ((referenceBox5 true).toKeyData 19200) referenceSideDistance5_pos e R hp
    (some (i,si)) (hzero (.inr (i,si)) hs)
  have hpos' : sideMaterialHalfspace f true = ridgeNormalProjection R p ⁻¹' normalHalfspace nR := hpos
  have hneg' : sideMaterialHalfspace f false = ridgeNormalProjection R p ⁻¹' normalHalfspace (-nR) := hneg
  have hlocal : LocalSetEq p (root : Set (Point 5)) (sideMaterialHalfspace f k.bump) :=
    (T5_literal_side_relativeInterior_sector ht R hp hcodim g hg hactive root hk q hq i si hs ho).1
  change ∃ B : incidentTiles tiles p, B ≠ root ∧
    LocalSetEq p (B : Set (Point 5)) (sideMaterialHalfspace f (!k.bump))
  cases hb : k.bump
  · rw [hb,hneg'] at hlocal
    obtain ⟨B,hB,hmodel⟩ := T5_two_incident_opposite_halfspace_germ ht R hp hcodim
      g hg hactive root (-nR) (neg_ne_zero.mpr hn) hlocal hcard
    refine ⟨B,hB,?_⟩
    rw [Bool.not_false,hpos']
    simpa only [neg_neg] using hmodel
  · rw [hb,hpos'] at hlocal
    obtain ⟨B,hB,hmodel⟩ := T5_two_incident_opposite_halfspace_germ ht R hp hcodim
      g hg hactive root nR hn hlocal hcard
    refine ⟨B,hB,?_⟩
    rw [Bool.not_true,hneg']
    exact hmodel

#print axioms T5_two_incident_literal_side_opposite_germ

theorem T7_two_incident_literal_side_opposite_germ
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
      0 < posedHalfspaceSlack7 q j ((g ⟨root,root.property.1⟩).symm p))
    (hcard : Nat.card (incidentTiles tiles p) = 2) :
    ∃ B : incidentTiles tiles p, B ≠ root ∧
      LocalSetEq p (B : Set (Point 7))
        (sideMaterialHalfspace
          (fun x => posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm x)) (!k.bump)) := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  let f : Point 7 → ℝ := fun x => posedHalfspaceSlack7 q (.inr (i,si)) (G.symm x)
  have hzero := T7_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  obtain ⟨nR,_,hn,hpos,hneg⟩ := key_facet_normal_space_adapter
    ((referenceBox7 true).toKeyData 188160) referenceSideDistance7_pos e R hp
    (some (i,si)) (hzero (.inr (i,si)) hs)
  have hpos' : sideMaterialHalfspace f true = ridgeNormalProjection R p ⁻¹' normalHalfspace nR := hpos
  have hneg' : sideMaterialHalfspace f false = ridgeNormalProjection R p ⁻¹' normalHalfspace (-nR) := hneg
  have hlocal : LocalSetEq p (root : Set (Point 7)) (sideMaterialHalfspace f k.bump) :=
    (T7_literal_side_relativeInterior_sector ht R hp hcodim g hg hactive root hk q hq i si hs ho).1
  change ∃ B : incidentTiles tiles p, B ≠ root ∧
    LocalSetEq p (B : Set (Point 7)) (sideMaterialHalfspace f (!k.bump))
  cases hb : k.bump
  · rw [hb,hneg'] at hlocal
    obtain ⟨B,hB,hmodel⟩ := T7_two_incident_opposite_halfspace_germ ht R hp hcodim
      g hg hactive root (-nR) (neg_ne_zero.mpr hn) hlocal hcard
    refine ⟨B,hB,?_⟩
    rw [Bool.not_false,hpos']
    simpa only [neg_neg] using hmodel
  · rw [hb,hpos'] at hlocal
    obtain ⟨B,hB,hmodel⟩ := T7_two_incident_opposite_halfspace_germ ht R hp hcodim
      g hg hactive root nR hn hlocal hcard
    refine ⟨B,hB,?_⟩
    rw [Bool.not_true,hneg']
    exact hmodel

#print axioms T7_two_incident_literal_side_opposite_germ
end SparseMonotiles
