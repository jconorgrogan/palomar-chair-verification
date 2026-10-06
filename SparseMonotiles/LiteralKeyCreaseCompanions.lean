module

public import SparseMonotiles.LiteralKeyCreaseModels
public import SparseMonotiles.PhysicalSectorConsequences

@[expose] public section

/-! # Exact K2 incident count at literal key creases
The root angle, its boundary status, and every neighboring sector are derived.
Inputs are the actual tiling, fixed-frame genericity, and the explicit literal
crease equations with strict omitted inequalities.
-/
namespace SparseMonotiles
open Set Canonical

private theorem isometry_image_as_inverse_preimage {d : ℕ}
    (G : Point d ≃ᵢ Point d) (M : Set (Point d)) :
    G '' M = G.symm ⁻¹' M := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [Set.mem_preimage,G.symm_apply_apply] using hy
  · intro hx
    exact ⟨G.symm x,hx,G.apply_symm_apply x⟩

theorem T5_literal_base_side_crease_exactly_two_incident
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
    (hb : posedHalfspaceSlack5 q (.inl false) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inl false → j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j ((g ⟨root,root.property.1⟩).symm p)) :
    Nat.card (incidentTiles tiles p) = 2 := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T5_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  have hlocal := (T5_literal_base_side_crease_germ hk q hq i si hb hs ho).image_isometry G
  simp only [G, IsometryEquiv.apply_symm_apply] at hlocal
  change LocalSetEq p (G '' T5)
    (G '' closedBaseSideWedge (posedHalfspaceSlack5 q) (.inl false) (.inr (i,si)) k.bump) at hlocal
  rw [isometry_image_as_inverse_preimage G
    (closedBaseSideWedge (posedHalfspaceSlack5 q) (.inl false) (.inr (i,si)) k.bump)] at hlocal
  have heq : G.symm ⁻¹' closedBaseSideWedge (posedHalfspaceSlack5 q) (.inl false) (.inr (i,si)) k.bump =
      closedBaseSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox5 true).toKeyData 19200) a (e x))
        (.inl false) (.inr (i,si)) k.bump := by
    cases k.bump <;> rfl
  rw [heq] at hlocal
  have hlocal' : LocalSetEq p (root : Set (Point 5))
      (closedBaseSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox5 true).toKeyData 19200) a (e x))
        (.inl false) (.inr (i,si)) k.bump) := by
    simpa only [G, ← hg ⟨root,root.property.1⟩] using hlocal
  have hangle := key_base_side_normal_model_sector_angle ((referenceBox5 true).toKeyData 19200)
    referenceSideDistance5_pos e R hp i si (referenceSideSlope5_bounds i si)
    (hzero (.inl false) hb) (hzero (.inr (i,si)) hs) k.bump
    (hpart.2.2.1 root).2.1 (hpart.2.2.1 root).2.2 hlocal'
  exact T5_key_root_incident_card_two ht R hp hcodim g hg hactive root
    hangle.1.1 hangle.2.1 hangle.2.2 (by cases k.bump <;> simp)

#print axioms T5_literal_base_side_crease_exactly_two_incident

theorem T5_literal_side_side_crease_exactly_two_incident
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
    (i j : Fin 4) (hij : i ≠ j) (si sj : Bool)
    (hi : posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (hj : posedHalfspaceSlack5 q (.inr (j,sj)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 4, l ≠ .inr (i,si) → l ≠ .inr (j,sj) →
      0 < posedHalfspaceSlack5 q l ((g ⟨root,root.property.1⟩).symm p)) :
    Nat.card (incidentTiles tiles p) = 2 := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T5_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  have hlocal := (T5_literal_side_side_crease_germ hk q hq i j si sj hi hj ho).image_isometry G
  simp only [G, IsometryEquiv.apply_symm_apply] at hlocal
  change LocalSetEq p (G '' T5)
    (G '' closedSideSideWedge (posedHalfspaceSlack5 q) (.inr (i,si)) (.inr (j,sj)) k.bump) at hlocal
  rw [isometry_image_as_inverse_preimage G
    (closedSideSideWedge (posedHalfspaceSlack5 q) (.inr (i,si)) (.inr (j,sj)) k.bump)] at hlocal
  have heq : G.symm ⁻¹' closedSideSideWedge (posedHalfspaceSlack5 q) (.inr (i,si)) (.inr (j,sj)) k.bump =
      closedSideSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox5 true).toKeyData 19200) a (e x))
        (.inr (i,si)) (.inr (j,sj)) k.bump := by
    cases k.bump <;> rfl
  rw [heq] at hlocal
  have hlocal' : LocalSetEq p (root : Set (Point 5))
      (closedSideSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox5 true).toKeyData 19200) a (e x))
        (.inr (i,si)) (.inr (j,sj)) k.bump) := by
    simpa only [G, ← hg ⟨root,root.property.1⟩] using hlocal
  have hangle := key_side_side_normal_model_sector_angle ((referenceBox5 true).toKeyData 19200)
    referenceSideDistance5_pos e R hp i j hij si sj (referenceSideSlope5_bounds i si) (referenceSideSlope5_bounds j sj)
    (hzero (.inr (i,si)) hi) (hzero (.inr (j,sj)) hj) k.bump
    (hpart.2.2.1 root).2.1 (hpart.2.2.1 root).2.2 hlocal'
  exact T5_key_root_incident_card_two ht R hp hcodim g hg hactive root
    hangle.1.1 hangle.2.1 hangle.2.2 (by cases k.bump <;> simp)

#print axioms T5_literal_side_side_crease_exactly_two_incident

theorem T7_literal_base_side_crease_exactly_two_incident
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
    (hb : posedHalfspaceSlack7 q (.inl false) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inl false → j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j ((g ⟨root,root.property.1⟩).symm p)) :
    Nat.card (incidentTiles tiles p) = 2 := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T7_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  have hlocal := (T7_literal_base_side_crease_germ hk q hq i si hb hs ho).image_isometry G
  simp only [G, IsometryEquiv.apply_symm_apply] at hlocal
  change LocalSetEq p (G '' T7)
    (G '' closedBaseSideWedge (posedHalfspaceSlack7 q) (.inl false) (.inr (i,si)) k.bump) at hlocal
  rw [isometry_image_as_inverse_preimage G
    (closedBaseSideWedge (posedHalfspaceSlack7 q) (.inl false) (.inr (i,si)) k.bump)] at hlocal
  have heq : G.symm ⁻¹' closedBaseSideWedge (posedHalfspaceSlack7 q) (.inl false) (.inr (i,si)) k.bump =
      closedBaseSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox7 true).toKeyData 188160) a (e x))
        (.inl false) (.inr (i,si)) k.bump := by
    cases k.bump <;> rfl
  rw [heq] at hlocal
  have hlocal' : LocalSetEq p (root : Set (Point 7))
      (closedBaseSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox7 true).toKeyData 188160) a (e x))
        (.inl false) (.inr (i,si)) k.bump) := by
    simpa only [G, ← hg ⟨root,root.property.1⟩] using hlocal
  have hangle := key_base_side_normal_model_sector_angle ((referenceBox7 true).toKeyData 188160)
    referenceSideDistance7_pos e R hp i si (referenceSideSlope7_bounds i si)
    (hzero (.inl false) hb) (hzero (.inr (i,si)) hs) k.bump
    (hpart.2.2.1 root).2.1 (hpart.2.2.1 root).2.2 hlocal'
  exact T7_key_root_incident_card_two ht R hp hcodim g hg hactive root
    hangle.1.1 hangle.2.1 hangle.2.2 (by cases k.bump <;> simp)

#print axioms T7_literal_base_side_crease_exactly_two_incident

theorem T7_literal_side_side_crease_exactly_two_incident
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
    (i j : Fin 6) (hij : i ≠ j) (si sj : Bool)
    (hi : posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (hj : posedHalfspaceSlack7 q (.inr (j,sj)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 6, l ≠ .inr (i,si) → l ≠ .inr (j,sj) →
      0 < posedHalfspaceSlack7 q l ((g ⟨root,root.property.1⟩).symm p)) :
    Nat.card (incidentTiles tiles p) = 2 := by
  let G := g ⟨root,root.property.1⟩
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hzero := T7_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  have hlocal := (T7_literal_side_side_crease_germ hk q hq i j si sj hi hj ho).image_isometry G
  simp only [G, IsometryEquiv.apply_symm_apply] at hlocal
  change LocalSetEq p (G '' T7)
    (G '' closedSideSideWedge (posedHalfspaceSlack7 q) (.inr (i,si)) (.inr (j,sj)) k.bump) at hlocal
  rw [isometry_image_as_inverse_preimage G
    (closedSideSideWedge (posedHalfspaceSlack7 q) (.inr (i,si)) (.inr (j,sj)) k.bump)] at hlocal
  have heq : G.symm ⁻¹' closedSideSideWedge (posedHalfspaceSlack7 q) (.inr (i,si)) (.inr (j,sj)) k.bump =
      closedSideSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox7 true).toKeyData 188160) a (e x))
        (.inr (i,si)) (.inr (j,sj)) k.bump := by
    cases k.bump <;> rfl
  rw [heq] at hlocal
  have hlocal' : LocalSetEq p (root : Set (Point 7))
      (closedSideSideWedge (fun a x => keyPyramidHalfspaceSlack ((referenceBox7 true).toKeyData 188160) a (e x))
        (.inr (i,si)) (.inr (j,sj)) k.bump) := by
    simpa only [G, ← hg ⟨root,root.property.1⟩] using hlocal
  have hangle := key_side_side_normal_model_sector_angle ((referenceBox7 true).toKeyData 188160)
    referenceSideDistance7_pos e R hp i j hij si sj (referenceSideSlope7_bounds i si) (referenceSideSlope7_bounds j sj)
    (hzero (.inr (i,si)) hi) (hzero (.inr (j,sj)) hj) k.bump
    (hpart.2.2.1 root).2.1 (hpart.2.2.1 root).2.2 hlocal'
  exact T7_key_root_incident_card_two ht R hp hcodim g hg hactive root
    hangle.1.1 hangle.2.1 hangle.2.2 (by cases k.bump <;> simp)

#print axioms T7_literal_side_side_crease_exactly_two_incident

end SparseMonotiles
