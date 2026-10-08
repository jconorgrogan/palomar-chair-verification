module

public import SparseMonotiles.StripCreaseCrossingWorldBarrier
public import SparseMonotiles.StripCreaseCrossingWorldNormals
public import SparseMonotiles.StripCreaseCrossingThreeSectors
public import SparseMonotiles.LiteralKeySideModels

@[expose] public section

/-! # Eliminate the actual three-sector seam on each literal key side
Every exposed facet, supporting-plane alignment, unit strip, new generic
crease and physical incident tile is derived before applying the contradiction.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_key_side_no_aligned_seam_normal
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (A B : tiles) (hBA : B ≠ A)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i : Fin 4) (si : Bool) {p : Point 5}
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm p) = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 4, l ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q l ((g A).symm p))
    (R : AffineSubspace ℝ (Point 5)) (N : R.directionᗮ)
    (hzero : ∀ x, posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm x) = 0 ↔
      inner (𝕜 := ℝ) N (ridgeNormalProjection R p x) = 0)
    {S : Set R.directionᗮ} (D : CarrierSeamGeometry (g B) R p S)
    {c : ℝ} (hc : 0 < c) (hN : N = (-c) • D.normal₁) : False := by
  let f : Contact.Facet 5 := {cell := D.cell,axis := D.first,positive := !D.positive₁}
  let z : Point 5 := q.euclidean.symm ((g A).symm p)
  have hz : g A (q.euclidean z) = p := by simp [z]
  have hlevel : (f.gridFacet.anchor f.axis : ℝ) = (g B).symm p D.first := by
    rw [Contact.Facet.gridFacet_anchor_axis]
    change ((D.cell D.first + if !D.positive₁ then 1 else 0 : ℤ) : ℝ) = _
    rw [D.endpoint₁]
    cases D.positive₁ <;> simp
  refine T5_no_aligned_carrier_edge_on_key_side ht g hg A B hBA hk q hq i si
    (p := z) hs ho f D.owner D.exposed₁ D.second D.different.symm (!D.positive₂) ?_ ?_ ?_
  · intro x
    have hkey : referenceHalfspaceSlack5 (.inr (i,si)) x =
        posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm (g A (q.euclidean x))) := by
      simp [posedHalfspaceSlack5]
    rw [hkey,hzero]
    have hline := Set.ext_iff.mp (normal_zero_planes_eq_of_negative_multiple hc hN)
      (ridgeNormalProjection R p (g A (q.euclidean x)))
    change inner (𝕜 := ℝ) N _ = 0 ↔ inner (𝕜 := ℝ) D.normal₁ _ = 0 at hline
    exact hline.trans ((D.plane₁ _).trans (by rw [hlevel]))
  · change (g B).symm (g A (q.euclidean z)) D.second =
      (D.cell D.second : ℝ)+(if !D.positive₂ then 1 else 0)
    rw [hz,D.endpoint₂]
    cases D.positive₂ <;> simp
  · intro a hai haj
    simpa only [hz] using D.other_strict a hai haj

#print axioms T5_key_side_no_aligned_seam_normal

theorem T7_key_side_no_aligned_seam_normal
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (A B : tiles) (hBA : B ≠ A)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i : Fin 6) (si : Bool) {p : Point 7}
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm p) = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 6, l ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q l ((g A).symm p))
    (R : AffineSubspace ℝ (Point 7)) (N : R.directionᗮ)
    (hzero : ∀ x, posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm x) = 0 ↔
      inner (𝕜 := ℝ) N (ridgeNormalProjection R p x) = 0)
    {S : Set R.directionᗮ} (D : CarrierSeamGeometry (g B) R p S)
    {c : ℝ} (hc : 0 < c) (hN : N = (-c) • D.normal₁) : False := by
  let f : Contact.Facet 7 := {cell := D.cell,axis := D.first,positive := !D.positive₁}
  let z : Point 7 := q.euclidean.symm ((g A).symm p)
  have hz : g A (q.euclidean z) = p := by simp [z]
  have hlevel : (f.gridFacet.anchor f.axis : ℝ) = (g B).symm p D.first := by
    rw [Contact.Facet.gridFacet_anchor_axis]
    change ((D.cell D.first + if !D.positive₁ then 1 else 0 : ℤ) : ℝ) = _
    rw [D.endpoint₁]
    cases D.positive₁ <;> simp
  refine T7_no_aligned_carrier_edge_on_key_side ht g hg A B hBA hk q hq i si
    (p := z) hs ho f D.owner D.exposed₁ D.second D.different.symm (!D.positive₂) ?_ ?_ ?_
  · intro x
    have hkey : referenceHalfspaceSlack7 (.inr (i,si)) x =
        posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm (g A (q.euclidean x))) := by
      simp [posedHalfspaceSlack7]
    rw [hkey,hzero]
    have hline := Set.ext_iff.mp (normal_zero_planes_eq_of_negative_multiple hc hN)
      (ridgeNormalProjection R p (g A (q.euclidean x)))
    change inner (𝕜 := ℝ) N _ = 0 ↔ inner (𝕜 := ℝ) D.normal₁ _ = 0 at hline
    exact hline.trans ((D.plane₁ _).trans (by rw [hlevel]))
  · change (g B).symm (g A (q.euclidean z)) D.second =
      (D.cell D.second : ℝ)+(if !D.positive₂ then 1 else 0)
    rw [hz,D.endpoint₂]
    cases D.positive₂ <;> simp
  · intro a hai haj
    simpa only [hz] using D.other_strict a hai haj

#print axioms T7_key_side_no_aligned_seam_normal


/-- Complete pointwise K1 incident count at the relative interior of a
literal key side. The actual three-sector seam alternative is contradicted
in world coordinates using the full fixed physical plane inventory. -/
theorem T5_literal_side_generic_exactly_two_incident
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction+2=5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5) (i : Fin 4) (si : Bool)
    (hs : posedHalfspaceSlack5 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack5 q j ((g ⟨root,root.property.1⟩).symm p)) :
    Nat.card (incidentTiles tiles p) = 2 := by
  classical
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  obtain ⟨hrootlocal,hrootangle,hrootboundary⟩ :=
    T5_literal_side_relativeInterior_sector ht R hp hcodim g hg hactive root hk q hq i si hs ho
  rcases T5_generic_flat_root_incident_count ht R hp hcodim g hg hactive root hrootangle hrootboundary with
    htwo | hthree
  · exact htwo
  · exfalso
    letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
    obtain ⟨width,hwroot,hshape,hInv,_⟩ := T5_generic_root_sector_partition
      ht R hp hcodim g hg hactive root hrootangle (Or.inr (Or.inl rfl)) hrootboundary
    obtain ⟨B,C,hBne,hCne,hBC,hall,hBangle,hCangle⟩ := flat_partition_three_actual_companions
      hpart.2.1 (T5IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2
      root hwroot hInv (by simpa only [Nat.card_eq_fintype_card] using hthree)
    obtain ⟨N,hN,hrootEq,hzero⟩ := T5_literal_side_relativeInterior_normal
      ht R hp hcodim g hg hactive root hk q hq i si hs ho
    have hboundary := ht.incident_mem_frontier_of_root_sector T5_isCompact R p root hrootangle
      (hpart.2.2.1 root).2.2 hrootboundary
    obtain ⟨DB⟩ := T5_right_angle_carrier_seam_geometry (g ⟨B,B.property.1⟩) R hp hcodim
      (hactive B) (hpart.2.2.1 B).2.1
      (by simpa only [← hg ⟨B,B.property.1⟩] using (hpart.2.2.1 B).2.2)
      (by simpa only [← hg ⟨B,B.property.1⟩] using hboundary B) hBangle
    obtain ⟨DC⟩ := T5_right_angle_carrier_seam_geometry (g ⟨C,C.property.1⟩) R hp hcodim
      (hactive C) (hpart.2.2.1 C).2.1
      (by simpa only [← hg ⟨C,C.property.1⟩] using (hpart.2.2.1 C).2.2)
      (by simpa only [← hg ⟨C,C.property.1⟩] using hboundary C) hCangle
    have hcover : ∀ v : R.directionᗮ, v ∈ SectorAngleSum.normalHalfspace N ∨
        v ∈ SectorAngleSum.normalHalfspace DB.normal₁ ∩ SectorAngleSum.normalHalfspace DB.normal₂ ∨
        v ∈ SectorAngleSum.normalHalfspace DC.normal₁ ∩ SectorAngleSum.normalHalfspace DC.normal₂ := by
      intro v
      obtain ⟨J,hJ⟩ := hpart.2.2.2.1 v
      rcases hall J with rfl | rfl | rfl
      · exact Or.inl (hrootEq ▸ hJ)
      · exact Or.inr (Or.inl (DB.cone_eq ▸ hJ))
      · exact Or.inr (Or.inr (DC.cone_eq ▸ hJ))
    have halign := (two_quadrants_flat_boundary_alignment hpart.2.1 N
      DB.normal₁ DB.normal₂ DC.normal₁ DC.normal₂ hN DB.unit₁ DB.unit₂ DB.orthogonal
      DC.unit₁ DC.unit₂ DC.orthogonal hcover
      (by simpa only [← hrootEq,← DB.cone_eq] using hpart.2.2.2.2 root B hBne.symm)
      (by simpa only [← hrootEq,← DC.cone_eq] using hpart.2.2.2.2 root C hCne.symm)).1
    have hBA : (⟨B,B.property.1⟩ : tiles) ≠ ⟨root,root.property.1⟩ := by
      intro heq
      apply hBne
      apply Subtype.ext
      exact congrArg (fun X : tiles => (X : Set (Point 5))) heq
    rcases halign with ⟨c,hc,heq⟩ | ⟨c,hc,heq⟩
    · exact T5_key_side_no_aligned_seam_normal ht g hg ⟨root,root.property.1⟩ ⟨B,B.property.1⟩
        hBA hk q hq i si hs ho R N hzero DB hc heq
    · exact T5_key_side_no_aligned_seam_normal ht g hg ⟨root,root.property.1⟩ ⟨B,B.property.1⟩
        hBA hk q hq i si hs ho R N hzero DB.swap hc heq

#print axioms T5_literal_side_generic_exactly_two_incident

/-- Complete pointwise K1 incident count at the relative interior of a
literal key side. The actual three-sector seam alternative is contradicted
in world coordinates using the full fixed physical plane inventory. -/
theorem T7_literal_side_generic_exactly_two_incident
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction+2=7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7) (i : Fin 6) (si : Bool)
    (hs : posedHalfspaceSlack7 q (.inr (i,si)) ((g ⟨root,root.property.1⟩).symm p) = 0)
    (ho : ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) →
      0 < posedHalfspaceSlack7 q j ((g ⟨root,root.property.1⟩).symm p)) :
    Nat.card (incidentTiles tiles p) = 2 := by
  classical
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  obtain ⟨hrootlocal,hrootangle,hrootboundary⟩ :=
    T7_literal_side_relativeInterior_sector ht R hp hcodim g hg hactive root hk q hq i si hs ho
  rcases T7_generic_flat_root_incident_count ht R hp hcodim g hg hactive root hrootangle hrootboundary with
    htwo | hthree
  · exact htwo
  · exfalso
    letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
    obtain ⟨width,hwroot,hshape,hInv,_⟩ := T7_generic_root_sector_partition
      ht R hp hcodim g hg hactive root hrootangle (Or.inr (Or.inl rfl)) hrootboundary
    obtain ⟨B,C,hBne,hCne,hBC,hall,hBangle,hCangle⟩ := flat_partition_three_actual_companions
      hpart.2.1 (T7IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2
      root hwroot hInv (by simpa only [Nat.card_eq_fintype_card] using hthree)
    obtain ⟨N,hN,hrootEq,hzero⟩ := T7_literal_side_relativeInterior_normal
      ht R hp hcodim g hg hactive root hk q hq i si hs ho
    have hboundary := ht.incident_mem_frontier_of_root_sector T7_isCompact R p root hrootangle
      (hpart.2.2.1 root).2.2 hrootboundary
    obtain ⟨DB⟩ := T7_right_angle_carrier_seam_geometry (g ⟨B,B.property.1⟩) R hp hcodim
      (hactive B) (hpart.2.2.1 B).2.1
      (by simpa only [← hg ⟨B,B.property.1⟩] using (hpart.2.2.1 B).2.2)
      (by simpa only [← hg ⟨B,B.property.1⟩] using hboundary B) hBangle
    obtain ⟨DC⟩ := T7_right_angle_carrier_seam_geometry (g ⟨C,C.property.1⟩) R hp hcodim
      (hactive C) (hpart.2.2.1 C).2.1
      (by simpa only [← hg ⟨C,C.property.1⟩] using (hpart.2.2.1 C).2.2)
      (by simpa only [← hg ⟨C,C.property.1⟩] using hboundary C) hCangle
    have hcover : ∀ v : R.directionᗮ, v ∈ SectorAngleSum.normalHalfspace N ∨
        v ∈ SectorAngleSum.normalHalfspace DB.normal₁ ∩ SectorAngleSum.normalHalfspace DB.normal₂ ∨
        v ∈ SectorAngleSum.normalHalfspace DC.normal₁ ∩ SectorAngleSum.normalHalfspace DC.normal₂ := by
      intro v
      obtain ⟨J,hJ⟩ := hpart.2.2.2.1 v
      rcases hall J with rfl | rfl | rfl
      · exact Or.inl (hrootEq ▸ hJ)
      · exact Or.inr (Or.inl (DB.cone_eq ▸ hJ))
      · exact Or.inr (Or.inr (DC.cone_eq ▸ hJ))
    have halign := (two_quadrants_flat_boundary_alignment hpart.2.1 N
      DB.normal₁ DB.normal₂ DC.normal₁ DC.normal₂ hN DB.unit₁ DB.unit₂ DB.orthogonal
      DC.unit₁ DC.unit₂ DC.orthogonal hcover
      (by simpa only [← hrootEq,← DB.cone_eq] using hpart.2.2.2.2 root B hBne.symm)
      (by simpa only [← hrootEq,← DC.cone_eq] using hpart.2.2.2.2 root C hCne.symm)).1
    have hBA : (⟨B,B.property.1⟩ : tiles) ≠ ⟨root,root.property.1⟩ := by
      intro heq
      apply hBne
      apply Subtype.ext
      exact congrArg (fun X : tiles => (X : Set (Point 7))) heq
    rcases halign with ⟨c,hc,heq⟩ | ⟨c,hc,heq⟩
    · exact T7_key_side_no_aligned_seam_normal ht g hg ⟨root,root.property.1⟩ ⟨B,B.property.1⟩
        hBA hk q hq i si hs ho R N hzero DB hc heq
    · exact T7_key_side_no_aligned_seam_normal ht g hg ⟨root,root.property.1⟩ ⟨B,B.property.1⟩
        hBA hk q hq i si hs ho R N hzero DB.swap hc heq

#print axioms T7_literal_side_generic_exactly_two_incident

end SparseMonotiles
