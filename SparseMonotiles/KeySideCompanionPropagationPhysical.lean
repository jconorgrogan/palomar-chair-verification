module

public import SparseMonotiles.KeySideCompanionPropagationGeometry
public import SparseMonotiles.StripCreaseCrossingClosedFace

@[expose] public section

/-! # Physical generic shared creases and equality of side companions
A finite inventory is fixed on the whole placed key before the point is chosen.
Every incident physical field at the new point is therefore controlled.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_exists_generic_shared_key_side_point_of_seed
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i j : Fin 4) (hij : i ≠ j) (si sj : Bool) {p : Point 5}
    (hi : referenceHalfspaceSlack5 (.inr (i,si)) p=0)
    (hj : referenceHalfspaceSlack5 (.inr (j,sj)) p=0)
    (ho : ∀ a : PyramidHalfspaceIndex 4, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
      0 < referenceHalfspaceSlack5 a p) :
    ∃ y : Point 5, y ∈ (A : Set (Point 5)) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (j,sj)) x=0}) ∧
      Nat.card (incidentTiles tiles y)=2 := by
  classical
  let W : Point 5 ≃ᵃⁱ[ℝ] Point 5 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let K : Set (Point 5) := W '' referenceSolid5
  have hK : Bornology.IsBounded K := W.isometry.lipschitz.isBounded_image
    (keySolid_isBounded ((referenceBox5 true).toKeyData 19200))
  have hf := ht.finite_bounded_meeting_subtype T5_isCompact
    (by norm_num) T5_centralBall_from_cellCores hK
  let I := {C : tiles // ((C : Set (Point 5)) ∩ K).Nonempty}
  letI : Fintype I := hf.fintype
  let H : I × GlobalBodyHalfspaceIndex keys5 (PyramidHalfspaceIndex 4) → AffineSubspace ℝ (Point 5) :=
    fun z => (affineFormPlane (T5WorldAffineFields (g z.1.1) z.2) 0).comap W.toAffineMap
  obtain ⟨y,L,hyk,hyi,hyj,hyother,hyL,hLdim,hgeneric⟩ :=
    exists_generic_key_side_side_crease ((referenceBox5 true).toKeyData 19200)
      (by simp [Fin.last]) (by simp [Fin.last])
      (by
        change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
        exact_mod_cast referenceBox5_height_pos true)
      referenceSideDistance5_pos i j hij si sj hi hj ho H
  let R := L.map W.toAffineMap
  have hyR : W y ∈ R := ⟨y,hyL,rfl⟩
  have hRdim : Module.finrank ℝ R.direction+2=5 := by
    rw [show Module.finrank ℝ R.direction = Module.finrank ℝ L.direction from
      affineEquiv_map_ridge_finrank W.toAffineEquiv L]
    exact hLdim
  have hrootcoord (z : Point 5) : (g A).symm (W z) = q.euclidean z := by simp [W]
  have hslack (l : PyramidHalfspaceIndex 4) :
      posedHalfspaceSlack5 q l ((g A).symm (W y)) = referenceHalfspaceSlack5 l y := by
    rw [hrootcoord]
    simp [posedHalfspaceSlack5]
  have hyA : W y ∈ (A : Set (Point 5)) := by
    rw [hg A]
    refine ⟨q.euclidean y,?_,rfl⟩
    apply T5_literal_pruned_crease_mem hk q hq i si (some (⟨j,hij.symm⟩,sj))
    · simpa [referenceHalfspaceSlack5,posedHalfspaceSlack5] using hyi
    · simpa [referenceHalfspaceSlack5,posedHalfspaceSlack5,pyramidFacetHalfspaceIndex,pyramidSideBoundaryFacet] using hyj
    · intro l hli hlj
      simpa [referenceHalfspaceSlack5,posedHalfspaceSlack5] using hyother l hli hlj
  let root : incidentTiles tiles (W y) := ⟨A,A.property,hyA⟩
  have hactive : ∀ C : incidentTiles tiles (W y), ∀ l,
      T5WorldAffineFields (g ⟨C,C.property.1⟩) l (W y) = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨C,C.property.1⟩) l) 0 := by
    intro C l hl z hz
    have hCK : ((C : Set (Point 5)) ∩ K).Nonempty := ⟨W y,C.property.2,⟨y,hyk,rfl⟩⟩
    rcases hz with ⟨w,hw,rfl⟩
    exact hgeneric (⟨⟨⟨C,C.property.1⟩,hCK⟩,l⟩)
      ((mem_affineFormPlane _ _ _).mpr hl) hw
  have hcard : Nat.card (incidentTiles tiles (W y))=2 := by
    apply T5_literal_side_side_crease_exactly_two_incident ht R hyR hRdim g hg hactive
      root hk q hq i j hij si sj
    · exact (hslack _).trans hyi
    · exact (hslack _).trans hyj
    · intro l hli hlj
      change 0 < posedHalfspaceSlack5 q l ((g A).symm (W y))
      rw [hslack]
      exact hyother l hli hlj
  have hykey : q.euclidean y ∈ keySolid k := by
    rw [hq]
    exact ⟨y,hyk,rfl⟩
  refine ⟨W y,hyA,?_,?_,hcard⟩
  · refine ⟨q.euclidean y,⟨hykey,?_⟩,rfl⟩
    simpa [referenceHalfspaceSlack5,posedHalfspaceSlack5] using hyi
  · refine ⟨q.euclidean y,⟨hykey,?_⟩,rfl⟩
    simpa [referenceHalfspaceSlack5,posedHalfspaceSlack5] using hyj

#print axioms T5_exists_generic_shared_key_side_point_of_seed

theorem T7_exists_generic_shared_key_side_point_of_seed
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i j : Fin 6) (hij : i ≠ j) (si sj : Bool) {p : Point 7}
    (hi : referenceHalfspaceSlack7 (.inr (i,si)) p=0)
    (hj : referenceHalfspaceSlack7 (.inr (j,sj)) p=0)
    (ho : ∀ a : PyramidHalfspaceIndex 6, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
      0 < referenceHalfspaceSlack7 a p) :
    ∃ y : Point 7, y ∈ (A : Set (Point 7)) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (j,sj)) x=0}) ∧
      Nat.card (incidentTiles tiles y)=2 := by
  classical
  let W : Point 7 ≃ᵃⁱ[ℝ] Point 7 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let K : Set (Point 7) := W '' referenceSolid7
  have hK : Bornology.IsBounded K := W.isometry.lipschitz.isBounded_image
    (keySolid_isBounded ((referenceBox7 true).toKeyData 188160))
  have hf := ht.finite_bounded_meeting_subtype T7_isCompact
    (by norm_num) T7_centralBall_from_cellCores hK
  let I := {C : tiles // ((C : Set (Point 7)) ∩ K).Nonempty}
  letI : Fintype I := hf.fintype
  let H : I × GlobalBodyHalfspaceIndex keys7 (PyramidHalfspaceIndex 6) → AffineSubspace ℝ (Point 7) :=
    fun z => (affineFormPlane (T7WorldAffineFields (g z.1.1) z.2) 0).comap W.toAffineMap
  obtain ⟨y,L,hyk,hyi,hyj,hyother,hyL,hLdim,hgeneric⟩ :=
    exists_generic_key_side_side_crease ((referenceBox7 true).toKeyData 188160)
      (by simp [Fin.last]) (by simp [Fin.last])
      (by
        change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
        exact_mod_cast referenceBox7_height_pos true)
      referenceSideDistance7_pos i j hij si sj hi hj ho H
  let R := L.map W.toAffineMap
  have hyR : W y ∈ R := ⟨y,hyL,rfl⟩
  have hRdim : Module.finrank ℝ R.direction+2=7 := by
    rw [show Module.finrank ℝ R.direction = Module.finrank ℝ L.direction from
      affineEquiv_map_ridge_finrank W.toAffineEquiv L]
    exact hLdim
  have hrootcoord (z : Point 7) : (g A).symm (W z) = q.euclidean z := by simp [W]
  have hslack (l : PyramidHalfspaceIndex 6) :
      posedHalfspaceSlack7 q l ((g A).symm (W y)) = referenceHalfspaceSlack7 l y := by
    rw [hrootcoord]
    simp [posedHalfspaceSlack7]
  have hyA : W y ∈ (A : Set (Point 7)) := by
    rw [hg A]
    refine ⟨q.euclidean y,?_,rfl⟩
    apply T7_literal_pruned_crease_mem hk q hq i si (some (⟨j,hij.symm⟩,sj))
    · simpa [referenceHalfspaceSlack7,posedHalfspaceSlack7] using hyi
    · simpa [referenceHalfspaceSlack7,posedHalfspaceSlack7,pyramidFacetHalfspaceIndex,pyramidSideBoundaryFacet] using hyj
    · intro l hli hlj
      simpa [referenceHalfspaceSlack7,posedHalfspaceSlack7] using hyother l hli hlj
  let root : incidentTiles tiles (W y) := ⟨A,A.property,hyA⟩
  have hactive : ∀ C : incidentTiles tiles (W y), ∀ l,
      T7WorldAffineFields (g ⟨C,C.property.1⟩) l (W y) = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨C,C.property.1⟩) l) 0 := by
    intro C l hl z hz
    have hCK : ((C : Set (Point 7)) ∩ K).Nonempty := ⟨W y,C.property.2,⟨y,hyk,rfl⟩⟩
    rcases hz with ⟨w,hw,rfl⟩
    exact hgeneric (⟨⟨⟨C,C.property.1⟩,hCK⟩,l⟩)
      ((mem_affineFormPlane _ _ _).mpr hl) hw
  have hcard : Nat.card (incidentTiles tiles (W y))=2 := by
    apply T7_literal_side_side_crease_exactly_two_incident ht R hyR hRdim g hg hactive
      root hk q hq i j hij si sj
    · exact (hslack _).trans hyi
    · exact (hslack _).trans hyj
    · intro l hli hlj
      change 0 < posedHalfspaceSlack7 q l ((g A).symm (W y))
      rw [hslack]
      exact hyother l hli hlj
  have hykey : q.euclidean y ∈ keySolid k := by
    rw [hq]
    exact ⟨y,hyk,rfl⟩
  refine ⟨W y,hyA,?_,?_,hcard⟩
  · refine ⟨q.euclidean y,⟨hykey,?_⟩,rfl⟩
    simpa [referenceHalfspaceSlack7,posedHalfspaceSlack7] using hyi
  · refine ⟨q.euclidean y,⟨hykey,?_⟩,rfl⟩
    simpa [referenceHalfspaceSlack7,posedHalfspaceSlack7] using hyj

#print axioms T7_exists_generic_shared_key_side_point_of_seed

end SparseMonotiles
