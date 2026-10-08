module

public import SparseMonotiles.StripCreaseCrossingWorldStrip
public import SparseMonotiles.StripCreaseCrossingPointMembership
public import SparseMonotiles.GenericFaceTiling

@[expose] public section

/-! # An aligned physical carrier edge cannot enter a literal key side face
The finite world-plane inventory is fixed on the entire bounded placed key
before choosing the new crossing. All incident tiles at that crossing are
controlled, and both incident memberships are derived from the actual bodies.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_no_aligned_carrier_edge_on_key_side
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (A B : tiles) (hBA : B ≠ A)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i : Fin 4) (si : Bool) {p : Point 5}
    (hside : referenceHalfspaceSlack5 (.inr (i,si)) p = 0)
    (hother : ∀ a : PyramidHalfspaceIndex 4, a ≠ .inr (i,si) → 0 < referenceHalfspaceSlack5 a p)
    (f : Contact.Facet 5) (howner : Contact.IsChairCell f.cell)
    (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (j : Fin 5) (hj : j ≠ f.axis) (upper : Bool)
    (hplane : ∀ x : Point 5, referenceHalfspaceSlack5 (.inr (i,si)) x = 0 ↔
      (g B).symm (g A (q.euclidean x)) f.axis = (f.gridFacet.anchor f.axis : ℝ))
    (hjend : (g B).symm (g A (q.euclidean p)) j = (f.cell j : ℝ)+(if upper then 1 else 0))
    (hotherCell : ∀ a, a ≠ f.axis → a ≠ j →
      (f.cell a : ℝ) < (g B).symm (g A (q.euclidean p)) a ∧
        (g B).symm (g A (q.euclidean p)) a < (f.cell a : ℝ)+1) : False := by
  classical
  let W : Point 5 ≃ᵃⁱ[ℝ] Point 5 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := W.trans (g B).symm.toRealAffineIsometryEquiv
  let K : Set (Point 5) := W '' referenceSolid5
  have hK : Bornology.IsBounded K := W.isometry.lipschitz.isBounded_image
    (keySolid_isBounded ((referenceBox5 true).toKeyData 19200))
  have hf := ht.finite_bounded_meeting_subtype T5_isCompact
    (by norm_num) T5_centralBall_from_cellCores hK
  let I := {C : tiles // ((C : Set (Point 5)) ∩ K).Nonempty}
  letI : Fintype I := hf.fintype
  let H : I × GlobalBodyHalfspaceIndex keys5 (PyramidHalfspaceIndex 4) → AffineSubspace ℝ (Point 5) :=
    fun z => (affineFormPlane (T5WorldAffineFields (g z.1.1) z.2) 0).comap W.toAffineMap
  obtain ⟨a,y,L,hyk,hystrip,hyi,hya,hyother,hyL,hLdim,hLside,hgeneric⟩ :=
    aligned_carrier_edge_crosses_generic_key_crease (by omega : 2 ≤ 4)
      ((referenceBox5 true).toKeyData 19200)
      (by simp [Fin.last]) (by simp [Fin.last])
      (by
        change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
        exact_mod_cast referenceBox5_height_pos true)
      (fun j => by unfold keyPyramidLo keyPyramidHi; exact_mod_cast referenceBox5_base_interval_pos true j)
      referenceSideDistance5_pos i si e f j hj upper hside hother hplane hjend hotherCell
      referenceSolid5_diam_lt_quarter H
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
    apply T5_literal_pruned_crease_mem hk q hq i si a
    · simpa [posedHalfspaceSlack5, referenceHalfspaceSlack5] using hyi
    · simpa [posedHalfspaceSlack5, referenceHalfspaceSlack5] using hya
    · intro l hli hla
      simpa [posedHalfspaceSlack5, referenceHalfspaceSlack5] using hyother l hli hla
  have hyB : W y ∈ (B : Set (Point 5)) := by
    rw [hg B]
    refine ⟨(g B).symm (W y),?_,(g B).apply_symm_apply _⟩
    exact T5_carrierFacetEdgeStrip_mem f howner hexposed j hj upper hystrip
  let root : incidentTiles tiles (W y) := ⟨A,A.property,hyA⟩
  let flat : incidentTiles tiles (W y) := ⟨B,B.property,hyB⟩
  have hflatne : flat ≠ root := by
    intro heq
    apply hBA
    apply Subtype.ext
    exact congrArg (fun C : incidentTiles tiles (W y) => (C : Set (Point 5))) heq
  have hactive : ∀ C : incidentTiles tiles (W y), ∀ l,
      T5WorldAffineFields (g ⟨C,C.property.1⟩) l (W y) = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨C,C.property.1⟩) l) 0 := by
    intro C l hl z hz
    have hCK : ((C : Set (Point 5)) ∩ K).Nonempty := ⟨W y,C.property.2,⟨y,hyk,rfl⟩⟩
    rcases hz with ⟨w,hw,rfl⟩
    exact hgeneric (⟨⟨⟨C,C.property.1⟩,hCK⟩,l⟩)
      ((mem_affineFormPlane _ _ _).mpr hl) hw
  have hflatplane : ∀ z ∈ R, (g B).symm z f.axis = (f.gridFacet.anchor f.axis : ℝ) := by
    rintro z ⟨w,hw,rfl⟩
    exact (hplane w).mp (hLside w hw)
  cases a with
  | none =>
      refine T5_literal_base_side_crease_no_carrier_strip ht R hyR hRdim g hg hactive
        root hk q hq i si ?_ ?_ ?_ flat hflatne f howner hexposed j hj upper hystrip hflatplane
      · exact (hslack _).trans hya
      · exact (hslack _).trans hyi
      · intro l hlb hls
        change 0 < posedHalfspaceSlack5 q l ((g A).symm (W y))
        rw [hslack]
        exact hyother l hls hlb
  | some a =>
      rcases a with ⟨l,sl⟩
      refine T5_literal_side_side_crease_no_carrier_strip ht R hyR hRdim g hg hactive
        root hk q hq i l.val (Ne.symm l.property) si sl ?_ ?_ ?_
        flat hflatne f howner hexposed j hj upper hystrip hflatplane
      · exact (hslack _).trans hyi
      · exact (hslack _).trans hya
      · intro z hzi hzl
        change 0 < posedHalfspaceSlack5 q z ((g A).symm (W y))
        rw [hslack]
        exact hyother z hzi hzl

#print axioms T5_no_aligned_carrier_edge_on_key_side

theorem T7_no_aligned_carrier_edge_on_key_side
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (A B : tiles) (hBA : B ≠ A)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i : Fin 6) (si : Bool) {p : Point 7}
    (hside : referenceHalfspaceSlack7 (.inr (i,si)) p = 0)
    (hother : ∀ a : PyramidHalfspaceIndex 6, a ≠ .inr (i,si) → 0 < referenceHalfspaceSlack7 a p)
    (f : Contact.Facet 7) (howner : Contact.IsChairCell f.cell)
    (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (j : Fin 7) (hj : j ≠ f.axis) (upper : Bool)
    (hplane : ∀ x : Point 7, referenceHalfspaceSlack7 (.inr (i,si)) x = 0 ↔
      (g B).symm (g A (q.euclidean x)) f.axis = (f.gridFacet.anchor f.axis : ℝ))
    (hjend : (g B).symm (g A (q.euclidean p)) j = (f.cell j : ℝ)+(if upper then 1 else 0))
    (hotherCell : ∀ a, a ≠ f.axis → a ≠ j →
      (f.cell a : ℝ) < (g B).symm (g A (q.euclidean p)) a ∧
        (g B).symm (g A (q.euclidean p)) a < (f.cell a : ℝ)+1) : False := by
  classical
  let W : Point 7 ≃ᵃⁱ[ℝ] Point 7 := q.euclidean.trans (g A).toRealAffineIsometryEquiv
  let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := W.trans (g B).symm.toRealAffineIsometryEquiv
  let K : Set (Point 7) := W '' referenceSolid7
  have hK : Bornology.IsBounded K := W.isometry.lipschitz.isBounded_image
    (keySolid_isBounded ((referenceBox7 true).toKeyData 188160))
  have hf := ht.finite_bounded_meeting_subtype T7_isCompact
    (by norm_num) T7_centralBall_from_cellCores hK
  let I := {C : tiles // ((C : Set (Point 7)) ∩ K).Nonempty}
  letI : Fintype I := hf.fintype
  let H : I × GlobalBodyHalfspaceIndex keys7 (PyramidHalfspaceIndex 6) → AffineSubspace ℝ (Point 7) :=
    fun z => (affineFormPlane (T7WorldAffineFields (g z.1.1) z.2) 0).comap W.toAffineMap
  obtain ⟨a,y,L,hyk,hystrip,hyi,hya,hyother,hyL,hLdim,hLside,hgeneric⟩ :=
    aligned_carrier_edge_crosses_generic_key_crease (by omega : 2 ≤ 6)
      ((referenceBox7 true).toKeyData 188160)
      (by simp [Fin.last]) (by simp [Fin.last])
      (by
        change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
        exact_mod_cast referenceBox7_height_pos true)
      (fun j => by unfold keyPyramidLo keyPyramidHi; exact_mod_cast referenceBox7_base_interval_pos true j)
      referenceSideDistance7_pos i si e f j hj upper hside hother hplane hjend hotherCell
      referenceSolid7_diam_lt_quarter H
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
    apply T7_literal_pruned_crease_mem hk q hq i si a
    · simpa [posedHalfspaceSlack7, referenceHalfspaceSlack7] using hyi
    · simpa [posedHalfspaceSlack7, referenceHalfspaceSlack7] using hya
    · intro l hli hla
      simpa [posedHalfspaceSlack7, referenceHalfspaceSlack7] using hyother l hli hla
  have hyB : W y ∈ (B : Set (Point 7)) := by
    rw [hg B]
    refine ⟨(g B).symm (W y),?_,(g B).apply_symm_apply _⟩
    exact T7_carrierFacetEdgeStrip_mem f howner hexposed j hj upper hystrip
  let root : incidentTiles tiles (W y) := ⟨A,A.property,hyA⟩
  let flat : incidentTiles tiles (W y) := ⟨B,B.property,hyB⟩
  have hflatne : flat ≠ root := by
    intro heq
    apply hBA
    apply Subtype.ext
    exact congrArg (fun C : incidentTiles tiles (W y) => (C : Set (Point 7))) heq
  have hactive : ∀ C : incidentTiles tiles (W y), ∀ l,
      T7WorldAffineFields (g ⟨C,C.property.1⟩) l (W y) = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨C,C.property.1⟩) l) 0 := by
    intro C l hl z hz
    have hCK : ((C : Set (Point 7)) ∩ K).Nonempty := ⟨W y,C.property.2,⟨y,hyk,rfl⟩⟩
    rcases hz with ⟨w,hw,rfl⟩
    exact hgeneric (⟨⟨⟨C,C.property.1⟩,hCK⟩,l⟩)
      ((mem_affineFormPlane _ _ _).mpr hl) hw
  have hflatplane : ∀ z ∈ R, (g B).symm z f.axis = (f.gridFacet.anchor f.axis : ℝ) := by
    rintro z ⟨w,hw,rfl⟩
    exact (hplane w).mp (hLside w hw)
  cases a with
  | none =>
      refine T7_literal_base_side_crease_no_carrier_strip ht R hyR hRdim g hg hactive
        root hk q hq i si ?_ ?_ ?_ flat hflatne f howner hexposed j hj upper hystrip hflatplane
      · exact (hslack _).trans hya
      · exact (hslack _).trans hyi
      · intro l hlb hls
        change 0 < posedHalfspaceSlack7 q l ((g A).symm (W y))
        rw [hslack]
        exact hyother l hls hlb
  | some a =>
      rcases a with ⟨l,sl⟩
      refine T7_literal_side_side_crease_no_carrier_strip ht R hyR hRdim g hg hactive
        root hk q hq i l.val (Ne.symm l.property) si sl ?_ ?_ ?_
        flat hflatne f howner hexposed j hj upper hystrip hflatplane
      · exact (hslack _).trans hyi
      · exact (hslack _).trans hya
      · intro z hzi hzl
        change 0 < posedHalfspaceSlack7 q z ((g A).symm (W y))
        rw [hslack]
        exact hyother z hzi hzl

#print axioms T7_no_aligned_carrier_edge_on_key_side

end SparseMonotiles
