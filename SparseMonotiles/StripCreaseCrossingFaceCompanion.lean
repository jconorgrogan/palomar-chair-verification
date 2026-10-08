module

public import SparseMonotiles.StripCreaseCrossingPointwise
public import SparseMonotiles.LiteralKeySideCompanions
public import SparseMonotiles.GenericFaceTiling
public import SparseMonotiles.FaceCompanionContinuation

@[expose] public section

/-! # Actual pointwise and connected-face key-side companions -/
namespace SparseMonotiles
open Set Canonical

/-- Either material orientation of an actual nonzero key side is regular
closed, including every point of its supporting plane. -/
theorem key_side_material_regular_at_ridge {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (R : AffineSubspace ℝ (Point (n+1))) {p : Point (n+1)} (hp : p ∈ R)
    (i : Fin n) (si b : Bool)
    (hzero : ∀ x ∈ R, keyPyramidHalfspaceSlack k (.inr (i,si)) (e x) = 0) :
    p ∈ closure (interior (sideMaterialHalfspace
      (fun x => keyPyramidHalfspaceSlack k (.inr (i,si)) (e x)) b)) := by
  obtain ⟨N,_,hN,hpos,hneg⟩ := key_facet_normal_space_adapter k hd e R hp (some (i,si)) hzero
  simp only [pyramidFacetHalfspaceIndex] at hpos hneg
  have hs : keyPyramidHalfspaceSlack k (.inr (i,si)) (e p) = 0 := hzero p hp
  cases b
  · change p ∈ closure (interior {x | keyPyramidHalfspaceSlack k (.inr (i,si)) (e x) ≤ 0})
    rw [hneg,normal_sector_pullback_regular_closed R p
      (SectorAngleSum.HasSectorAngle.halfplane (-N) (neg_ne_zero.mpr hN) rfl)]
    simpa [ridgeNormalProjection,SectorAngleSum.normalHalfspace]
  · change p ∈ closure (interior {x | 0 ≤ keyPyramidHalfspaceSlack k (.inr (i,si)) (e x)})
    rw [hpos,normal_sector_pullback_regular_closed R p
      (SectorAngleSum.HasSectorAngle.halfplane N hN rfl)]
    simpa [ridgeNormalProjection,SectorAngleSum.normalHalfspace]


/-- Pointwise K1: the actual generic key-side point has a distinct physical
companion with the fixed opposite ambient halfspace germ. -/
theorem T5_literal_side_generic_companion
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
    (∃ B : incidentTiles tiles p, B ≠ root ∧ LocalSetEq p (B : Set (Point 5))
      (sideMaterialHalfspace (fun x => posedHalfspaceSlack5 q (.inr (i,si))
        ((g ⟨root,root.property.1⟩).symm x)) (!k.bump))) ∧
    p ∈ closure (interior (sideMaterialHalfspace (fun x => posedHalfspaceSlack5 q (.inr (i,si))
      ((g ⟨root,root.property.1⟩).symm x)) (!k.bump))) := by
  have hcard := T5_literal_side_generic_exactly_two_incident ht R hp hcodim g hg hactive
    root hk q hq i si hs ho
  refine ⟨T5_two_incident_literal_side_opposite_germ ht R hp hcodim g hg hactive
    root hk q hq i si hs ho hcard,?_⟩
  let G := g ⟨root,root.property.1⟩
  let e := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hzero := T5_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  exact key_side_material_regular_at_ridge ((referenceBox5 true).toKeyData 19200)
    referenceSideDistance5_pos e R hp i si (!k.bump) (hzero (.inr (i,si)) hs)

/-- Generic-face selection and pointwise companion existence are now composed
for any actual bounded relatively open convex patch of a literal key side. -/
theorem T5_key_side_patch_generic_companions
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5) (i : Fin 4) (si : Bool)
    (P : AffineSubspace ℝ (Point 5)) (hP : (P : Set (Point 5)).Nonempty)
    (hPdim : Module.finrank ℝ P.direction+1=5)
    (O : Set (Point 5)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty)
    (hside : ∀ p ∈ O, posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm p) = 0 ∧
      ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) → 0 < posedHalfspaceSlack5 q j ((g A).symm p)) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      (∀ x ∈ G, ∃ B ∈ incidentTiles tiles (x : Point 5), B ≠ (A : Set (Point 5)) ∧
        LocalSetEq (x : Point 5) B
          (sideMaterialHalfspace (fun y => posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) ∧
      ∀ x ∈ G, (x : Point 5) ∈ closure (interior
        (sideMaterialHalfspace (fun y => posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) := by
  classical
  obtain ⟨G,hGO,hpath,hcl,hgeneric⟩ := T5_tiling_exists_genericFacePoints_common_ridge
    ht g P hP hPdim O hOb hO hconv hne
  have hxresult (x : P) (hx : x ∈ G) :
      (∃ B ∈ incidentTiles tiles (x : Point 5), B ≠ (A : Set (Point 5)) ∧
        LocalSetEq (x : Point 5) B
          (sideMaterialHalfspace (fun y => posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) ∧
      (x : Point 5) ∈ closure (interior
        (sideMaterialHalfspace (fun y => posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) := by
    have hs := hside x (hGO hx)
    have hxA : (x : Point 5) ∈ (A : Set (Point 5)) := by
      rw [hg A]
      exact (T5_copy_literal_side_relativeInterior_germ (g A) hk q hq i si hs.1 hs.2).1
    let root : incidentTiles tiles (x : Point 5) := ⟨A,A.property,hxA⟩
    obtain ⟨R,hxR,hRP,hRdim,hRactive⟩ := hgeneric x hx
    have hactive : ∀ C : incidentTiles tiles (x : Point 5), ∀ j,
        T5WorldAffineFields (g ⟨C,C.property.1⟩) j x = 0 →
          R ≤ affineFormPlane (T5WorldAffineFields (g ⟨C,C.property.1⟩) j) 0 := by
      intro C j hj
      exact hRactive ⟨C,C.property.1⟩ ⟨x,C.property.2,hGO hx⟩ j hj
    obtain ⟨⟨B,hBne,hBlocal⟩,hreg⟩ := T5_literal_side_generic_companion
      ht R hxR hRdim g hg hactive root hk q hq i si hs.1 hs.2
    refine ⟨⟨B,B.property,?_,hBlocal⟩,hreg⟩
    intro heq
    exact hBne (Subtype.ext heq)
  exact ⟨G,hGO,hpath,hcl,fun x hx => (hxresult x hx).1,fun x hx => (hxresult x hx).2⟩

/-- One physical companion continues across the closure of the actual side
patch, derived from pointwise K1 and connected generic-face selection. -/
theorem T5_key_side_patch_whole_companion
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5) (i : Fin 4) (si : Bool)
    (P : AffineSubspace ℝ (Point 5)) (hP : (P : Set (Point 5)).Nonempty)
    (hPdim : Module.finrank ℝ P.direction+1=5)
    (O : Set (Point 5)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty)
    (hside : ∀ p ∈ O, posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm p) = 0 ∧
      ∀ j : PyramidHalfspaceIndex 4, j ≠ .inr (i,si) → 0 < posedHalfspaceSlack5 q j ((g A).symm p)) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∃ B ∈ tiles, B ≠ (A : Set (Point 5)) ∧
        Subtype.val '' closure (Subtype.val ⁻¹' O : Set P) ⊆ B ∧
        (∀ x ∈ G, LocalSetEq (x : Point 5) B
          (sideMaterialHalfspace (fun y => posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) ∧
        ∀ x ∈ G, ∀ C ∈ tiles,
          LocalSetEq (x : Point 5) C
            (sideMaterialHalfspace (fun y => posedHalfspaceSlack5 q (.inr (i,si)) ((g A).symm y)) (!k.bump)) → C = B := by
  obtain ⟨G,hGO,hpath,hcl,hex,hreg⟩ := T5_key_side_patch_generic_companions
    ht g hg A hk q hq i si P hP hPdim O hOb hO hconv hne hside
  refine ⟨G,hGO,hpath,hcl,?_⟩
  exact ht.exists_companion_closed_face_intrinsic T5_isCompact
    (Subtype.val : P → Point 5) continuous_subtype_val hpath.isConnected hcl hreg hex

#print axioms T5_literal_side_generic_companion
#print axioms T5_key_side_patch_generic_companions
#print axioms T5_key_side_patch_whole_companion

/-- Pointwise K1: the actual generic key-side point has a distinct physical
companion with the fixed opposite ambient halfspace germ. -/
theorem T7_literal_side_generic_companion
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
    (∃ B : incidentTiles tiles p, B ≠ root ∧ LocalSetEq p (B : Set (Point 7))
      (sideMaterialHalfspace (fun x => posedHalfspaceSlack7 q (.inr (i,si))
        ((g ⟨root,root.property.1⟩).symm x)) (!k.bump))) ∧
    p ∈ closure (interior (sideMaterialHalfspace (fun x => posedHalfspaceSlack7 q (.inr (i,si))
      ((g ⟨root,root.property.1⟩).symm x)) (!k.bump))) := by
  have hcard := T7_literal_side_generic_exactly_two_incident ht R hp hcodim g hg hactive
    root hk q hq i si hs ho
  refine ⟨T7_two_incident_literal_side_opposite_germ ht R hp hcodim g hg hactive
    root hk q hq i si hs ho hcard,?_⟩
  let G := g ⟨root,root.property.1⟩
  let e := G.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
  have hzero := T7_local_key_active_planes_contain_ridge G hk q hq R (hactive root)
  exact key_side_material_regular_at_ridge ((referenceBox7 true).toKeyData 188160)
    referenceSideDistance7_pos e R hp i si (!k.bump) (hzero (.inr (i,si)) hs)

/-- Generic-face selection and pointwise companion existence are now composed
for any actual bounded relatively open convex patch of a literal key side. -/
theorem T7_key_side_patch_generic_companions
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7) (i : Fin 6) (si : Bool)
    (P : AffineSubspace ℝ (Point 7)) (hP : (P : Set (Point 7)).Nonempty)
    (hPdim : Module.finrank ℝ P.direction+1=7)
    (O : Set (Point 7)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty)
    (hside : ∀ p ∈ O, posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm p) = 0 ∧
      ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) → 0 < posedHalfspaceSlack7 q j ((g A).symm p)) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      (∀ x ∈ G, ∃ B ∈ incidentTiles tiles (x : Point 7), B ≠ (A : Set (Point 7)) ∧
        LocalSetEq (x : Point 7) B
          (sideMaterialHalfspace (fun y => posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) ∧
      ∀ x ∈ G, (x : Point 7) ∈ closure (interior
        (sideMaterialHalfspace (fun y => posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) := by
  classical
  obtain ⟨G,hGO,hpath,hcl,hgeneric⟩ := T7_tiling_exists_genericFacePoints_common_ridge
    ht g P hP hPdim O hOb hO hconv hne
  have hxresult (x : P) (hx : x ∈ G) :
      (∃ B ∈ incidentTiles tiles (x : Point 7), B ≠ (A : Set (Point 7)) ∧
        LocalSetEq (x : Point 7) B
          (sideMaterialHalfspace (fun y => posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) ∧
      (x : Point 7) ∈ closure (interior
        (sideMaterialHalfspace (fun y => posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) := by
    have hs := hside x (hGO hx)
    have hxA : (x : Point 7) ∈ (A : Set (Point 7)) := by
      rw [hg A]
      exact (T7_copy_literal_side_relativeInterior_germ (g A) hk q hq i si hs.1 hs.2).1
    let root : incidentTiles tiles (x : Point 7) := ⟨A,A.property,hxA⟩
    obtain ⟨R,hxR,hRP,hRdim,hRactive⟩ := hgeneric x hx
    have hactive : ∀ C : incidentTiles tiles (x : Point 7), ∀ j,
        T7WorldAffineFields (g ⟨C,C.property.1⟩) j x = 0 →
          R ≤ affineFormPlane (T7WorldAffineFields (g ⟨C,C.property.1⟩) j) 0 := by
      intro C j hj
      exact hRactive ⟨C,C.property.1⟩ ⟨x,C.property.2,hGO hx⟩ j hj
    obtain ⟨⟨B,hBne,hBlocal⟩,hreg⟩ := T7_literal_side_generic_companion
      ht R hxR hRdim g hg hactive root hk q hq i si hs.1 hs.2
    refine ⟨⟨B,B.property,?_,hBlocal⟩,hreg⟩
    intro heq
    exact hBne (Subtype.ext heq)
  exact ⟨G,hGO,hpath,hcl,fun x hx => (hxresult x hx).1,fun x hx => (hxresult x hx).2⟩

/-- One physical companion continues across the closure of the actual side
patch, derived from pointwise K1 and connected generic-face selection. -/
theorem T7_key_side_patch_whole_companion
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7) (i : Fin 6) (si : Bool)
    (P : AffineSubspace ℝ (Point 7)) (hP : (P : Set (Point 7)).Nonempty)
    (hPdim : Module.finrank ℝ P.direction+1=7)
    (O : Set (Point 7)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty)
    (hside : ∀ p ∈ O, posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm p) = 0 ∧
      ∀ j : PyramidHalfspaceIndex 6, j ≠ .inr (i,si) → 0 < posedHalfspaceSlack7 q j ((g A).symm p)) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∃ B ∈ tiles, B ≠ (A : Set (Point 7)) ∧
        Subtype.val '' closure (Subtype.val ⁻¹' O : Set P) ⊆ B ∧
        (∀ x ∈ G, LocalSetEq (x : Point 7) B
          (sideMaterialHalfspace (fun y => posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm y)) (!k.bump))) ∧
        ∀ x ∈ G, ∀ C ∈ tiles,
          LocalSetEq (x : Point 7) C
            (sideMaterialHalfspace (fun y => posedHalfspaceSlack7 q (.inr (i,si)) ((g A).symm y)) (!k.bump)) → C = B := by
  obtain ⟨G,hGO,hpath,hcl,hex,hreg⟩ := T7_key_side_patch_generic_companions
    ht g hg A hk q hq i si P hP hPdim O hOb hO hconv hne hside
  refine ⟨G,hGO,hpath,hcl,?_⟩
  exact ht.exists_companion_closed_face_intrinsic T7_isCompact
    (Subtype.val : P → Point 7) continuous_subtype_val hpath.isConnected hcl hreg hex

#print axioms T7_literal_side_generic_companion
#print axioms T7_key_side_patch_generic_companions
#print axioms T7_key_side_patch_whole_companion

#print axioms key_side_material_regular_at_ridge
end SparseMonotiles
