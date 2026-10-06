module

public import SparseMonotiles.KeySideFacePatch

@[expose] public section

/-! The actual open side patch and its full closed face under arbitrary
Euclidean affine-isometric placement. These are the concrete hypotheses
required by generic-face selection and physical companion continuation. -/
namespace SparseMonotiles
open Set

noncomputable def posedKeySidePlane {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) : AffineSubspace ℝ (Point (n+1)) :=
  (keySideAffinePlane k i b).map W.toAffineEquiv.toAffineMap

noncomputable def posedKeySidePatch {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) : Set (Point (n+1)) :=
  W '' keySideStrictPatch k i b

theorem mem_posedKeySidePlane_iff {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (x : Point (n+1)) :
    x ∈ posedKeySidePlane k i b W ↔ W.symm x ∈ keySideAffinePlane k i b := by
  change x ∈ (keySideAffinePlane k i b).map W.toAffineEquiv.toAffineMap ↔ _
  rw [AffineSubspace.mem_map]
  constructor
  · rintro ⟨y,hy,hxy⟩
    have heq : W.symm x=y := by rw [← hxy]; exact W.symm_apply_apply y
    simpa only [heq] using hy
  · intro hx
    exact ⟨W.symm x,hx,W.apply_symm_apply x⟩

theorem mem_posedKeySidePatch_iff {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (x : Point (n+1)) :
    x ∈ posedKeySidePatch k i b W ↔ W.symm x ∈ keySideStrictPatch k i b := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [W.symm_apply_apply] using hy
  · intro hx
    exact ⟨W.symm x,hx,W.apply_symm_apply x⟩

theorem posedKeySidePatch_subset_plane {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ j c, 0 < keySideDistance k j c) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    posedKeySidePatch k i b W ⊆ (posedKeySidePlane k i b W : Set (Point (n+1))) := by
  intro x hx
  apply (mem_posedKeySidePlane_iff k i b W x).mpr
  exact (mem_keySideAffinePlane_iff k hd i b _).mpr
    ((mem_posedKeySidePatch_iff k i b W x).mp hx).1

theorem posedKeySidePlane_nonempty {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    (posedKeySidePlane k i b W : Set (Point (n+1))).Nonempty := by
  refine ⟨W (rationalPoint k.apex),?_⟩
  change W (rationalPoint k.apex) ∈ posedKeySidePlane k i b W
  apply (mem_posedKeySidePlane_iff k i b W _).mpr
  rw [W.symm_apply_apply]
  exact key_apex_mem_sideAffinePlane k i b

theorem posedKeySidePlane_finrank {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    Module.finrank ℝ (posedKeySidePlane k i b W).direction + 1 = n+1 := by
  change Module.finrank ℝ ((keySideAffinePlane k i b).map W.toAffineEquiv.toAffineMap).direction+1=n+1
  rw [affineEquiv_map_ridge_finrank,keySideAffinePlane_direction_finrank]

theorem posedKeySidePatch_nonempty_in_plane {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (hd : ∀ j c, 0 < keySideDistance k j c)
    (i : Fin n) (b : Bool) (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    (Subtype.val ⁻¹' posedKeySidePatch k i b W : Set (posedKeySidePlane k i b W)).Nonempty := by
  have hx : W (keySideStrictPoint k i b) ∈ posedKeySidePatch k i b W :=
    ⟨keySideStrictPoint k i b,keySideStrictPoint_mem k hh hd i b,rfl⟩
  exact ⟨⟨W (keySideStrictPoint k i b),posedKeySidePatch_subset_plane k hd i b W hx⟩,hx⟩

theorem convex_posedKeySidePatch {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) : Convex ℝ (posedKeySidePatch k i b W) :=
  Convex.affine_image W.toAffineEquiv.toAffineMap (convex_keySideStrictPatch k i b)

theorem posedKeySidePatch_bounded {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) : Bornology.IsBounded (posedKeySidePatch k i b W) :=
  W.isometry.lipschitz.isBounded_image (keySideStrictPatch_bounded k hc hr hh i b)

theorem isOpen_posedKeySidePatch_in_plane {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ j c, 0 < keySideDistance k j c) (i : Fin n) (b : Bool)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    IsOpen (Subtype.val ⁻¹' posedKeySidePatch k i b W : Set (posedKeySidePlane k i b W)) := by
  classical
  have heq : (Subtype.val ⁻¹' posedKeySidePatch k i b W : Set (posedKeySidePlane k i b W)) =
      {x : posedKeySidePlane k i b W | ∀ j : {j : PyramidHalfspaceIndex n // j ≠ .inr (i,b)},
        0 < keyPyramidHalfspaceSlack k j (W.symm (x : Point (n+1)))} := by
    ext x
    rw [Set.mem_preimage,mem_posedKeySidePatch_iff]
    constructor
    · intro h j; exact h.2 j j.property
    · intro h
      refine ⟨?_,fun j hj => h ⟨j,hj⟩⟩
      exact (mem_keySideAffinePlane_iff k hd i b _).mp
        ((mem_posedKeySidePlane_iff k i b W x).mp x.property)
  rw [heq,Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const
    ((continuous_keyPyramidHalfspaceSlack k j).comp (W.symm.continuous.comp continuous_subtype_val)))

/-- Intrinsic closure followed by the inclusion of a closed plane is ambient
closure whenever the original set is in that plane. -/
theorem subtype_image_closure_preimage_of_closed {E : Type*} [TopologicalSpace E]
    (P O : Set E) (hP : IsClosed P) (hOP : O ⊆ P) :
    Subtype.val '' closure (Subtype.val ⁻¹' O : Set P) = closure O := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' O : Set P) = O := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨⟨x,hOP hx⟩,hx,rfl⟩
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,himg]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact hy
  · intro hx
    exact ⟨⟨x,closure_minimal hOP hP hx⟩,hx,rfl⟩

theorem posedKeySidePatch_intrinsic_closure {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ j c, 0 < keySideDistance k j c)
    (i : Fin n) (b : Bool) (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    Subtype.val '' closure
      (Subtype.val ⁻¹' posedKeySidePatch k i b W : Set (posedKeySidePlane k i b W)) =
        W '' keySideClosedFace k i b := by
  calc
    _ = closure (posedKeySidePatch k i b W) :=
      subtype_image_closure_preimage_of_closed _ _
        (posedKeySidePlane k i b W).closed_of_finiteDimensional
        (posedKeySidePatch_subset_plane k hd i b W)
    _ = W '' keySideClosedFace k i b := by
      change closure (W.toHomeomorph '' keySideStrictPatch k i b) = _
      rw [← W.toHomeomorph.image_closure,closure_keySideStrictPatch k hc hr hh hd i b]
      rfl

#print axioms posedKeySidePatch_nonempty_in_plane
#print axioms isOpen_posedKeySidePatch_in_plane
#print axioms posedKeySidePatch_intrinsic_closure
end SparseMonotiles
