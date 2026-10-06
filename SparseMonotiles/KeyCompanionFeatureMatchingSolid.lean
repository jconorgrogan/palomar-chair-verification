module

public import SparseMonotiles.KeyCompanionFeatureMatchingSideSupport
public import SparseMonotiles.KeyCompanionFeatureMatchingNoncoordinate
public import SparseMonotiles.KeyCompanionFeatureMatchingConvex
public import SparseMonotiles.KeyCompanionFeatureMatchingCompact
public import SparseMonotiles.GlobalBodyAffine

@[expose] public section

/-! # Actual whole-solid coincidence from the apex and side-plane match
Finite closed key supports remove all carrier restrictions. Each connected
closed side belongs to the common-apex key. Convexity gives solid inclusion,
and compact congruence upgrades it to equality without a base-plane premise.
-/
namespace SparseMonotiles
open Set

theorem whole_key_coincidence_of_common_apex_side_planes {n : ℕ}
    (k₀ : KeyData (n+1))
    (hc : k₀.centre (Fin.last n)=0) (hr : k₀.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k₀) (hd : ∀ i b, 0 < keySideDistance k₀ i b)
    (i₀ : Fin n) (ks : List (KeyData (n+1))) (T : Set (Point (n+1)))
    (hkeyclosed : ∀ a ∈ ks, IsClosed (keySolid a))
    (hdisjoint : ∀ a ∈ ks, ∀ c ∈ ks, a ≠ c → Disjoint (keySolid a) (keySolid c))
    (hboundary : ∀ x ∈ frontier T, (∃ l ∈ ks, x ∈ keySolid l) ∨
      ∃ a : CarrierHalfspaceIndex (n+1), carrierHalfspaceSlack a x=0)
    {l : KeyData (n+1)} (hl : l ∈ ks) (q : Contact.Pose (n+1))
    (hq : keySolid l=q.euclidean '' keySolid k₀)
    (g : Point (n+1) ≃ᵢ Point (n+1))
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (hside : ∀ i b, W '' keySideClosedFace k₀ i b ⊆ frontier (g '' T))
    (hapex : W (rationalPoint k₀.apex)=g (q.euclidean (rationalPoint k₀.apex)))
    (σ : (Fin n × Bool) ≃ (Fin n × Bool))
    (hplanes : ∀ a, posedKeySidePlane k₀ a.1 a.2 W=
      posedKeySidePlane k₀ (σ a).1 (σ a).2 (q.euclidean.trans g.toRealAffineIsometryEquiv)) :
    W '' keySolid k₀=g '' keySolid l := by
  classical
  let V : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1) := q.euclidean.trans g.toRealAffineIsometryEquiv
  let I := {a : KeyData (n+1) // a ∈ ks}
  letI : Fintype I := ks.finite_toSet.fintype
  let K : I → Set (Point (n+1)) := fun a => g '' keySolid a.val
  let H : CarrierHalfspaceIndex (n+1) → AffineSubspace ℝ (Point (n+1)) := fun a =>
    affineFormPlane ((carrierSlackAffine a).comp g.symm.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap) 0
  have hclosed : ∀ a, IsClosed (K a) := fun a => g.toHomeomorph.isClosedMap _ (hkeyclosed a.val a.property)
  have hdis : ∀ a c, a ≠ c → Disjoint (K a) (K c) := by
    intro a c hac
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,hzy⟩
    have hval : a.val ≠ c.val := fun h => hac (Subtype.ext h)
    exact Set.disjoint_left.mp (hdisjoint a.val a.property c.val c.property hval)
      hy (g.injective hzy ▸ hz)
  have hpK : W (rationalPoint k₀.apex) ∈ K ⟨l,hl⟩ := by
    rw [hapex]
    refine ⟨q.euclidean (rationalPoint k₀.apex),?_,rfl⟩
    rw [hq]
    exact ⟨_,subset_convexHull ℝ _ (Set.mem_insert _ _),rfl⟩
  have hsupport : ∀ i b, W '' keySideClosedFace k₀ i b ⊆ K ⟨l,hl⟩ := by
    intro i b
    apply closed_key_side_subset_anchored_support k₀ hc hr hh hd i b W K hclosed hdis ⟨l,hl⟩ hpK H
    · intro a hle
      have hzero : ∀ x ∈ posedKeySidePlane k₀ (σ (i,b)).1 (σ (i,b)).2 V,
          carrierHalfspaceSlack a (g.symm x)=0 := by
        intro x hx
        have hroot : x ∈ posedKeySidePlane k₀ i b W := by rw [hplanes (i,b)]; exact hx
        have hz := (mem_affineFormPlane _ _ _).mp (hle hroot)
        change carrierSlackAffine a (g.symm x)=0 at hz
        simpa only [carrierSlackAffine_apply] using hz
      rcases a with ⟨a,c⟩
      fin_cases c
      · apply physical_key_side_plane_not_carrier_coordinate k₀ hh hd q g
          (σ (i,b)).1 (σ (i,b)).2 a 0
        intro x hx
        simpa [carrierHalfspaceSlack] using hzero x hx
      · apply physical_key_side_plane_not_carrier_coordinate k₀ hh hd q g
          (σ (i,b)).1 (σ (i,b)).2 a 2
        intro x hx
        have hz := hzero x hx
        simp [carrierHalfspaceSlack] at hz
        linarith
      · apply physical_key_side_plane_not_carrier_coordinate k₀ hh hd q g
          (σ (i,b)).1 (σ (i,b)).2 a 1
        intro x hx
        have hz := hzero x hx
        simp [carrierHalfspaceSlack] at hz
        linarith
    · intro x hx
      have hxF : x ∈ g '' frontier T := by
        change x ∈ g.toHomeomorph '' frontier T
        rw [g.toHomeomorph.image_frontier]
        exact hside i b hx
      have hxnative : g.symm x ∈ frontier T := by
        obtain ⟨y,hy,hey⟩ := hxF
        rw [← hey,g.symm_apply_apply]
        exact hy
      rcases hboundary (g.symm x) hxnative with ⟨a,ha,hxa⟩ | ⟨a,ha⟩
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨a,ha⟩,g.symm x,hxa,g.apply_symm_apply x⟩)
      · apply Or.inr
        refine ⟨a,(mem_affineFormPlane _ _ _).mpr ?_⟩
        change carrierSlackAffine a (g.symm x)=0
        simpa only [carrierSlackAffine_apply] using ha
  have hconv : Convex ℝ (K ⟨l,hl⟩) :=
    Convex.affine_image g.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap (convex_convexHull ℝ _)
  have hincl := posed_keySolid_subset_convex_of_closed_sides k₀ hc hr i₀ W hconv hsupport
  have hVK : K ⟨l,hl⟩=V '' keySolid k₀ := by
    change g '' keySolid l=V '' keySolid k₀
    rw [hq,Set.image_image]
    rfl
  rw [hVK] at hincl
  have hcompact : IsCompact (keySolid k₀) := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    refine ⟨?_,keySolid_isBounded k₀⟩
    rw [keySolid_eq_iInter_halfspaces k₀ hc hr hh]
    exact isClosed_iInter (fun j => isClosed_le
      (keyPyramidHalfspaceNormal k₀ j).continuous_of_finiteDimensional continuous_const)
  have heq := compact_congruent_images_eq_of_subset hcompact
    W.toIsometryEquiv V.toIsometryEquiv hincl
  change W '' keySolid k₀=V '' keySolid k₀ at heq
  rw [← hVK] at heq
  exact heq

#print axioms whole_key_coincidence_of_common_apex_side_planes
end SparseMonotiles
