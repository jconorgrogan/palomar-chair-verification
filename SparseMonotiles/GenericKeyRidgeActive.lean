module

public import SparseMonotiles.CanonicalPoseUniqueness
public import SparseMonotiles.CanonicalRidgeRank
public import SparseMonotiles.GenericRidgePoints

@[expose] public section

/-!
# Actual key incidence at generic codimension-two ridge points

An active plane is required to contain the ridge. This is the conclusion of
our proved generic-point selection, rather than an assumed bound on the
number of active facets. The key apex and any third independent facet are
excluded by the actual two-dimensional normal space.
-/
namespace SparseMonotiles

open Set

/-- Exact affine changes of frame preserve ridge codimension. -/
theorem affineEquiv_map_ridge_finrank {d : ℕ}
    (e : Point d ≃ᵃ[ℝ] Point d) (R : AffineSubspace ℝ (Point d)) :
    Module.finrank ℝ (R.map e.toAffineMap).direction = Module.finrank ℝ R.direction := by
  rw [AffineSubspace.map_direction]
  exact e.linear.finrank_map_eq R.direction

/-- Any coordinate-independent family of active key facets fits in the
actual two-dimensional ridge normal space. -/
theorem key_ridge_independent_active_card_le_two {n : ℕ} {ι : Type*} [Fintype ι]
    (k : KeyData (n+1)) (hh : 0 < keyPyramidHeight k)
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (R : AffineSubspace ℝ (Point (n+1)))
    (hcodim : Module.finrank ℝ R.direction + 2 = n+1)
    {p : Point (n+1)} (hpR : p ∈ R)
    (f : ι → PyramidFacetIndex n)
    (hf : Function.Injective (pyramidFacetCoordinate ∘ f))
    (hzero : ∀ a, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (f a)) p = 0)
    (hactive : ∀ j, keyPyramidHalfspaceSlack k j p = 0 →
      ∀ x ∈ R, keyPyramidHalfspaceSlack k j x = 0) : Fintype.card ι ≤ 2 := by
  let N := fun a => pyramidFacetSlopeNormal (keySideSlope k) (f a)
  have hN : LinearIndependent ℝ N := pyramidFacetSlopeNormal_linearIndependent
    (keySideSlope k) (fun i b => div_ne_zero (ne_of_gt hh) (ne_of_gt (hd i b))) f hf
  have hm (a : ι) : N a ∈ R.directionᗮ := by
    apply normal_mem_ridge_orthogonal (show (R : Set (Point (n+1))).Nonempty from ⟨p,hpR⟩)
      (show R ≤ R from le_rfl)
    intro x hx
    apply (key_facet_form_eq_iff_normal_inner_eq k hd (f a) x p).mp
    exact (sub_eq_zero.mp (hactive _ (hzero a) x hx)).symm.trans
      (sub_eq_zero.mp (hzero a))
  have hN' : LinearIndependent ℝ (fun a => (⟨N a, hm a⟩ : R.directionᗮ)) :=
    LinearIndependent.of_comp R.directionᗮ.subtype hN
  have hrank : Module.finrank ℝ R.directionᗮ = 2 := by
    apply ridge_orthogonal_finrank_two R
    simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hcodim
  simpa only [hrank] using hN'.fintype_card_le_finrank

/-- The apex lies on every genuine side plane of the actual key. -/
theorem key_apex_side_slack_zero {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    keyPyramidHalfspaceSlack k (.inr (i,b)) (rationalPoint k.apex) = 0 := by
  have h := (mem_pyramidFacetPlane_iff (keyPyramidLo k) (keyPyramidHi k)
    (keyPyramidApex k) (keyPyramidHeight k) (some (i,b))
    (keyPyramidApex k, keyPyramidHeight k)).mp
    (apex_mem_pyramidSidePlane _ _ _ _ i b)
  exact sub_eq_zero.mpr h.symm

/-- Three distinct tangential directions already exclude the apex. No local
facet-count or non-apex premise is used. -/
theorem key_ridge_point_ne_apex {n : ℕ} (hn : 3 ≤ n)
    (k : KeyData (n+1)) (hh : 0 < keyPyramidHeight k)
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (R : AffineSubspace ℝ (Point (n+1)))
    (hcodim : Module.finrank ℝ R.direction + 2 = n+1)
    {p : Point (n+1)} (hpR : p ∈ R)
    (hactive : ∀ j, keyPyramidHalfspaceSlack k j p = 0 →
      ∀ x ∈ R, keyPyramidHalfspaceSlack k j x = 0) :
    p ≠ rationalPoint k.apex := by
  intro hp
  let f : Fin 3 → PyramidFacetIndex n := fun a => some (⟨a.val, lt_of_lt_of_le a.isLt hn⟩, false)
  have hf : Function.Injective (pyramidFacetCoordinate ∘ f) := by
    intro a b h
    apply Fin.ext
    simpa [Function.comp_def, f, pyramidFacetCoordinate] using h
  have hcard := key_ridge_independent_active_card_le_two k hh hd R hcodim hpR f hf
    (fun a => by rw [hp]; exact key_apex_side_slack_zero k _ false) hactive
  simp only [Fintype.card_fin] at hcard
  omega

/-- Every family of distinct active facets below the apex has at most two
members. The coordinate independence is derived from the actual pyramid. -/
theorem key_ridge_active_facets_card_le_two {n : ℕ} {ι : Type*} [Fintype ι]
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (R : AffineSubspace ℝ (Point (n+1)))
    (hcodim : Module.finrank ℝ R.direction + 2 = n+1)
    {p : Point (n+1)} (hpR : p ∈ R) (hpk : p ∈ keySolid k)
    (hne : p ≠ rationalPoint k.apex)
    (f : ι → PyramidFacetIndex n) (hf : Function.Injective f)
    (hzero : ∀ a, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (f a)) p = 0)
    (hactive : ∀ j, keyPyramidHalfspaceSlack k j p = 0 →
      ∀ x ∈ R, keyPyramidHalfspaceSlack k j x = 0) : Fintype.card ι ≤ 2 := by
  have hph := key_height_lt_of_ne_apex k hc hr hh hpk hne
  have hmem (a : ι) : pointPyramidEquiv n p ∈
      pyramidFacetPlane (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k)
        (keyPyramidHeight k) (f a) := by
    rw [mem_pyramidFacetPlane_iff]
    exact (sub_eq_zero.mp (hzero a)).symm
  have hinj : Function.Injective (pyramidFacetCoordinate ∘ f) := by
    intro a b hab
    apply hf
    exact pyramidFacetCoordinate_injOn_active_below_apex
      (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k) hw hph
      ((mem_pyramidActiveFacets _ _ _ _ _ _).mpr (hmem a))
      ((mem_pyramidActiveFacets _ _ _ _ _ _).mpr (hmem b)) hab
  exact key_ridge_independent_active_card_le_two k hh hd R hcodim hpR f hinj hzero hactive

/-- The redundant top equation is inactive away from the apex, so the same
bound applies to the full exact H-representation. -/
theorem key_ridge_active_halfspaces_card_le_two {n : ℕ}
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (R : AffineSubspace ℝ (Point (n+1)))
    (hcodim : Module.finrank ℝ R.direction + 2 = n+1)
    {p : Point (n+1)} (hpR : p ∈ R) (hpk : p ∈ keySolid k)
    (hne : p ≠ rationalPoint k.apex)
    (hactive : ∀ j, keyPyramidHalfspaceSlack k j p = 0 →
      ∀ x ∈ R, keyPyramidHalfspaceSlack k j x = 0) :
    Nat.card {j : PyramidHalfspaceIndex n // keyPyramidHalfspaceSlack k j p = 0} ≤ 2 := by
  classical
  let I := {j : PyramidHalfspaceIndex n // keyPyramidHalfspaceSlack k j p = 0}
  let f : I → PyramidFacetIndex n := fun j =>
    Classical.choose (active_key_halfspace_is_facet k hc hr hh hpk hne j.val j.property)
  have heq (j : I) : pyramidFacetHalfspaceIndex (f j) = j.val :=
    (Classical.choose_spec (active_key_halfspace_is_facet k hc hr hh hpk hne j.val j.property)).1
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rw [← heq a, ← heq b, hab]
  have hz (a : I) : keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (f a)) p = 0 := by
    rw [heq a]
    exact a.property
  have h := key_ridge_active_facets_card_le_two k hc hr hh hw hd R hcodim hpR hpk hne
    f hinj hz hactive
  simpa only [Nat.card_eq_fintype_card] using h

/-- At a generic ridge point, two distinct active equations exhaust the
active H-representation. This discharges the omitted-slack premise of the
physical closed-wedge theorem. -/
theorem key_ridge_other_slacks_ne_zero {n : ℕ}
    (k : KeyData (n+1)) {p : Point (n+1)}
    (hcard : Nat.card {j : PyramidHalfspaceIndex n // keyPyramidHalfspaceSlack k j p = 0} ≤ 2)
    {j l : PyramidHalfspaceIndex n} (hjl : j ≠ l)
    (hj : keyPyramidHalfspaceSlack k j p = 0)
    (hl : keyPyramidHalfspaceSlack k l p = 0) :
    ∀ m, m ≠ j → m ≠ l → keyPyramidHalfspaceSlack k m p ≠ 0 := by
  classical
  intro m hmj hml hm
  let f : Fin 3 → {a : PyramidHalfspaceIndex n // keyPyramidHalfspaceSlack k a p = 0} :=
    ![⟨j,hj⟩, ⟨l,hl⟩, ⟨m,hm⟩]
  have hf : Function.Injective f := by
    intro a b hab
    have hval := congrArg Subtype.val hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hle := Fintype.card_le_of_injective f hf
  have hle' : 3 ≤ Nat.card {a : PyramidHalfspaceIndex n // keyPyramidHalfspaceSlack k a p = 0} := by
    simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using hle
  omega

#print axioms affineEquiv_map_ridge_finrank
#print axioms key_ridge_point_ne_apex
#print axioms key_ridge_active_facets_card_le_two
#print axioms key_ridge_active_halfspaces_card_le_two
#print axioms key_ridge_other_slacks_ne_zero

end SparseMonotiles
