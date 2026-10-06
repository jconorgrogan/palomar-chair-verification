module

public import SparseMonotiles.StripCreaseCrossingRank
public import SparseMonotiles.GenericKeyRidgeActive
public import SparseMonotiles.KeySlackNormals

@[expose] public section

/-! # Constructed Euclidean charts of actual key side planes -/
namespace SparseMonotiles
open Set

/-- The selected actual side plane, based at the key apex. -/
noncomputable def keySideAffinePlane {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    AffineSubspace ℝ (Point (n+1)) :=
  normalAffineIntersection
    (fun _ : Fin 1 => pyramidFacetSlopeNormal (keySideSlope k) (some (i,b)))
    (rationalPoint k.apex)

theorem key_apex_mem_sideAffinePlane {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    rationalPoint k.apex ∈ keySideAffinePlane k i b := by
  rw [keySideAffinePlane,mem_normalAffineIntersection_iff]
  exact fun _ => rfl

/-- The normal-defined plane is exactly the selected actual affine equation. -/
theorem mem_keySideAffinePlane_iff {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ j b, 0 < keySideDistance k j b) (i : Fin n) (b : Bool) (x : Point (n+1)) :
    x ∈ keySideAffinePlane k i b ↔ keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0 := by
  rw [keySideAffinePlane,mem_normalAffineIntersection_iff]
  have heq := key_facet_form_eq_iff_normal_inner_eq k hd (some (i,b)) x (rationalPoint k.apex)
  have hapex := key_apex_side_slack_zero k i b
  constructor
  · intro hx
    have hform := heq.mpr (hx 0)
    change keyPyramidHalfspaceNormal k (.inr (i,b)) x =
      keyPyramidHalfspaceNormal k (.inr (i,b)) (rationalPoint k.apex) at hform
    change keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0
    unfold keyPyramidHalfspaceSlack at hapex ⊢
    rw [hform]
    exact hapex
  · intro hx _
    apply heq.mp
    exact (sub_eq_zero.mp hx).symm.trans (sub_eq_zero.mp hapex)

/-- Its direction has the required Euclidean dimension `n`, proved from
its nonzero actual normal. -/
theorem keySideAffinePlane_direction_finrank {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    Module.finrank ℝ (keySideAffinePlane k i b).direction = n := by
  have hN : LinearIndependent ℝ
      (fun _ : Fin 1 => pyramidFacetSlopeNormal (keySideSlope k) (some (i,b))) :=
    linearIndependent_unique_iff.mpr (pyramidFacetSlopeNormal_ne_zero (keySideSlope k) (some (i,b)))
  have h := normalAffineIntersection_codimension _ hN (rationalPoint k.apex)
  simp only [Fintype.card_fin] at h
  change Module.finrank ℝ (keySideAffinePlane k i b).direction+1=n+1 at h
  omega

/-- Translation of the Euclidean direction space to the apex gives an
explicit affine-isometric chart into the full supporting plane. -/
noncomputable def keySideChart {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    (keySideAffinePlane k i b).direction →ᵃⁱ[ℝ] Point (n+1) := by
  let R := keySideAffinePlane k i b
  let p : R := ⟨rationalPoint k.apex,key_apex_mem_sideAffinePlane k i b⟩
  letI : Nonempty R := ⟨p⟩
  exact R.subtypeₐᵢ.comp (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry

/-- Every chart point satisfies the chosen actual side equation. -/
theorem keySideChart_selected_zero {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ j b, 0 < keySideDistance k j b) (i : Fin n) (b : Bool)
    (x : (keySideAffinePlane k i b).direction) :
    keyPyramidHalfspaceSlack k (.inr (i,b)) (keySideChart k i b x) = 0 := by
  letI : Nonempty (keySideAffinePlane k i b) :=
    ⟨⟨rationalPoint k.apex,key_apex_mem_sideAffinePlane k i b⟩⟩
  apply (mem_keySideAffinePlane_iff k hd i b _).mp
  exact (AffineIsometryEquiv.vaddConst ℝ
    (⟨rationalPoint k.apex,key_apex_mem_sideAffinePlane k i b⟩ : keySideAffinePlane k i b) x).property

/-- The chart covers the whole supporting plane, rather than only a subset. -/
theorem range_keySideChart {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    Set.range (keySideChart k i b) = (keySideAffinePlane k i b : Set (Point (n+1))) := by
  let R := keySideAffinePlane k i b
  let p : R := ⟨rationalPoint k.apex,key_apex_mem_sideAffinePlane k i b⟩
  letI : Nonempty R := ⟨p⟩
  let e := AffineIsometryEquiv.vaddConst ℝ p
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    exact (e v).property
  · intro hx
    refine ⟨e.symm ⟨x,hx⟩,?_⟩
    change (e (e.symm ⟨x,hx⟩) : Point (n+1)) = x
    simp

#print axioms mem_keySideAffinePlane_iff
#print axioms keySideAffinePlane_direction_finrank
#print axioms keySideChart_selected_zero
#print axioms range_keySideChart
end SparseMonotiles
