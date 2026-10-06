module

public import SparseMonotiles.KeyCompanionFeatureMatchingApexPatches
public import SparseMonotiles.KeySideCreaseSeed

@[expose] public section

/-! # No actual canonical key side plane is a carrier coordinate plane
Coordinate variation is witnessed by literal points of the selected side.
Signed integral poses preserve this variation in every native coordinate.
-/
namespace SparseMonotiles
open Set

theorem keySidePlane_coordinate_varies {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (i : Fin n) (b : Bool) (a : Fin (n+1)) :
    ∃ x ∈ keySideAffinePlane k i b, x a ≠ rationalPoint k.apex a := by
  refine Fin.lastCases ?_ (fun j => ?_) a
  · refine ⟨keySideStrictPoint k i b,(mem_keySideAffinePlane_iff k hd i b _).mpr
      (keySideStrictPoint_mem k hh hd i b).1,?_⟩
    rw [keySideStrictPoint_last]
    change keyPyramidHeight k/2 ≠ keyPyramidHeight k
    linarith
  · by_cases hji : j=i
    · subst j
      refine ⟨keySideStrictPoint k i b,(mem_keySideAffinePlane_iff k hd i b _).mpr
        (keySideStrictPoint_mem k hh hd i b).1,?_⟩
      rw [keySideStrictPoint_tangent]
      simp only [ite_true]
      change ((if b then keyPyramidHi k i else keyPyramidLo k i)+keyPyramidApex k i)/2 ≠ keyPyramidApex k i
      have hdist := hd i b
      cases b <;> simp only [Bool.false_eq_true,if_false,if_true,keySideDistance] at hdist ⊢ <;> linarith
    · refine ⟨keySideCreasePoint k i j b false,(mem_keySideAffinePlane_iff k hd i b _).mpr
        (keySideCreasePoint_full_slacks k hh hd i j (Ne.symm hji) b false).1,?_⟩
      rw [keySideCreasePoint_tangent]
      simp only [if_neg hji,ite_true,Bool.false_eq_true,if_false]
      change (keyPyramidLo k j+keyPyramidApex k j)/2 ≠ keyPyramidApex k j
      have hdist := hd j false
      simp only [keySideDistance,Bool.false_eq_true,if_false] at hdist
      linarith

theorem posed_key_side_plane_not_coordinate {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (q : Contact.Pose (n+1)) (i : Fin n) (b : Bool) (a : Fin (n+1)) (c : ℝ) :
    ¬ ∀ x ∈ posedKeySidePlane k i b q.euclidean, x a=c := by
  intro h
  obtain ⟨x,hx,hxa⟩ := keySidePlane_coordinate_varies k hh hd i b (q.perm a)
  have hqapex := h (q.euclidean (rationalPoint k.apex))
    ((mem_posedKeySidePlane_iff k i b q.euclidean _).mpr (by
      rw [q.euclidean.symm_apply_apply]
      exact key_apex_mem_sideAffinePlane k i b))
  have hqx := h (q.euclidean x) ((mem_posedKeySidePlane_iff k i b q.euclidean _).mpr (by
    rw [q.euclidean.symm_apply_apply]; exact hx))
  have heq := hqx.trans hqapex.symm
  simp only [Contact.Pose.euclidean_apply] at heq
  have hsign : (q.sign a : ℝ) ≠ 0 := by
    cases hb : q.negative a <;> simp [Contact.Pose.sign,hb]
  exact hxa (mul_left_cancel₀ hsign (add_right_cancel heq))

/-- The conclusion is unchanged in an arbitrary physical tile frame. -/
theorem physical_key_side_plane_not_carrier_coordinate {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (q : Contact.Pose (n+1)) (g : Point (n+1) ≃ᵢ Point (n+1))
    (i : Fin n) (b : Bool) (a : Fin (n+1)) (c : ℝ) :
    ¬ ∀ x ∈ posedKeySidePlane k i b (q.euclidean.trans g.toRealAffineIsometryEquiv),
      g.symm x a=c := by
  intro h
  apply posed_key_side_plane_not_coordinate k hh hd q i b a c
  intro x hx
  have hx' : g x ∈ posedKeySidePlane k i b (q.euclidean.trans g.toRealAffineIsometryEquiv) := by
    apply (mem_posedKeySidePlane_iff k i b _ _).mpr
    change q.euclidean.symm (g.toRealAffineIsometryEquiv.symm (g x)) ∈ keySideAffinePlane k i b
    rw [show g.toRealAffineIsometryEquiv.symm (g x)=x from g.toRealAffineIsometryEquiv.symm_apply_apply x]
    exact (mem_posedKeySidePlane_iff k i b q.euclidean x).mp hx
  simpa only [g.symm_apply_apply] using h (g x) hx'

#print axioms posed_key_side_plane_not_coordinate
#print axioms physical_key_side_plane_not_carrier_coordinate
end SparseMonotiles
