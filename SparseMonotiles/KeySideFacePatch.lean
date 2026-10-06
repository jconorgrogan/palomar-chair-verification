module

public import SparseMonotiles.StripCreaseCrossingChart
public import SparseMonotiles.Compactness
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-! Concrete relative-open side patches of the actual canonical box pyramid.
The strict point is constructed explicitly; all closure, convexity and
boundedness hypotheses used in full-face K1 are then derived. -/
namespace SparseMonotiles
open Set

noncomputable def keySideStrictPatch {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    Set (Point (n+1)) :=
  {x | keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0 ∧
    ∀ j : PyramidHalfspaceIndex n, j ≠ .inr (i,b) → 0 < keyPyramidHalfspaceSlack k j x}

noncomputable def keySideClosedFace {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    Set (Point (n+1)) := keySolid k ∩ {x | keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0}

noncomputable def keySideStrictPoint {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    Point (n+1) := (pointPyramidEquiv n).symm
      ((fun j => if j=i then ((if b then keyPyramidHi k i else keyPyramidLo k i)+keyPyramidApex k i)/2
        else keyPyramidApex k j), keyPyramidHeight k/2)

@[simp] theorem keySideStrictPoint_last {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    keySideStrictPoint k i b (Fin.last n) = keyPyramidHeight k/2 :=
  congrArg Prod.snd ((pointPyramidEquiv n).apply_symm_apply _)

@[simp] theorem keySideStrictPoint_tangent {n : ℕ} (k : KeyData (n+1)) (i j : Fin n) (b : Bool) :
    keySideStrictPoint k i b j.castSucc =
      if j=i then ((if b then keyPyramidHi k i else keyPyramidLo k i)+keyPyramidApex k i)/2
      else keyPyramidApex k j :=
  congrArg (fun z : PyramidPoint n => z.1 j) ((pointPyramidEquiv n).apply_symm_apply _)

theorem keySideStrictPoint_side_slack {n : ℕ} (k : KeyData (n+1))
    (i j : Fin n) (b c : Bool) :
    keyPyramidHalfspaceSlack k (.inr (j,c)) (keySideStrictPoint k i b) =
      (keyPyramidHeight k/2) *
        (if j=i then if c=b then 0 else keyPyramidHi k i-keyPyramidLo k i
          else keySideDistance k j c) := by
  by_cases hji : j=i
  · subst j
    cases b <;> cases c <;>
      simp [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
        keyPyramidHalfspaceNormal_apply,keySideStrictPoint_tangent,keySideDistance] <;> ring
  · cases b <;> cases c <;>
      simp [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
        keyPyramidHalfspaceNormal_apply,keySideStrictPoint_tangent,keySideDistance,hji] <;> ring

/-- The midpoint of the apex and a base-side point is strict for all omitted
full H-representation inequalities, including the top-height inequality. -/
theorem keySideStrictPoint_mem {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (hd : ∀ j c, 0 < keySideDistance k j c)
    (i : Fin n) (b : Bool) : keySideStrictPoint k i b ∈ keySideStrictPatch k i b := by
  refine ⟨?_,?_⟩
  · rw [keySideStrictPoint_side_slack]
    simp
  · intro j hj
    rcases j with c | ⟨j,c⟩
    · cases c <;> change 0 < _ - _
      · simp only [keyPyramidHalfspaceBound,pyramidHalfspaceBound,
          keyPyramidHalfspaceNormal_apply,keySideStrictPoint_last]
        linarith
      · simp only [keyPyramidHalfspaceBound,pyramidHalfspaceBound,
          keyPyramidHalfspaceNormal_apply,keySideStrictPoint_last]
        linarith
    · rw [keySideStrictPoint_side_slack]
      apply mul_pos (by linarith)
      by_cases hji : j=i
      · subst j
        have hcb : c ≠ b := fun h => hj (by rw [h])
        simp only [ite_true,if_pos (Eq.refl i),if_neg hcb]
        have hlo := hd i false
        have hhi := hd i true
        simp only [keySideDistance,Bool.false_eq_true,if_false,if_true] at hlo hhi
        linarith
      · simpa only [if_neg hji] using hd j c

theorem keyPyramidHalfspaceSlack_combo {n : ℕ} (k : KeyData (n+1))
    (j : PyramidHalfspaceIndex n) (x y : Point (n+1)) (a b : ℝ) (hab : a+b=1) :
    keyPyramidHalfspaceSlack k j (a • x+b • y) =
      a*keyPyramidHalfspaceSlack k j x+b*keyPyramidHalfspaceSlack k j y := by
  simp only [keyPyramidHalfspaceSlack,map_add,map_smul,smul_eq_mul]
  have h := congrArg (fun t : ℝ => t*keyPyramidHalfspaceBound k j) hab
  nlinarith

theorem convex_keySideStrictPatch {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool) :
    Convex ℝ (keySideStrictPatch k i b) := by
  intro x hx y hy a c ha hc hac
  constructor
  · rw [keyPyramidHalfspaceSlack_combo k _ x y a c hac,hx.1,hy.1]
    ring
  · intro j hj
    rw [keyPyramidHalfspaceSlack_combo k j x y a c hac]
    have hxp := hx.2 j hj
    have hyp := hy.2 j hj
    have hax := mul_nonneg ha hxp.le
    have hcy := mul_nonneg hc hyp.le
    by_cases ha0 : a=0
    · have hc1 : c=1 := by linarith
      simpa [ha0,hc1] using hyp
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hxp) hcy

theorem keySideStrictPatch_subset_face {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (i : Fin n) (b : Bool) :
    keySideStrictPatch k i b ⊆ keySideClosedFace k i b := by
  intro x hx
  refine ⟨(mem_keySolid_iff_nonneg_slacks k hc hr hh x).mpr ?_,hx.1⟩
  intro j
  by_cases hj : j=.inr (i,b)
  · subst j; exact hx.1.ge
  · exact (hx.2 j hj).le

theorem isClosed_keySideClosedFace {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (i : Fin n) (b : Bool) :
    IsClosed (keySideClosedFace k i b) := by
  have hclosed : IsClosed (keySolid k) := by
    rw [keySolid_eq_iInter_halfspaces k hc hr hh]
    exact isClosed_iInter (fun j => isClosed_le
      (keyPyramidHalfspaceNormal k j).continuous_of_finiteDimensional continuous_const)
  exact hclosed.inter (isClosed_eq (continuous_keyPyramidHalfspaceSlack k _) continuous_const)

theorem closure_keySideStrictPatch {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ j c, 0 < keySideDistance k j c)
    (i : Fin n) (b : Bool) :
    closure (keySideStrictPatch k i b) = keySideClosedFace k i b := by
  apply Subset.antisymm
  · exact closure_minimal (keySideStrictPatch_subset_face k hc hr hh i b)
      (isClosed_keySideClosedFace k hc hr hh i b)
  · intro x hx
    let y := keySideStrictPoint k i b
    have hy : y ∈ keySideStrictPatch k i b := keySideStrictPoint_mem k hh hd i b
    have hsegment : openSegment ℝ x y ⊆ keySideStrictPatch k i b := by
      rintro z ⟨a,c,ha,hc',hac,rfl⟩
      constructor
      · rw [keyPyramidHalfspaceSlack_combo k _ x y a c hac,hx.2,hy.1]
        ring
      · intro j hj
        rw [keyPyramidHalfspaceSlack_combo k _ x y a c hac]
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg ha.le ((mem_keySolid_iff_nonneg_slacks k hc hr hh x).mp hx.1 j))
          (mul_pos hc' (hy.2 j hj))
    exact closure_mono hsegment (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

theorem isOpen_keySideStrictPatch_in_plane {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ j c, 0 < keySideDistance k j c) (i : Fin n) (b : Bool) :
    IsOpen (Subtype.val ⁻¹' keySideStrictPatch k i b : Set (keySideAffinePlane k i b)) := by
  classical
  have heq : (Subtype.val ⁻¹' keySideStrictPatch k i b : Set (keySideAffinePlane k i b)) =
      {x : keySideAffinePlane k i b | ∀ j : {j : PyramidHalfspaceIndex n // j ≠ .inr (i,b)},
        0 < keyPyramidHalfspaceSlack k j (x : Point (n+1))} := by
    ext x
    simp only [Set.mem_preimage,keySideStrictPatch,Set.mem_setOf_eq]
    constructor
    · intro h j; exact h.2 j j.property
    · intro h
      exact ⟨(mem_keySideAffinePlane_iff k hd i b x).mp x.property,fun j hj => h ⟨j,hj⟩⟩
  rw [heq,Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const ((continuous_keyPyramidHalfspaceSlack k j).comp continuous_subtype_val)

theorem keySideStrictPatch_bounded {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (i : Fin n) (b : Bool) :
    Bornology.IsBounded (keySideStrictPatch k i b) :=
  (keySolid_isBounded k).subset
    (fun _ hx => (keySideStrictPatch_subset_face k hc hr hh i b hx).1)

#print axioms keySideStrictPoint_mem
#print axioms closure_keySideStrictPatch
#print axioms isOpen_keySideStrictPatch_in_plane
end SparseMonotiles
