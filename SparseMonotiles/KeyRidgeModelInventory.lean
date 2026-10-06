module

public import SparseMonotiles.PhysicalKeyRidgeActive
public import SparseMonotiles.TwoPlaneWedgeModels

@[expose] public section

/-!
# Zero-, one-, and two-plane material germs of an isolated key

At a generic key point, the proved active-plane cardinality gives a complete
constant/halfspace/two-plane inventory. This is an equality of actual local
closed material sets; identifying their planar angles is a subsequent step.
-/
namespace SparseMonotiles
open Set

/-- A single side equation gives a genuine halfspace for either material sign. -/
theorem localSetEq_closure_merged_single_side
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (slack : ι → X → ℝ) (base side : ι) (b : Bool) (p : X)
    (hside : side ≠ base) (hf : ∀ i, Continuous (slack i))
    (hbase : 0 < slack base p)
    (hother : ∀ i, i ≠ base → i ≠ side → 0 < slack i p)
    (hclose : closure {x | slack side x < 0} = {x | slack side x ≤ 0}) :
    LocalSetEq p (closure (mergedKeyRegion slack base b))
      (if b then {x | 0 ≤ slack side x} else {x | slack side x ≤ 0}) := by
  have h := localSetEq_closure_merged_side_side slack base side side b p
    hside hside hf hbase (fun i hi hj _ => hother i hi hj) hclose hclose
  cases b <;> simpa [closedSideSideWedge] using h

/-- The explicit material inventory for the genuine base and side planes. -/
def IsKeyRidgeModel {n : ℕ} (slack : PyramidHalfspaceIndex n → Point (n+1) → ℝ)
    (b : Bool) (M : Set (Point (n+1))) : Prop :=
  M = univ ∨ M = ∅ ∨
  M = (if b then {x | slack (.inl false) x ≤ 0} else {x | 0 ≤ slack (.inl false) x}) ∨
  (∃ i si, M = (if b then {x | 0 ≤ slack (.inr (i,si)) x}
    else {x | slack (.inr (i,si)) x ≤ 0})) ∨
  (∃ i si, M = closedBaseSideWedge slack (.inl false) (.inr (i,si)) b) ∨
  (∃ i r si sr, i ≠ r ∧ M = closedSideSideWedge slack (.inr (i,si)) (.inr (r,sr)) b)

/-- Complete inventory at a point lying in the actual key solid. -/
theorem localSetEq_keyRidgeModel_of_mem_key {n : ℕ}
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (q : Contact.Pose (n+1)) (b : Bool)
    {p : Point (n+1)} {T : Set (Point (n+1))}
    (hp : q.euclidean.symm p ∈ keySolid k)
    (hne : q.euclidean.symm p ≠ rationalPoint k.apex)
    (hcard : Nat.card {j : PyramidHalfspaceIndex n //
      keyPyramidHalfspaceSlack k j (q.euclidean.symm p) = 0} ≤ 2)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)) (.inl false) b))) :
    ∃ M, IsKeyRidgeModel (fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)) b M ∧
      LocalSetEq p T M := by
  classical
  let slack := fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)
  have hcont (j) : Continuous (slack j) :=
    (continuous_keyPyramidHalfspaceSlack k j).comp q.euclidean.symm.continuous
  have hnonneg (j) : 0 ≤ slack j p :=
    (mem_keySolid_iff_nonneg_slacks k hc hr hh _).mp hp j
  by_cases htwo : ∃ j l, j ≠ l ∧ slack j p = 0 ∧ slack l p = 0
  · rcases htwo with ⟨j,l,hjl,hj,hl⟩
    have hother := key_ridge_other_slacks_ne_zero k hcard hjl hj hl
    rcases localSetEq_closed_wedge_of_two_active_key_planes k hc hr hh hw q b
      hp hne hjl hj hl hother hT with ⟨i,si,h⟩ | ⟨i,r,si,sr,hir,h⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,si,rfl⟩)))), h⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,r,si,sr,hir,rfl⟩)))), h⟩
  · by_cases hside : ∃ j, j ≠ (.inl false : PyramidHalfspaceIndex n) ∧ slack j p = 0
    · rcases hside with ⟨j,hjb,hj⟩
      obtain ⟨a,ha,_⟩ := active_key_halfspace_is_facet k hc hr hh hp hne j hj
      cases a with
      | none => exact (hjb ha.symm).elim
      | some u =>
          rcases u with ⟨i,si⟩
          change Sum.inr (i,si) = j at ha
          subst j
          have hbase : 0 < slack (.inl false) p := by
            apply lt_of_le_of_ne (hnonneg _)
            intro hz
            exact htwo ⟨.inl false, .inr (i,si), by simp, hz.symm, hj⟩
          have hother (l) (_ : l ≠ (.inl false : PyramidHalfspaceIndex n))
              (hl : l ≠ .inr (i,si)) : 0 < slack l p := by
            apply lt_of_le_of_ne (hnonneg l)
            intro hz
            exact htwo ⟨l, .inr (i,si), hl, hz.symm, hj⟩
          have h := hT.trans (localSetEq_closure_merged_single_side slack (.inl false)
            (.inr (i,si)) b p (by simp) hcont hbase hother
            (closure_key_side_negative_posed k hh q i si))
          exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl ⟨i,si,rfl⟩))), h⟩
    · have hpos (j) (hj : j ≠ (.inl false : PyramidHalfspaceIndex n)) : 0 < slack j p := by
        apply lt_of_le_of_ne (hnonneg j)
        intro hz
        exact hside ⟨j,hj,hz.symm⟩
      have h := hT.trans (localSetEq_closure_mergedKeyRegion_of_nonbase_strict slack
        (.inl false) b p (fun j => (hcont j).continuousAt) hpos)
      cases b
      · exact ⟨∅, Or.inr (Or.inl rfl), h⟩
      · exact ⟨univ, Or.inl rfl, h⟩

/-- Complete inventory also outside the key: a violated side leaves the
carrier halfspace, and a violated base gives constant material. -/
theorem localSetEq_keyRidgeModel_inventory {n : ℕ}
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (q : Contact.Pose (n+1)) (b : Bool)
    {p : Point (n+1)} {T : Set (Point (n+1))}
    (hgeneric : q.euclidean.symm p ∈ keySolid k →
      q.euclidean.symm p ≠ rationalPoint k.apex ∧
      Nat.card {j : PyramidHalfspaceIndex n //
        keyPyramidHalfspaceSlack k j (q.euclidean.symm p) = 0} ≤ 2)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)) (.inl false) b))) :
    ∃ M, IsKeyRidgeModel (fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)) b M ∧
      LocalSetEq p T M := by
  classical
  by_cases hp : q.euclidean.symm p ∈ keySolid k
  · exact localSetEq_keyRidgeModel_of_mem_key k hc hr hh hw q b hp
      (hgeneric hp).1 (hgeneric hp).2 hT
  · have hnot : ¬ ∀ j, 0 ≤ keyPyramidHalfspaceSlack k j (q.euclidean.symm p) := by
      exact fun h => hp ((mem_keySolid_iff_nonneg_slacks k hc hr hh _).mpr h)
    push_neg at hnot
    obtain ⟨j,hj⟩ := hnot
    let slack := fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)
    have hcont (j) : Continuous (slack j) :=
      (continuous_keyPyramidHalfspaceSlack k j).comp q.euclidean.symm.continuous
    by_cases hbase : j = (.inl false : PyramidHalfspaceIndex n)
    · subst j
      have h := hT.trans (localSetEq_closure_merged_of_base_negative slack
        (.inl false) b p (hcont _) hj)
      cases b
      · exact ⟨∅, Or.inr (Or.inl rfl), h⟩
      · exact ⟨univ, Or.inl rfl, h⟩
    · have h := hT.trans (localSetEq_closure_merged_of_nonbase_negative slack
        (.inl false) j b p hbase hcont hj)
      exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩

#print axioms localSetEq_closure_merged_single_side
#print axioms localSetEq_keyRidgeModel_of_mem_key
#print axioms localSetEq_keyRidgeModel_inventory
end SparseMonotiles
