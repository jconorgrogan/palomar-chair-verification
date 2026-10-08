module

public import SparseMonotiles.PhysicalKeyModelInventory

@[expose] public section

/-! # Boundary key ridge models retaining every active plane equation
All constants are excluded by the physical boundary premise. The remaining
model exposes actual zero equations, so its affine halfspaces pull back to
homogeneous halfspaces in the common ridge normal space.
-/
namespace SparseMonotiles
open Set

theorem localSetEq_closed_wedge_with_active_equations {n : ℕ}
    (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k)
    (hwidth : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (q : Contact.Pose (n + 1)) (bump : Bool)
    {p : Point (n + 1)} {T : Set (Point (n + 1))}
    (hp : q.euclidean.symm p ∈ keySolid k)
    (hne : q.euclidean.symm p ≠ rationalPoint k.apex)
    {j l : PyramidHalfspaceIndex n} (hjl : j ≠ l)
    (hj : keyPyramidHalfspaceSlack k j (q.euclidean.symm p) = 0)
    (hl : keyPyramidHalfspaceSlack k l (q.euclidean.symm p) = 0)
    (hother : ∀ m, m ≠ j → m ≠ l →
      keyPyramidHalfspaceSlack k m (q.euclidean.symm p) ≠ 0)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun m x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x)) (.inl false) bump))) :
    (∃ i si, keyPyramidHalfspaceSlack k (.inl false) (q.euclidean.symm p) = 0 ∧
      keyPyramidHalfspaceSlack k (.inr (i,si)) (q.euclidean.symm p) = 0 ∧
      LocalSetEq p T (closedBaseSideWedge
      (fun m x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x))
        (.inl false) (.inr (i, si)) bump)) ∨
    (∃ i r si sr, i ≠ r ∧
      keyPyramidHalfspaceSlack k (.inr (i,si)) (q.euclidean.symm p) = 0 ∧
      keyPyramidHalfspaceSlack k (.inr (r,sr)) (q.euclidean.symm p) = 0 ∧
      LocalSetEq p T (closedSideSideWedge
      (fun m x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x))
        (.inr (i, si)) (.inr (r, sr)) bump)) := by
  have hcont (m : PyramidHalfspaceIndex n) :
      Continuous (fun x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x)) :=
    (continuous_keyPyramidHalfspaceSlack k m).comp q.euclidean.symm.continuous
  have hnonneg := (mem_keySolid_iff_nonneg_slacks k hc hr hh _).mp hp
  have hpos (m : PyramidHalfspaceIndex n) (hmj : m ≠ j) (hml : m ≠ l) :
      0 < keyPyramidHalfspaceSlack k m (q.euclidean.symm p) :=
    lt_of_le_of_ne (hnonneg m) (Ne.symm (hother m hmj hml))
  obtain ⟨a, c, ha, hc', hpair⟩ := active_key_halfspace_pair_classification
    k hc hr hh hwidth hp hne hjl hj hl
  cases a with
  | none =>
      cases c with
      | none => exact (show False from hpair).elim
      | some s =>
          rcases s with ⟨i, si⟩
          simp only [pyramidFacetHalfspaceIndex] at ha hc'
          subst j l
          refine Or.inl ⟨i, si, hj, hl, hT.trans ?_⟩
          apply localSetEq_closure_merged_base_side _ _ _ _ _ (by simp) hcont
          · intro m hm0 hmi
            exact hpos m hm0 hmi
          · exact closure_key_base_side_dent_posed k hh q i si
  | some s =>
      rcases s with ⟨i, si⟩
      cases c with
      | none =>
          simp only [pyramidFacetHalfspaceIndex] at ha hc'
          subst j l
          refine Or.inl ⟨i, si, hl, hj, hT.trans ?_⟩
          apply localSetEq_closure_merged_base_side _ _ _ _ _ (by simp) hcont
          · intro m hm0 hmi
            exact hpos m hmi hm0
          · exact closure_key_base_side_dent_posed k hh q i si
      | some t =>
          rcases t with ⟨r, sr⟩
          simp only [pyramidFacetHalfspaceIndex] at ha hc'
          subst j l
          refine Or.inr ⟨i, r, si, sr, hpair, hj, hl, hT.trans ?_⟩
          apply localSetEq_closure_merged_side_side _ _ _ _ _ _ (by simp) (by simp)
            hcont (hpos (.inl false) (by simp) (by simp))
          · intro m _ hmi hmr
            exact hpos m hmi hmr
          · exact closure_key_side_negative_posed k hh q i si
          · exact closure_key_side_negative_posed k hh q r sr

/-- Nonconstant boundary models and the precise active equations. -/
def IsActiveKeyRidgeModel {n : ℕ}
    (slack : PyramidHalfspaceIndex n → Point (n+1) → ℝ)
    (b : Bool) (p : Point (n+1)) (M : Set (Point (n+1))) : Prop :=
  (slack (.inl false) p = 0 ∧
    M = (if b then {x | slack (.inl false) x ≤ 0} else {x | 0 ≤ slack (.inl false) x})) ∨
  (∃ i si, slack (.inr (i,si)) p = 0 ∧
    M = (if b then {x | 0 ≤ slack (.inr (i,si)) x} else {x | slack (.inr (i,si)) x ≤ 0})) ∨
  (∃ i si, slack (.inl false) p = 0 ∧ slack (.inr (i,si)) p = 0 ∧
    M = closedBaseSideWedge slack (.inl false) (.inr (i,si)) b) ∨
  (∃ i r si sr, i ≠ r ∧ slack (.inr (i,si)) p = 0 ∧ slack (.inr (r,sr)) p = 0 ∧
    M = closedSideSideWedge slack (.inr (i,si)) (.inr (r,sr)) b)

/-- Exact boundary inventory, both on and off the key solid. -/
theorem localSetEq_active_keyRidgeModel_inventory {n : ℕ}
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (q : Contact.Pose (n+1)) (b : Bool)
    {p : Point (n+1)} {T : Set (Point (n+1))} (hpT : p ∈ frontier T)
    (hgeneric : q.euclidean.symm p ∈ keySolid k →
      q.euclidean.symm p ≠ rationalPoint k.apex ∧
      Nat.card {j : PyramidHalfspaceIndex n //
        keyPyramidHalfspaceSlack k j (q.euclidean.symm p) = 0} ≤ 2)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)) (.inl false) b))) :
    ∃ M, IsActiveKeyRidgeModel (fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)) b p M ∧
      LocalSetEq p T M := by
  classical
  let slack := fun j x => keyPyramidHalfspaceSlack k j (q.euclidean.symm x)
  have hcont (j) : Continuous (slack j) :=
    (continuous_keyPyramidHalfspaceSlack k j).comp q.euclidean.symm.continuous
  have hconstant (hcst : LocalSetEq p T (if b then univ else ∅)) : False := by
    have h := hcst.frontier.mem_iff.mp hpT
    cases b <;> simp at h
  by_cases hp : q.euclidean.symm p ∈ keySolid k
  · obtain ⟨hne,hcard⟩ := hgeneric hp
    have hnonneg (j) : 0 ≤ slack j p :=
      (mem_keySolid_iff_nonneg_slacks k hc hr hh _).mp hp j
    by_cases htwo : ∃ j l, j ≠ l ∧ slack j p = 0 ∧ slack l p = 0
    · rcases htwo with ⟨j,l,hjl,hj,hl⟩
      have hother := key_ridge_other_slacks_ne_zero k hcard hjl hj hl
      rcases localSetEq_closed_wedge_with_active_equations k hc hr hh hw q b
        hp hne hjl hj hl hother hT with ⟨i,si,hbase,hside,h⟩ | ⟨i,r,si,sr,hir,hi,hr,h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl ⟨i,si,hbase,hside,rfl⟩)), h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨i,r,si,sr,hir,hi,hr,rfl⟩)), h⟩
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
            exact ⟨_, Or.inr (Or.inl ⟨i,si,hj,rfl⟩), h⟩
      · have hpos (j) (hj : j ≠ (.inl false : PyramidHalfspaceIndex n)) : 0 < slack j p := by
          apply lt_of_le_of_ne (hnonneg j)
          intro hz
          exact hside ⟨j,hj,hz.symm⟩
        exact (hconstant (hT.trans (localSetEq_closure_mergedKeyRegion_of_nonbase_strict slack
          (.inl false) b p (fun j => (hcont j).continuousAt) hpos))).elim
  · have hnot : ¬ ∀ j, 0 ≤ slack j p := by
      exact fun h => hp ((mem_keySolid_iff_nonneg_slacks k hc hr hh _).mpr h)
    push_neg at hnot
    obtain ⟨j,hj⟩ := hnot
    by_cases hbase : j = (.inl false : PyramidHalfspaceIndex n)
    · subst j
      exact (hconstant (hT.trans (localSetEq_closure_merged_of_base_negative slack
        (.inl false) b p (hcont _) hj))).elim
    · have h := hT.trans (localSetEq_closure_merged_of_nonbase_negative slack
        (.inl false) j b p hbase hcont hj)
      have hboundary := h.frontier.mem_iff.mp hpT
      have hz : slack (.inl false) p = 0 := by
        cases b
        · exact ((frontier_le_subset_eq continuous_const (hcont _)) hboundary).symm
        · exact (frontier_le_subset_eq (hcont _) continuous_const) hboundary
      exact ⟨_, Or.inl ⟨hz,rfl⟩, h⟩

#print axioms localSetEq_closed_wedge_with_active_equations
#print axioms localSetEq_active_keyRidgeModel_inventory
end SparseMonotiles
