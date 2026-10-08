module
public import RegisteredPrime.GridPaths
@[expose] public section
namespace RegisteredPrime

theorem relative_even_same_anchor_parity {p : Nat} (t u : Pose p)
    (he : ∀ i, (t.relative u).anchor i % 2 = 0) :
    ∀ i, t.anchor i % 2 = u.anchor i % 2 := by
  intro i
  have h := even_relative_box_parity t u he i
  cases ht : t.frame.negative i <;> cases hu : u.frame.negative i <;>
    simp [boxLower, bit, ht, hu] at h <;> omega

theorem same_anchor_parity_relative_even {p : Nat} (t u : Pose p)
    (he : ∀ i, t.anchor i % 2 = u.anchor i % 2) :
    ∀ i, (t.relative u).anchor i % 2 = 0 := by
  intro i
  have h := he (t.frame.inverse i)
  rw [relative_anchor]
  cases hn : t.frame.negative (t.frame.inverse i) <;>
    simp [RegisteredFrame.sign, hn] <;> omega

theorem complete_parent_cell_cover (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (c : Cell P.p) :
    ∃ t, CompleteParent P W t ∧ DoubledOccupies t c := by
  obtain ⟨q, hq, hqc⟩ := W.covers c
  obtain ⟨t, ht, a, ha⟩ := registered_complete_parent_pose P W hl q hq
  exact ⟨t, ht, (doubled_occupies_iff_child P t c).mpr ⟨a, ha ▸ hqc⟩⟩

theorem complete_parent_common_cell (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) (c : Cell P.p)
    (htc : DoubledOccupies t c) (huc : DoubledOccupies u c) : t = u := by
  apply Classical.byContradiction
  intro hne
  exact CompleteParent.doubled_disjoint P W hl t u ht hu hne c ⟨htc, huc⟩

theorem doubled_parent_origin_cell (P : Parameters) (t : Pose P.p) :
    DoubledOccupies t (t.cell (fun _ => 0)) := by
  unfold DoubledOccupies
  rw [Pose.inv_cell_cell]
  exact ⟨fun _ => ⟨by simp, by simp⟩,
    ⟨⟨0, by have := P.prime.two_le; omega⟩, by simp⟩⟩

/-- Full cell coverage propagates the proved edgewise alignment to every
recognized parent, even parents that are not neighbors. -/
theorem complete_parents_same_anchor_parity (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) :
    ∀ i, t.anchor i % 2 = u.anchor i % 2 := by
  let F : Cell P.p → Prop := fun c => ∀ v, CompleteParent P W v → DoubledOccupies v c →
    ∀ i, v.anchor i % 2 = t.anchor i % 2
  have hstart : F (t.cell (fun _ => 0)) := by
    intro v hv hvc i
    have he := complete_parent_common_cell P W hl v t hv ht _ hvc (doubled_parent_origin_cell P t)
    rw [he]
  have hstep : ∀ a b, Adjacent a b → F a → F b := by
    intro a b hab hfa v hv hvb
    obtain ⟨w, hw, hwa⟩ := complete_parent_cell_cover P W hl a
    have hwp := hfa w hw hwa
    by_cases he : w = v
    · subst v
      exact hwp
    · have hc : DoubledFaceContact w v :=
        ⟨CompleteParent.doubled_disjoint P W hl w v hw hv he, a, b, hwa, hvb, hab⟩
      have hpar := relative_even_same_anchor_parity w v
        (child_legal_parent_even P w v hc (CompleteParent.child_legal P W hl w v hw hv))
      intro i
      exact (hpar i).symm.trans (hwp i)
  have h := cell_property_global F hstep _ hstart (u.cell (fun _ => 0))
  intro i
  exact (h u hu (doubled_parent_origin_cell P u) i).symm

/-- Every complete parent has an even relative anchor in any chosen complete
parent's full frame. This is the actual global registration coset theorem. -/
theorem complete_parents_relative_even (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) : ∀ i, (t.relative u).anchor i % 2 = 0 :=
  same_anchor_parity_relative_even t u (complete_parents_same_anchor_parity P W hl t u ht hu)

end RegisteredPrime
