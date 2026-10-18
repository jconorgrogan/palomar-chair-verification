module

public import SparseMonotiles.CarrierHierarchyAlignment
public import SparseMonotiles.IntegerGridConnected

@[expose] public section

/-!
All complete parent anchors occupy one common parity coset. The connectivity
argument is derived on the full integer cell grid; connectivity of an assumed
parent graph is not introduced as a new hierarchy premise.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem parent_has_cell {d : ℕ} (p : Pose d) (j : Fin d) :
    ParentOccupies p (p.cell (fun _ => 0)) := by
  change DoubleCell (p.inverseCell (p.cell (fun _ => 0)))
  rw [Pose.inverseCell_cell]
  exact ⟨fun _ => by norm_num, j, by norm_num⟩

theorem physical_parent_anchor_eq {d : ℕ} {r : Equiv.Perm (Fin d)}
    {hr : Function.Involutive r} {p q : Pose d}
    (h : physicalClass r hr p = physicalClass r hr q) : p.shift = q.shift :=
  gauge_shift_eq (Quotient.exact h)

private theorem grid_step_adjacent {d : ℕ} {c b : Cell d}
    (h : IntegerGridStep c b) : AdjacentCells c b := by
  obtain ⟨j, rfl | rfl⟩ := h
  · refine ⟨j, Or.inl ?_, ?_⟩
    · simp [integerGridUnit]
    · intro i hij
      simp [integerGridUnit, hij]
  · refine ⟨j, Or.inr ?_, ?_⟩
    · simp [integerGridUnit]
    · intro i hij
      simp [integerGridUnit, hij]

/-- Every pair of complete parent anchors differs by an even integer vector. -/
theorem RegisteredWorld.all_parents_even {d : ℕ} (W : RegisteredWorld d)
    (hd : 3 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (p₀ : Pose d) (hp₀ : CompleteParent σ r W.tiles p₀)
    (q : Pose d) (hq : CompleteParent σ r W.tiles q) :
    ∀ i, (q.shift i - p₀.shift i) % 2 = 0 := by
  classical
  let S : Set (Cell d) := {c | ∃ p, CompleteParent σ r W.tiles p ∧
    ParentOccupies p c ∧ ∀ i, (p.shift i - p₀.shift i) % 2 = 0}
  let j : Fin d := ⟨0, by omega⟩
  have hS : S = Set.univ := by
    apply integerGrid_eq_univ_of_step_closed
    · exact ⟨p₀.cell (fun _ => 0), p₀, hp₀, parent_has_cell p₀ j, by simp⟩
    · rintro c ⟨p, hp, hpc, hpp⟩ b hstep
      obtain ⟨P, ⟨s, _, hs, hsb⟩, _⟩ := W.parent_cells_tile hd hr he hL hl b
      have hps : ∀ i, (s.shift i - p.shift i) % 2 = 0 := by
        by_cases hclass : physicalClass r hr p = physicalClass r hr s
        · have heq := physical_parent_anchor_eq hclass
          intro i
          rw [← heq]
          simp
        · exact W.parent_contact_even (by omega) hr he hL hl hp hs hclass hpc hsb
            (grid_step_adjacent hstep)
      refine ⟨s, hs, hsb, ?_⟩
      intro i
      have h₁ := hpp i
      have h₂ := hps i
      omega
  have hmem : q.cell (fun _ => 0) ∈ S := by rw [hS]; trivial
  obtain ⟨p, hp, hpc, hpp⟩ := hmem
  have heq := physical_parent_anchor_eq
    (complete_parent_cells_unique (by omega) hr he W hp hq hpc (parent_has_cell q j))
  simpa only [heq] using hpp

#print axioms RegisteredWorld.all_parents_even
end SparseMonotiles.CarrierHierarchy
