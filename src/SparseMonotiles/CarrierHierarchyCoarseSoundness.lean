module

public import SparseMonotiles.CarrierHierarchyCoarseChecker

@[expose] public section

/-!
Soundness of each finite coarse rejection, and of an indexed necessity-only
certificate. A completed concrete certificate supplies arithmetic row checks and
coverage of all aligned child witnesses, not a coarsening theorem as a premise.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem inverseCell_compose_cell {d : ℕ} (p q : Pose d) (c : Cell d) :
    (compose p q).inverseCell (p.cell c) = q.inverseCell c := by
  apply cell_injective (compose p q)
  rw [Pose.cell_inverseCell, compose_cell, Pose.cell_inverseCell]

theorem parent_compose_cell {d : ℕ} (p q : Pose d) (c : Cell d) :
    ParentOccupies (compose p q) (p.cell c) ↔ ParentOccupies q c := by
  simp only [ParentOccupies, inverseCell_compose_cell]

private theorem canonical_child_in_parent {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} (P : Pose d) {a : Pose d}
    (ha : a ∈ children σ (rootPose d)) : compose P a ∈ children σ P := by
  rcases ha with h | ⟨b, hb, h⟩
  · have hh : a = centralPose d := h
    rw [hh, compose_central]
    exact Or.inl rfl
  · rw [compose_root_left] at h
    rw [h]
    exact Or.inr ⟨b, hb, rfl⟩

/-- Every accepted, overlap, or forbidden-child row has the promised logical
meaning for a pair of actual complete parents in a fine legal world. -/
theorem CoarseWitness.sound {d : ℕ} (W : RegisteredWorld d)
    (hd : 2 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : IsCanonicalTable σ C)
    (hGauge : GaugeClosed r L) (hl : W.Legal L)
    {P Q : Pose d} (hP : CompleteParent σ r W.tiles P) (hQ : CompleteParent σ r W.tiles Q)
    (hne : physicalClass r hr P ≠ physicalClass r hr Q)
    {w : CoarseWitness d} (hw : w.Valid C L (normalize P Q)) :
    coarsePose (fun _ => 0) (normalize P Q) ∈ L := by
  cases w with
  | member => exact hw
  | overlap c =>
      obtain ⟨hroot, hF⟩ := hw
      have hPc : ParentOccupies P (P.cell c) := by
        simpa only [compose_root_right] using (parent_compose_cell P (rootPose d) c).mpr hroot
      have hQc : ParentOccupies Q (P.cell c) := by
        simpa only [compose_normalize] using (parent_compose_cell P (normalize P Q) c).mpr hF
      exact False.elim (hne (complete_parent_cells_unique hd hr he W hP hQ hPc hQc))
  | illegalChild a b c e =>
      obtain ⟨ha, hb, hac, hbe, hadj, hbad⟩ := hw
      have haP := canonical_child_in_parent P (hC.2 a ha)
      have hbQ := canonical_child_in_parent Q (hC.2 b hb)
      obtain ⟨s, hs, hgs⟩ := hP _ haP
      obtain ⟨t, ht, hgt⟩ := hQ _ hbQ
      have hsc : Occupies s (P.cell c) := (gauge_occupies_iff hgs _).mp
        ((occupies_compose_cell P a c).mpr hac)
      have hte : Occupies t (P.cell e) := by
        apply (gauge_occupies_iff hgt _).mp
        have h := (occupies_compose_cell P (compose (normalize P Q) b) e).mpr hbe
        simpa only [← compose_assoc, compose_normalize] using h
      have hst : s ≠ t := by
        intro h
        subst t
        exact hne (complete_parent_unique hd hr he W.tiles W.disjoint hP hQ
          ⟨_, haP, hgs⟩ ⟨_, hbQ, hgt⟩)
      have hlegal := hl s hs t ht hst ⟨_, _, hsc, hte, adjacent_cell_image P hadj⟩
      have hk := hGauge.normal_congr hr (hgs.symm hr) (hgt.symm hr) hlegal
      rw [normalized_parent_children] at hk
      exact False.elim (hbad hk)

theorem normalize_even_of_anchors {d : ℕ} (P Q : Pose d)
    (hEven : ∀ i, (Q.shift i - P.shift i) % 2 = 0) :
    ∀ i, (normalize P Q).shift i % 2 = 0 := by
  intro i
  have hi := hEven (P.perm.symm i)
  rcases Bool.eq_false_or_eq_true (P.negative (P.perm.symm i)) with h | h <;>
    simp [normalize, compose, inversePose, Pose.sign, h] <;> omega

/-- Indexed certificate coverage need only include the aligned canonical
child-witness triples. Actual parent alignment is supplied by a proved theorem. -/
theorem indexed_coarse_certificate_sound {d : ℕ} {ρ : Type}
    (W : RegisteredWorld d) (hd : 2 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : IsCanonicalTable σ C)
    (hGauge : GaugeClosed r L) (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (rows : ρ → CoarseRow d)
    (valid : ∀ i, (rows i).witness.Valid C L (rows i).pose)
    (covered : ∀ a ∈ C, ∀ b ∈ C, ∀ k ∈ L,
      (∀ j, (parentCandidate a b k).shift j % 2 = 0) →
      ∃ i, parentCandidate a b k = (rows i).pose)
    {P Q : Pose d} (hP : CompleteParent σ r W.tiles P) (hQ : CompleteParent σ r W.tiles Q)
    (hne : physicalClass r hr P ≠ physicalClass r hr Q)
    {c b : Cell d} (hPc : ParentOccupies P c) (hQb : ParentOccupies Q b)
    (hadj : AdjacentCells c b) : coarsePose (fun _ => 0) (normalize P Q) ∈ L := by
  obtain ⟨a, ha, b, hb, k, hk, hF⟩ :=
    W.canonical_parent_witness hd hr he C L hC.1 hGauge hl hP hQ hne hPc hQb hadj
  have hEven := normalize_even_of_anchors P Q
    (W.parent_contact_even hd hr he hL hl hP hQ hne hPc hQb hadj)
  rw [hF] at hEven
  obtain ⟨i, hi⟩ := covered a ha b hb k hk hEven
  have hv : (rows i).witness.Valid C L (normalize P Q) := by
    rw [hF, hi]
    exact valid i
  exact CoarseWitness.sound W hd hr he C L hC hGauge hl hP hQ hne hv

#print axioms CoarseWitness.sound
#print axioms indexed_coarse_certificate_sound
end SparseMonotiles.CarrierHierarchy
