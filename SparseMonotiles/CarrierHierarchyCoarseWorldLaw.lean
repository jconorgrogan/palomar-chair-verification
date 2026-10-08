module

public import SparseMonotiles.CarrierHierarchyCoarseSoundness

@[expose] public section

/-!
Turn an independently checked indexed coarse certificate into legality of the
constructed coarse world. Coarse face contacts are lifted to actual fine unit
faces; halving of relative poses is proved with the alignment hypotheses.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem normalize_coarse {d : ℕ} (origin : Cell d) (P Q : Pose d)
    (hP : ∀ i, (P.shift i - origin i) % 2 = 0)
    (hQ : ∀ i, (Q.shift i - origin i) % 2 = 0) :
    normalize (coarsePose origin P) (coarsePose origin Q) =
      coarsePose (fun _ => 0) (normalize P Q) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    have hp := hP (P.perm.symm i)
    have hq := hQ (P.perm.symm i)
    rcases Bool.eq_false_or_eq_true (P.negative (P.perm.symm i)) with h | h <;>
      simp [normalize, coarsePose, compose, inversePose, Pose.sign, h] <;> omega

private theorem parentBlock_fineCell {d : ℕ} (origin : Cell d) (P : Pose d)
    (hP : ∀ i, (P.shift i - origin i) % 2 = 0) (c : Cell d) :
    parentBlockLower P (fineCell origin c) = fineCell origin c := by
  funext i
  have hi := hP i
  simp only [parentBlockLower, fineCell]
  omega

/-- An actual coarse unit-face contact supplies a genuine fine parent-face
contact, without assuming that merely touching bounding boxes suffice. -/
theorem coarse_contact_lifts {d : ℕ} (origin : Cell d) (P Q : Pose d)
    (hP : ∀ i, (P.shift i - origin i) % 2 = 0)
    (hQ : ∀ i, (Q.shift i - origin i) % 2 = 0)
    (hcontact : CellContact (coarsePose origin P) (coarsePose origin Q)) :
    ∃ c b, ParentOccupies P c ∧ ParentOccupies Q b ∧ AdjacentCells c b := by
  obtain ⟨c, b, hc, hb, j, hj, hij⟩ := hcontact
  have hpc := (coarse_occupies_iff origin P hP c).mp hc
  have hqb := (coarse_occupies_iff origin Q hQ b).mp hb
  rcases hj with hj | hj
  · let x : Cell d := fun i => fineCell origin c i + unitAxis j i
    refine ⟨x, fineCell origin b, hpc.block_fill ?_, hqb, j, Or.inl ?_, ?_⟩
    · intro i
      rw [parentBlock_fineCell origin P hP c]
      by_cases h : i = j <;> simp [x, unitAxis, h]
    · simp [x, fineCell, unitAxis, hj]
      ring
    · intro i hji
      simp [x, fineCell, unitAxis, hji, hij i hji]
  · let y : Cell d := fun i => fineCell origin b i + unitAxis j i
    refine ⟨fineCell origin c, y, hpc, hqb.block_fill ?_, j, Or.inr ?_, ?_⟩
    · intro i
      rw [parentBlock_fineCell origin Q hQ b]
      by_cases h : i = j <;> simp [y, unitAxis, h]
    · simp [y, fineCell, unitAxis, hj]
      ring
    · intro i hji
      simp [y, fineCell, unitAxis, hji, hij i hji]

private theorem centers_eq_of_parent_class {d : ℕ} (W : RegisteredWorld d) (j : Fin d)
    {r : Equiv.Perm (Fin d)} {hr : Function.Involutive r} {t s : Pose d}
    (ht : t ∈ W.tiles) (hs : s ∈ W.tiles)
    (h : physicalClass r hr (centralParent t) = physicalClass r hr (centralParent s)) : t = s := by
  have hg : GaugeRel r (centralParent t) (centralParent s) := Quotient.exact h
  have hc := centralChild_respects_gauge r hg
  simp only [centralChild_parent] at hc
  have htOwn : Occupies t (t.cell (fun _ => 0)) :=
    (root_occupies_cell t _).mpr ⟨fun _ => Or.inl rfl, j, rfl⟩
  exact W.disjoint t ht s hs _ htOwn ((gauge_occupies_iff hc _).mp htOwn)

/-- The concrete arithmetic certificate closes the remaining legality premise
for the actual halved parent world. No whole hierarchy is an input. -/
theorem RegisteredWorld.coarsen_legal {d : ℕ} {ρ : Type}
    (W : RegisteredWorld d) (hd : 3 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : IsCanonicalTable σ C)
    (hGauge : GaugeClosed r L) (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (rows : ρ → CoarseRow d)
    (valid : ∀ i, (rows i).witness.Valid C L (rows i).pose)
    (covered : ∀ a ∈ C, ∀ b ∈ C, ∀ k ∈ L,
      (∀ j, (parentCandidate a b k).shift j % 2 = 0) →
      ∃ i, parentCandidate a b k = (rows i).pose)
    (p₀ : Pose d) (hp₀ : CompleteParent σ r W.tiles p₀) :
    (W.coarsen hd hr he hL hl p₀ hp₀).Legal L := by
  rintro p ⟨t, ht, hpt, rfl⟩ q ⟨s, hs, hps, rfl⟩ hne hcontact
  have hEvenT := W.all_parents_even hd hr he hL hl p₀ hp₀ (centralParent t) hpt
  have hEvenS := W.all_parents_even hd hr he hL hl p₀ hp₀ (centralParent s) hps
  have hclass : physicalClass r hr (centralParent t) ≠ physicalClass r hr (centralParent s) := by
    intro h
    let j : Fin d := ⟨0, by omega⟩
    have hts := centers_eq_of_parent_class W j ht hs h
    subst s
    exact hne rfl
  obtain ⟨c, b, hc, hb, hadj⟩ := coarse_contact_lifts p₀.shift _ _ hEvenT hEvenS hcontact
  have hk := indexed_coarse_certificate_sound W (by omega) hr he C L hC hGauge hL hl
    rows valid covered hpt hps hclass hc hb hadj
  rw [normalize_coarse p₀.shift _ _ hEvenT hEvenS]
  exact hk

#print axioms normalize_coarse
#print axioms coarse_contact_lifts
#print axioms RegisteredWorld.coarsen_legal
end SparseMonotiles.CarrierHierarchy
