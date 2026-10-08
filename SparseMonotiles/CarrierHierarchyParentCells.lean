module

public import SparseMonotiles.CarrierHierarchyPartition

@[expose] public section

/-!
The complete parents really tile all registered unit cells by doubled chair
supports. The exact all-odd offset obstruction is proved using full side-two
constituent blocks, without assuming alignment in advance.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def ParentOccupies {d : ℕ} (p : Pose d) (c : Cell d) : Prop := DoubleCell (p.inverseCell c)

theorem parent_support_dissection {d : ℕ}
    (σ : Bits d → Equiv.Perm (Fin d)) (p : Pose d) (c : Cell d) :
    ParentOccupies p c ↔ ∃ q ∈ children σ p, Occupies q c := by
  constructor
  · intro h
    rcases (canonical_dissection σ _).mp h with hc | ⟨a, ha, hc⟩
    · refine ⟨centralChild p, Or.inl rfl, ?_⟩
      rw [← compose_central, ← p.cell_inverseCell c]
      exact (occupies_compose_cell p (centralPose _) _).mpr hc
    · refine ⟨compose p (outerPose a (σ a)), Or.inr ⟨a, ha, rfl⟩, ?_⟩
      rw [← p.cell_inverseCell c]
      exact (occupies_compose_cell p _ _).mpr hc
  · rintro ⟨q, hq, hqc⟩
    apply (canonical_dissection σ _).mpr
    rcases hq with rfl | ⟨a, ha, rfl⟩
    · left
      apply (occupies_compose_cell p (centralPose _) _).mp
      simpa [compose_central, p.cell_inverseCell] using hqc
    · right
      refine ⟨a, ha, ?_⟩
      apply (occupies_compose_cell p _ _).mp
      simpa [p.cell_inverseCell] using hqc

theorem CompleteParent.owns_cell {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} {tiles : Set (Pose d)} {p : Pose d}
    (h : CompleteParent σ r tiles p) {c : Cell d} (hc : ParentOccupies p c) :
    ∃ q ∈ tiles, ParentContains σ r p q ∧ Occupies q c := by
  obtain ⟨s, hs, hsc⟩ := (parent_support_dissection σ p c).mp hc
  obtain ⟨q, hq, hg⟩ := h s hs
  exact ⟨q, hq, ⟨s, hs, hg⟩, (gauge_occupies_iff hg c).mp hsc⟩

theorem complete_parent_cells_unique {d : ℕ} (hd : 2 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (W : RegisteredWorld d) {p q : Pose d}
    (hp : CompleteParent σ r W.tiles p) (hq : CompleteParent σ r W.tiles q)
    {c : Cell d} (hpc : ParentOccupies p c) (hqc : ParentOccupies q c) :
    physicalClass r hr p = physicalClass r hr q := by
  obtain ⟨s, hs, hps, hsc⟩ := hp.owns_cell hpc
  obtain ⟨t, ht, hqt, htc⟩ := hq.owns_cell hqc
  have hst := W.disjoint s hs t ht c hsc htc
  subst t
  exact complete_parent_unique hd hr he W.tiles W.disjoint hp hq hps hqt

/-- The actual doubled-carrier supports cover and have unique physical owners. -/
theorem RegisteredWorld.parent_cells_tile {d : ℕ} (W : RegisteredWorld d)
    (hd : 3 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (c : Cell d) : ∃! P : PhysicalPose r hr, ∃ p, physicalClass r hr p = P ∧
      CompleteParent σ r W.tiles p ∧ ParentOccupies p c := by
  obtain ⟨t, ht, htc⟩ := W.covers c
  obtain ⟨p, hp, s, hs, hst⟩ := W.complete_parent_exists hd hL hl t ht
  have hpc : ParentOccupies p c := (parent_support_dissection σ p c).mpr
    ⟨s, hs, (gauge_occupies_iff hst c).mpr htc⟩
  refine ⟨physicalClass r hr p, ⟨p, rfl, hp, hpc⟩, ?_⟩
  rintro P ⟨q, hqP, hq, hqc⟩
  exact hqP.symm.trans (complete_parent_cells_unique (by omega) hr he W hq hp hqc hpc)

def parentBlockLower {d : ℕ} (p : Pose d) (c : Cell d) : Cell d :=
  fun i => c i - (c i - p.shift i) % 2

theorem parentBlock_contains {d : ℕ} (p : Pose d) (c : Cell d) (i : Fin d) :
    c i = parentBlockLower p c i ∨ c i = parentBlockLower p c i + 1 := by
  simp only [parentBlockLower]
  omega

theorem parentBlock_parity {d : ℕ} (p : Pose d) (c : Cell d) (i : Fin d) :
    (parentBlockLower p c i - p.shift i) % 2 = 0 := by
  simp only [parentBlockLower]
  omega

private theorem inverseCell_row {d : ℕ} (p : Pose d) (c : Cell d) (i : Fin d) :
    p.inverseCell c (p.perm i) =
      if p.negative i then p.shift i - 1 - c i else c i - p.shift i := by
  simp only [Pose.inverseCell, Equiv.symm_apply_apply, Pose.sign]
  rcases Bool.eq_false_or_eq_true (p.negative i) with h | h <;> simp [h] <;> omega

/-- Every parent-owned cell lies in a wholly owned side-two constituent block. -/
theorem ParentOccupies.block_fill {d : ℕ} {p : Pose d} {c : Cell d}
    (hc : ParentOccupies p c) {b : Cell d}
    (hb : ∀ i, b i = parentBlockLower p c i ∨ b i = parentBlockLower p c i + 1) :
    ParentOccupies p b := by
  obtain ⟨hbound, j, hj⟩ := hc
  constructor
  · intro k
    obtain ⟨i, rfl⟩ := p.perm.surjective k
    have hi := hbound (p.perm i)
    have hbi := hb i
    rw [inverseCell_row] at hi ⊢
    simp only [parentBlockLower] at hbi
    rcases Bool.eq_false_or_eq_true (p.negative i) with h | h <;>
      simp [h] at hi ⊢ <;> omega
  · obtain ⟨i, rfl⟩ := p.perm.surjective j
    refine ⟨p.perm i, ?_⟩
    have hi := hbound (p.perm i)
    have hbi := hb i
    rw [inverseCell_row] at hi hj ⊢
    simp only [parentBlockLower] at hbi
    rcases Bool.eq_false_or_eq_true (p.negative i) with h | h <;>
      simp [h] at hi hj ⊢ <;> omega

/-- All-odd parent anchor displacement cannot support a disjoint face contact.
It forces an explicit common occupied cell of the two constituent blocks. -/
theorem odd_parent_contact_overlap {d : ℕ} {p q : Pose d} {c b : Cell d}
    (hp : ParentOccupies p c) (hq : ParentOccupies q b)
    (hadj : AdjacentCells c b) (hodd : ∀ i, (q.shift i - p.shift i) % 2 = 1) :
    ∃ x, ParentOccupies p x ∧ ParentOccupies q x := by
  obtain ⟨j, hj, hij⟩ := hadj
  let x : Cell d := fun i => max (parentBlockLower p c i) (parentBlockLower q b i)
  have hdist : ∀ i, parentBlockLower p c i ≤ parentBlockLower q b i + 1 ∧
      parentBlockLower q b i ≤ parentBlockLower p c i + 1 := by
    intro i
    have hpc := parentBlock_contains p c i
    have hqb := parentBlock_contains q b i
    have hpp := parentBlock_parity p c i
    have hqp := parentBlock_parity q b i
    have ho := hodd i
    by_cases hi : i = j
    · subst i
      omega
    · have he := hij i hi
      omega
  refine ⟨x, hp.block_fill ?_, hq.block_fill ?_⟩
  · intro i
    have hd := hdist i
    have hl := le_max_left (parentBlockLower p c i) (parentBlockLower q b i)
    have hu : x i ≤ parentBlockLower p c i + 1 := max_le (by omega) hd.2
    change x i = parentBlockLower p c i ∨ x i = parentBlockLower p c i + 1
    change parentBlockLower p c i ≤ x i at hl
    omega
  · intro i
    have hd := hdist i
    have hl := le_max_right (parentBlockLower p c i) (parentBlockLower q b i)
    have hu : x i ≤ parentBlockLower q b i + 1 := max_le hd.1 (by omega)
    change x i = parentBlockLower q b i ∨ x i = parentBlockLower q b i + 1
    change parentBlockLower q b i ≤ x i at hl
    omega

#print axioms RegisteredWorld.parent_cells_tile
#print axioms ParentOccupies.block_fill
#print axioms odd_parent_contact_overlap
end SparseMonotiles.CarrierHierarchy
