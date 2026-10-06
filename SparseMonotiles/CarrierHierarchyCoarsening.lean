module

public import SparseMonotiles.CarrierHierarchyCoset

@[expose] public section

/-!
Construction of the actual registered coarse carrier tiling. Parent anchors are
first proved aligned in a common coset; only then are they divided by two.
The selected parent representative is fixed by its actual central fine tile.
Coarse contact-law legality is deliberately not asserted by this module.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem rightGauge_parentOccupies {d : ℕ} (r : Equiv.Perm (Fin d))
    (p : Pose d) (c : Cell d) : ParentOccupies (rightGauge r p) c ↔ ParentOccupies p c := by
  change DoubleCell (fun i => p.inverseCell c (r.symm i)) ↔ DoubleCell (p.inverseCell c)
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => by simpa using h (r j), r.symm i, hi⟩
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => h (r.symm j), r i, by simpa using hi⟩

theorem gauge_parentOccupies {d : ℕ} {r : Equiv.Perm (Fin d)}
    {p q : Pose d} (h : GaugeRel r p q) (c : Cell d) : ParentOccupies p c ↔ ParentOccupies q c := by
  rcases h with rfl | rfl
  · rfl
  · exact (rightGauge_parentOccupies r p c).symm

/-- One representative of each complete physical parent is determined by an
actual fine central tile already present in the global world. -/
theorem CompleteParent.actual_center {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {tiles : Set (Pose d)} {p : Pose d} (hp : CompleteParent σ r tiles p) :
    ∃ t ∈ tiles, GaugeRel r p (centralParent t) ∧ CompleteParent σ r tiles (centralParent t) := by
  obtain ⟨t, ht, hg⟩ := hp (centralChild p) (Or.inl rfl)
  have hgp := centralParent_respects_gauge r hg
  simp only [centralParent_child] at hgp
  exact ⟨t, ht, hgp, hp.of_gauge hr he hgp⟩

private theorem actual_centers_eq {d : ℕ} (W : RegisteredWorld d) (j : Fin d)
    {r : Equiv.Perm (Fin d)} {hr : Function.Involutive r} {t s : Pose d}
    (ht : t ∈ W.tiles) (hs : s ∈ W.tiles)
    (h : physicalClass r hr (centralParent t) = physicalClass r hr (centralParent s)) : t = s := by
  have hg : GaugeRel r (centralParent t) (centralParent s) := Quotient.exact h
  have hc := centralChild_respects_gauge r hg
  simp only [centralChild_parent] at hc
  have htOwn : Occupies t (t.cell (fun _ => 0)) :=
    (root_occupies_cell t _).mpr ⟨fun _ => Or.inl rfl, j, rfl⟩
  exact W.disjoint t ht s hs _ htOwn ((gauge_occupies_iff hc _).mp htOwn)

def coarsePose {d : ℕ} (origin : Cell d) (p : Pose d) : Pose d where
  perm := p.perm
  negative := p.negative
  shift := fun i => (p.shift i - origin i) / 2

def fineCell {d : ℕ} (origin : Cell d) (c : Cell d) : Cell d := fun i => 2 * c i + origin i

private theorem coarse_inverse_relation {d : ℕ} (origin : Cell d) (p : Pose d)
    (hEven : ∀ i, (p.shift i - origin i) % 2 = 0) (c : Cell d) (j : Fin d) :
    p.inverseCell (fineCell origin c) j =
      2 * (coarsePose origin p).inverseCell c j +
        if p.negative (p.perm.symm j) then 1 else 0 := by
  have he := hEven (p.perm.symm j)
  simp only [Pose.inverseCell, coarsePose, fineCell, Pose.sign]
  rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm j)) with h | h <;>
    simp [h] <;> omega

/-- Exact correspondence between coarse cells and fine parent macroblocks. -/
theorem coarse_occupies_iff {d : ℕ} (origin : Cell d) (p : Pose d)
    (hEven : ∀ i, (p.shift i - origin i) % 2 = 0) (c : Cell d) :
    Occupies (coarsePose origin p) c ↔ ParentOccupies p (fineCell origin c) := by
  constructor
  · rintro ⟨h, j, hj⟩
    constructor
    · intro i
      have hi := h i
      have he := coarse_inverse_relation origin p hEven c i
      rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm i)) with hp | hp <;>
        simp [hp] at he <;> omega
    · refine ⟨j, ?_⟩
      have he := coarse_inverse_relation origin p hEven c j
      rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm j)) with hp | hp <;>
        simp [hp] at he <;> omega
  · rintro ⟨h, j, hj⟩
    constructor
    · intro i
      have hi := h i
      have he := coarse_inverse_relation origin p hEven c i
      rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm i)) with hp | hp <;>
        simp [hp] at he <;> omega
    · refine ⟨j, ?_⟩
      have hi := h j
      have he := coarse_inverse_relation origin p hEven c j
      rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm j)) with hp | hp <;>
        simp [hp] at he <;> omega

/-- The coarse world is a genuine covering, nonoverlapping registered chair
world, before and independently of the remaining coarse contact-law proof. -/
def RegisteredWorld.coarsen {d : ℕ} (W : RegisteredWorld d)
    (hd : 3 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (p₀ : Pose d) (hp₀ : CompleteParent σ r W.tiles p₀) : RegisteredWorld d where
  tiles := {q | ∃ t ∈ W.tiles, CompleteParent σ r W.tiles (centralParent t) ∧
    coarsePose p₀.shift (centralParent t) = q}
  covers := by
    intro c
    obtain ⟨P, ⟨p, _, hp, hpc⟩, _⟩ := W.parent_cells_tile hd hr he hL hl (fineCell p₀.shift c)
    obtain ⟨t, ht, hg, hct⟩ := hp.actual_center hr he
    have hEven := W.all_parents_even hd hr he hL hl p₀ hp₀ (centralParent t) hct
    refine ⟨coarsePose p₀.shift (centralParent t), ⟨t, ht, hct, rfl⟩, ?_⟩
    exact (coarse_occupies_iff p₀.shift _ hEven c).mpr ((gauge_parentOccupies hg _).mp hpc)
  disjoint := by
    rintro p ⟨t, ht, hct, rfl⟩ q ⟨s, hs, hcs, rfl⟩ c hpc hqc
    have htEven := W.all_parents_even hd hr he hL hl p₀ hp₀ (centralParent t) hct
    have hsEven := W.all_parents_even hd hr he hL hl p₀ hp₀ (centralParent s) hcs
    have htOwn := (coarse_occupies_iff p₀.shift _ htEven c).mp hpc
    have hsOwn := (coarse_occupies_iff p₀.shift _ hsEven c).mp hqc
    have hclass := complete_parent_cells_unique (by omega) hr he W hct hcs htOwn hsOwn
    let j : Fin d := ⟨0, by omega⟩
    have hts := actual_centers_eq W j ht hs hclass
    subst s
    rfl

#print axioms coarse_occupies_iff
#print axioms RegisteredWorld.coarsen
end SparseMonotiles.CarrierHierarchy
