module

public import SparseMonotiles.CarrierHierarchyParentCells

@[expose] public section

/-!
Complete contacting parents have even relative anchor displacement. The proof
uses actual cross-child contacts in the fine world, the supplied contact law's
constant parity, and the proved all-odd geometric obstruction. Alignment is a
conclusion, never an input to candidate generation or coarsening.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem normalized_shift_at {d : ℕ} (p q : Pose d) (i : Fin d) :
    (normalize p q).shift (p.perm i) = p.sign i * (q.shift i - p.shift i) := by
  rcases Bool.eq_false_or_eq_true (p.negative i) with h | h <;>
    simp [normalize, compose, inversePose, Pose.sign, h] <;> ring

private theorem normal_parity_to_global {d : ℕ} (p q : Pose d) (b : Bool)
    (h : ∀ i, (normalize p q).shift i % 2 = if b then 1 else 0) :
    ∀ i, (q.shift i - p.shift i) % 2 = if b then 1 else 0 := by
  intro i
  have hi := h (p.perm i)
  rw [normalized_shift_at] at hi
  rcases Bool.eq_false_or_eq_true (p.negative i) with hn | hn <;>
    simp [Pose.sign, hn] at hi <;> omega

/-- Canonical central and outer child offsets have uniform parity. -/
theorem child_anchor_parity {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (p : Pose d) {q : Pose d} (hq : q ∈ children σ p) :
    ∃ b : Bool, ∀ i, (q.shift i - p.shift i) % 2 = if b then 1 else 0 := by
  rcases hq with rfl | ⟨a, ha, rfl⟩
  · refine ⟨true, ?_⟩
    intro i
    rcases Bool.eq_false_or_eq_true (p.negative i) with h | h <;>
      simp [centralChild, Pose.sign, h] <;> omega
  · refine ⟨false, ?_⟩
    intro i
    rcases Bool.eq_false_or_eq_true (p.negative i) with hp | hp <;>
      rcases Bool.eq_false_or_eq_true (a (p.perm i)) with ha | ha <;>
      simp [compose, outerPose, bit, Pose.sign, hp, ha] <;> omega

private theorem physical_child_anchor_parity {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    {p q : Pose d} (h : ParentContains σ r p q) :
    ∃ b : Bool, ∀ i, (q.shift i - p.shift i) % 2 = if b then 1 else 0 := by
  obtain ⟨s, hs, hg⟩ := h
  obtain ⟨b, hb⟩ := child_anchor_parity σ p hs
  exact ⟨b, by simpa only [gauge_shift_eq hg] using hb⟩

/-- Exact parent alignment from one actual cross-parent unit-face contact. -/
theorem RegisteredWorld.parent_contact_even {d : ℕ} (W : RegisteredWorld d)
    (hd : 2 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    {p q : Pose d} (hp : CompleteParent σ r W.tiles p) (hq : CompleteParent σ r W.tiles q)
    (hne : physicalClass r hr p ≠ physicalClass r hr q)
    {c b : Cell d} (hpc : ParentOccupies p c) (hqb : ParentOccupies q b)
    (hadj : AdjacentCells c b) : ∀ i, (q.shift i - p.shift i) % 2 = 0 := by
  obtain ⟨s, hs, hps, hsc⟩ := hp.owns_cell hpc
  obtain ⟨t, ht, hqt, htb⟩ := hq.owns_cell hqb
  have hst : s ≠ t := by
    intro h
    subst t
    exact hne (complete_parent_unique hd hr he W.tiles W.disjoint hp hq hps hqt)
  have hcontact : CellContact s t := ⟨c, b, hsc, htb, hadj⟩
  obtain ⟨f, hf⟩ := (hL _ (hl s hs t ht hst hcontact)).1
  have hglobal := normal_parity_to_global s t f hf
  obtain ⟨u, hu⟩ := physical_child_anchor_parity hps
  obtain ⟨v, hv⟩ := physical_child_anchor_parity hqt
  obtain ⟨j, hj⟩ := hadj
  have hAdj : AdjacentCells c b := ⟨j, hj⟩
  have hconstant : ∀ i, (q.shift i - p.shift i) % 2 = (q.shift j - p.shift j) % 2 := by
    intro i
    have hfi := hglobal i
    have hfj := hglobal j
    have hui := hu i
    have huj := hu j
    have hvi := hv i
    have hvj := hv j
    omega
  by_cases heven : (q.shift j - p.shift j) % 2 = 0
  · intro i
    exact (hconstant i).trans heven
  · have hodd : ∀ i, (q.shift i - p.shift i) % 2 = 1 := by
      intro i
      have hi := hconstant i
      omega
    obtain ⟨x, hpx, hqx⟩ := odd_parent_contact_overlap hpc hqb hAdj hodd
    exact False.elim (hne (complete_parent_cells_unique hd hr he W hp hq hpx hqx))

#print axioms child_anchor_parity
#print axioms RegisteredWorld.parent_contact_even
end SparseMonotiles.CarrierHierarchy
