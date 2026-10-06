module

public import SparseMonotiles.CarrierHierarchyCells
public import SparseMonotiles.CarrierFacetHalfspace
public import SparseMonotiles.KeyCovariance

@[expose] public section

/-!
Realization of the discrete exact dissection as equality of actual Euclidean
closed carrier sets. This file does not mention `body`: the replaced pyramids
are not assumed to form a rep-tile. Coordinate-permutation choices only affect
child frames, not the undecorated carrier union.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact Set

/-- Exact transport of closed unit cells under the actual affine isometry. -/
theorem euclidean_mem_closedIntegerCell {d : ℕ} (p : Pose d)
    (c : Cell d) (x : Point d) :
    p.euclidean x ∈ closedIntegerCell (p.cell c) ↔ x ∈ closedIntegerCell c := by
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ := p.perm.surjective j
    have hi := h i
    rw [Pose.euclidean_apply] at hi
    cases hn : p.negative i <;>
      simp [Pose.cell, Pose.sign, hn] at hi <;>
      constructor <;> linarith
  · intro h i
    have hi := h (p.perm i)
    rw [Pose.euclidean_apply]
    cases hn : p.negative i <;>
      simp [Pose.cell, Pose.sign, hn] <;>
      constructor <;> linarith

/-- The registered cell predicate agrees with the image of the literal carrier. -/
theorem mem_posed_carrier_iff {d : ℕ} (p : Pose d) (x : Point d) :
    x ∈ p.euclidean '' carrier d ↔
      ∃ c, Occupies p c ∧ x ∈ closedIntegerCell c := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hyc⟩ := (mem_carrier_iff_exists_chairCell y).mp hy
    refine ⟨p.cell c, ?_, (euclidean_mem_closedIntegerCell p c y).mpr hyc⟩
    simpa [Occupies, p.inverseCell_cell] using hc
  · rintro ⟨c, hc, hxc⟩
    obtain ⟨y, rfl⟩ := p.euclidean.surjective x
    refine ⟨y, ?_, rfl⟩
    apply (mem_carrier_iff_exists_chairCell y).mpr
    refine ⟨p.inverseCell c, hc, ?_⟩
    apply (euclidean_mem_closedIntegerCell p (p.inverseCell c) y).mp
    simpa [p.cell_inverseCell] using hxc

private theorem carrier_bounds {d : ℕ} (x : Point d) :
    x ∈ carrier d ↔ (∀ i, 0 ≤ x i ∧ x i ≤ 2) ∧ ∃ i, x i ≤ 1 := by
  constructor
  · rintro ⟨b, ⟨i, hi⟩, h⟩
    constructor
    · intro j
      have hj := h j
      cases hb : b j <;> simp [hb] at hj <;> constructor <;> linarith
    · refine ⟨i, ?_⟩
      simpa [hi] using (h i).2
  · rintro ⟨h, i, hi⟩
    let b : Fin d → Bool := fun j => decide (1 < x j)
    refine ⟨b, ⟨i, by simp [b]; linarith⟩, ?_⟩
    intro j
    have hj := h j
    by_cases hb : 1 < x j <;> simp [b, hb] <;> constructor <;> linarith

/-- Literal scalar double of the unmarked chair carrier only. -/
def doubledCarrier (d : ℕ) : Set (Point d) :=
  (fun x : Point d => (2 : ℝ) • x) '' carrier d

private theorem doubledCarrier_bounds {d : ℕ} (x : Point d) :
    x ∈ doubledCarrier d ↔ (∀ i, 0 ≤ x i ∧ x i ≤ 4) ∧ ∃ i, x i ≤ 2 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hb, i, hi⟩ := (carrier_bounds y).mp hy
    constructor
    · intro j
      have hj := hb j
      change 0 ≤ 2 * y j ∧ 2 * y j ≤ 4
      constructor <;> linarith
    · exact ⟨i, by change 2 * y i ≤ 2; linarith⟩
  · rintro ⟨h, i, hi⟩
    refine ⟨(1 / 2 : ℝ) • x, (carrier_bounds _).mpr ?_, ?_⟩
    · constructor
      · intro j
        have hj := h j
        change 0 ≤ (1 / 2 : ℝ) * x j ∧ (1 / 2 : ℝ) * x j ≤ 2
        constructor <;> linarith
      · exact ⟨i, by change (1 / 2 : ℝ) * x i ≤ 1; linarith⟩
    · ext j
      change 2 * ((1 / 2 : ℝ) * x j) = x j
      ring

/-- The entire doubled closed carrier is covered, including cell boundaries. -/
theorem mem_doubledCarrier_iff {d : ℕ} (x : Point d) :
    x ∈ doubledCarrier d ↔ ∃ c, DoubleCell c ∧ x ∈ closedIntegerCell c := by
  rw [doubledCarrier_bounds]
  constructor
  · rintro ⟨h, i, hi⟩
    let c : Cell d := fun j => if x j ≤ 1 then 0 else if x j ≤ 2 then 1
      else if x j ≤ 3 then 2 else 3
    refine ⟨c, ⟨?_, ?_⟩, ?_⟩
    · intro j
      simp only [c]
      split_ifs <;> omega
    · refine ⟨i, ?_⟩
      simp only [c]
      split_ifs <;> omega
    · intro j
      have hj := h j
      by_cases h1 : x j ≤ 1
      · simpa [c, h1] using hj.1
      · by_cases h2 : x j ≤ 2
        · simp [c, h1, h2] <;> constructor <;> linarith
        · by_cases h3 : x j ≤ 3
          · simp [c, h1, h2, h3] <;> constructor <;> linarith
          · simp [c, h1, h2, h3] <;> constructor <;> linarith
  · rintro ⟨c, ⟨hb, i, hi⟩, hx⟩
    constructor
    · intro j
      have h0 : (0 : ℝ) ≤ c j := by exact_mod_cast (hb j).1
      have h3 : (c j : ℝ) ≤ 3 := by exact_mod_cast (hb j).2
      have hj := hx j
      constructor <;> linarith
    · refine ⟨i, ?_⟩
      have hc : (c i : ℝ) ≤ 1 := by exact_mod_cast hi
      have hj := hx i
      linarith

/-- A genuine Euclidean exact substitution equality for undecorated carriers.
This is independent of key geometry and asserts nothing about scaled bodies. -/
theorem canonical_carrier_dissection {d : ℕ}
    (σ : Bits d → Equiv.Perm (Fin d)) (x : Point d) :
    x ∈ doubledCarrier d ↔
      x ∈ (centralPose d).euclidean '' carrier d ∨
      ∃ a, Proper a ∧ x ∈ (outerPose a (σ a)).euclidean '' carrier d := by
  rw [mem_doubledCarrier_iff]
  constructor
  · rintro ⟨c, hc, hx⟩
    rcases (canonical_dissection σ c).mp hc with h | ⟨a, ha, h⟩
    · exact Or.inl ((mem_posed_carrier_iff _ _).mpr ⟨c, h, hx⟩)
    · exact Or.inr ⟨a, ha, (mem_posed_carrier_iff _ _).mpr ⟨c, h, hx⟩⟩
  · rintro (h | ⟨a, ha, h⟩)
    · obtain ⟨c, hc, hx⟩ := (mem_posed_carrier_iff _ _).mp h
      exact ⟨c, (canonical_dissection σ c).mpr (Or.inl hc), hx⟩
    · obtain ⟨c, hc, hx⟩ := (mem_posed_carrier_iff _ _).mp h
      exact ⟨c, (canonical_dissection σ c).mpr (Or.inr ⟨a, ha, hc⟩), hx⟩

#print axioms mem_posed_carrier_iff
#print axioms canonical_carrier_dissection
end SparseMonotiles.CarrierHierarchy
