module

public import PhysicalRegistration.RetainedCore

@[expose] public section

/-! Native occupied cells and their exact exposed-facet neighbors in the
integer lattice. These are literal coordinate sets and indices. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

abbrev LatticeIndex (m : ℕ) := Fin (m + 1) → ℤ

def cellIndex {m : ℕ} (c : Cell m) : LatticeIndex m :=
  fun i => if c.val i then 1 else 0

def latticeCell {m : ℕ} (z : LatticeIndex m) : Set (Space m) :=
  {x | ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ (z i : ℝ) + 1}

def latticeCenter {m : ℕ} (z : LatticeIndex m) : Space m :=
  WithLp.toLp 2 (fun i => (z i : ℝ) + 1 / 2)

def latticeStep {m : ℕ} (z : LatticeIndex m) (i : Fin (m + 1)) (positive : Bool) :
    LatticeIndex m := fun k => z k + if k = i then (if positive then 1 else -1) else 0

@[simp] theorem cast_cellIndex {m : ℕ} (c : Cell m) (i : Fin (m + 1)) :
    (cellIndex c i : ℝ) = bit (c.val i) := by
  cases hc : c.val i <;> norm_num [cellIndex, bit, hc]

@[simp] theorem latticeCell_cellIndex {m : ℕ} (c : Cell m) :
    latticeCell (cellIndex c) = unitCell c := by
  ext x
  simp only [latticeCell, unitCell, mem_ofPred_eq, cast_cellIndex]

@[simp] theorem latticeCenter_cellIndex {m : ℕ} (c : Cell m) :
    latticeCenter (cellIndex c) = cellCenter c := by
  ext i
  simp [latticeCenter, cellCenter]

/-- The occupied unit cell on the inward side of every exposed facet. -/
def facetInsideCell {m : ℕ} : Facet m → Cell m
  | .inl (c, _) => c
  | .inr i => ⟨fun k => decide (k ≠ i), by
      intro h
      have hi := congrFun h i
      simp at hi⟩

def facetPositive {m : ℕ} : Facet m → Bool
  | .inl (c, i) => c.val i
  | .inr _ => true

def facetOutsideIndex {m : ℕ} (F : Facet m) : LatticeIndex m :=
  latticeStep (cellIndex (facetInsideCell F)) (normalIndex F) (facetPositive F)

/-- Each native facet center is exactly half a normal step outward from
its inward occupied cell center. -/
theorem facetInsideCell_center {m : ℕ} (F : Facet m) :
    cellCenter (facetInsideCell F) = facetCenter F - (1 / 2 : ℝ) • outward F := by
  ext k
  cases F with
  | inl ci =>
    rcases ci with ⟨c, i⟩
    by_cases hki : k = i
    · subst k
      cases hc : c.val i <;> norm_num [facetInsideCell, cellCenter, facetCenter, outward,
        normalIndex, normalSign, sign, bit, hc]
    · simp [facetInsideCell, cellCenter, facetCenter, outward, normalIndex,
        hki]
  | inr i =>
    by_cases hki : k = i
    · subst k
      norm_num [facetInsideCell, cellCenter, facetCenter, outward, normalIndex, normalSign, bit]
    · norm_num [facetInsideCell, cellCenter, facetCenter, outward, normalIndex, normalSign, bit, hki]

/-- The cell just outside a facet has center exactly half a normal step
outward from that facet center. -/
theorem facetOutsideIndex_center {m : ℕ} (F : Facet m) :
    latticeCenter (facetOutsideIndex F) = facetCenter F + (1 / 2 : ℝ) • outward F := by
  have hstep : latticeCenter (facetOutsideIndex F) =
      cellCenter (facetInsideCell F) + outward F := by
    ext k
    cases F with
    | inl ci =>
      rcases ci with ⟨c, i⟩
      by_cases hki : k = i
      · subst k
        cases hc : c.val i <;> norm_num [latticeCenter, facetOutsideIndex, facetInsideCell,
          latticeStep, cellIndex, facetPositive, cellCenter, bit, outward, normalIndex, normalSign, sign, hc]
      · cases hck : c.val k <;> norm_num [latticeCenter, facetOutsideIndex, facetInsideCell, latticeStep, cellIndex,
          facetPositive, cellCenter, bit, outward, normalIndex, hki, hck]
    | inr i =>
      by_cases hki : k = i
      · subst k
        norm_num [latticeCenter, facetOutsideIndex, facetInsideCell, latticeStep, cellIndex,
          facetPositive, cellCenter, bit, outward, normalIndex, normalSign]
      · simp [latticeCenter, facetOutsideIndex, facetInsideCell, latticeStep, cellIndex,
          facetPositive, cellCenter, bit, outward, normalIndex, normalSign, hki]
  rw [hstep, facetInsideCell_center]
  module

/-- Every unit lattice neighbor of an occupied native cell is either another
occupied native cell or the exact outside cell across one native exposed facet. -/
theorem occupied_cell_neighbor {m : ℕ} (c : Cell m) (i : Fin (m + 1)) (b : Bool) :
    (∃ d : Cell m, latticeStep (cellIndex c) i b = cellIndex d) ∨
      ∃ F : Facet m, facetInsideCell F = c ∧
        latticeStep (cellIndex c) i b = facetOutsideIndex F := by
  classical
  cases hb : b <;> cases hc : c.val i
  · right
    exact ⟨.inl (c, i), rfl, by simp [facetOutsideIndex, facetInsideCell, normalIndex, facetPositive, hc]⟩
  · left
    let d : Cell m := ⟨Function.update c.val i false, by
      intro h
      have hi := congrFun h i
      simp at hi⟩
    refine ⟨d, ?_⟩
    funext k
    by_cases hki : k = i
    · subst k
      simp [latticeStep, cellIndex, d, hc]
    · simp [latticeStep, cellIndex, d, hki]
  · by_cases hall : Function.update c.val i true = fun _ => true
    · right
      refine ⟨.inr i, ?_, ?_⟩
      · apply Subtype.ext
        funext k
        by_cases hki : k = i
        · subst k; simp [facetInsideCell, hc]
        · have hk := congrFun hall k
          simpa [facetInsideCell, hki] using hk.symm
      · funext k
        by_cases hki : k = i
        · subst k
          simp [latticeStep, cellIndex, facetOutsideIndex, facetInsideCell,
            normalIndex, facetPositive, hc]
        · have hk := congrFun hall k
          have hck : c.val k = true := by simpa [hki] using hk
          simp [latticeStep, cellIndex, facetOutsideIndex, facetInsideCell,
            normalIndex, facetPositive, hki, hck]
    · left
      let d : Cell m := ⟨Function.update c.val i true, hall⟩
      refine ⟨d, ?_⟩
      funext k
      by_cases hki : k = i
      · subst k; simp [latticeStep, cellIndex, d, hc]
      · simp [latticeStep, cellIndex, d, hki]
  · right
    exact ⟨.inl (c, i), rfl, by simp [facetOutsideIndex, facetInsideCell, normalIndex, facetPositive, hc]⟩

#print axioms facetInsideCell_center
#print axioms facetOutsideIndex_center
#print axioms occupied_cell_neighbor
end
end PhysicalRegistration.NativeChair
