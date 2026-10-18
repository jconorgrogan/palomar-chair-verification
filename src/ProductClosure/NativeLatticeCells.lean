module

public import ProductClosure.RetainedCore

@[expose] public section

/-! Native lattice-cell API for arbitrary finite occupied polycubes. -/
namespace ProductClosure.NativeCompiler
open Set
noncomputable section

abbrev LatticeIndex (m : ℕ) := Polycube.LatticeIndex (m + 1)

variable {m : ℕ} {S : Finset (LatticeIndex m)}

def cellIndex (c : Polycube.Cell S) : LatticeIndex m := c.val
abbrev latticeCell (z : LatticeIndex m) : Set (Space m) := Polycube.latticeCell z
abbrev latticeCenter (z : LatticeIndex m) : Space m := Polycube.latticeCenter z
abbrev latticeStep (z : LatticeIndex m) (i : Fin (m + 1)) (b : Bool) : LatticeIndex m :=
  Polycube.latticeStep z i b
abbrev unitCell (c : Polycube.Cell S) : Set (Space m) := Polycube.latticeCell c.val

def facetInsideCell (f : Facet S) : Polycube.Cell S := f.cell
def facetPositive (f : Facet S) : Bool := f.positive
def facetOutsideIndex (f : Facet S) : LatticeIndex m := Polycube.facetOutsideIndex f

@[simp] theorem latticeCell_cellIndex (c : Polycube.Cell S) :
    latticeCell (cellIndex c) = unitCell c := rfl
@[simp] theorem latticeCenter_cellIndex (c : Polycube.Cell S) :
    latticeCenter (cellIndex c) = cellCenter c := rfl

theorem facetInsideCell_center (f : Facet S) :
    cellCenter (facetInsideCell f) = facetCenter f - (1 / 2 : ℝ) • outward f :=
  Polycube.facetInsideCell_center f

theorem facetOutsideIndex_center (f : Facet S) :
    latticeCenter (facetOutsideIndex f) = facetCenter f + (1 / 2 : ℝ) • outward f :=
  Polycube.facetOutsideIndex_center f

theorem occupied_cell_neighbor (c : Polycube.Cell S) (i : Fin (m + 1)) (b : Bool) :
    (∃ c' : Polycube.Cell S, latticeStep (cellIndex c) i b = cellIndex c') ∨
      ∃ f : Facet S, facetInsideCell f = c ∧
        latticeStep (cellIndex c) i b = facetOutsideIndex f := by
  rcases Polycube.occupied_cell_neighbor c i b with hi | ⟨f, hf, _, _, he⟩
  · exact Or.inl hi
  · exact Or.inr ⟨f, hf, he⟩

theorem latticeCenter_injective : Function.Injective (latticeCenter (m := m)) := by
  intro z w h
  funext i
  have hi := congrArg (fun x : Space m => x i) h
  change (z i : ℝ) + 1 / 2 = (w i : ℝ) + 1 / 2 at hi
  have he : (z i : ℝ) = (w i : ℝ) := by linarith
  exact_mod_cast he

theorem exists_latticeCell (x : Space m) : ∃ z : LatticeIndex m, x ∈ latticeCell z := by
  refine ⟨fun i => ⌊x i⌋, fun i => ?_⟩
  exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩

end
end ProductClosure.NativeCompiler
