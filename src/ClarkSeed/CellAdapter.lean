module

public import ClarkSeed.PoseAdapter
public import SparseMonotiles.ContactChairChecker
public import ProductClosure.ChairCarrierBridge

@[expose] public section

/-! Exact finite native chair carrier, retaining every occupied integer cell. -/
namespace ClarkSeed.PoseAdapter
noncomputable section
open SparseMonotiles

@[simp] theorem isChairCell_iff {d : ℕ} (z : Contact.Cell d) :
    Contact.IsChairCell z ↔ RegisteredPrime.UnitChairCell z := Iff.rfl

/-- The recovered finite chair is exactly the new native carrier, not merely
an equicardinal or isometric replacement. -/
theorem chairCells_eq (m : ℕ) :
    Contact.chairCells (m+1) = ProductClosure.ChairBridge.cells m := by
  ext z
  rw [Contact.mem_chairCells, ProductClosure.ChairBridge.mem_cells]
  rfl

/-- Old inverse-cell occupancy is exactly image occupancy in the new finite
carrier, including negative rows. -/
theorem inverseCell_mem_iff_placedCells {m : ℕ} (p : Contact.Pose (m+1))
    (z : Contact.Cell (m+1)) :
    Contact.IsChairCell (p.inverseCell z) ↔
      z ∈ ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)
        (toRegistered p) := by
  rw [placedCells_eq, ← chairCells_eq]
  constructor
  · intro h
    exact ⟨p.inverseCell z, (Contact.mem_chairCells _).mpr h, p.cell_inverseCell z⟩
  · rintro ⟨w, hw, rfl⟩
    rw [p.inverseCell_cell]
    exact (Contact.mem_chairCells _).mp hw

/-- The image finite cell set equals the footprint as a set. -/
theorem moved_chairCells_eq {m : ℕ} (p : Contact.Pose (m+1)) :
    (((Contact.chairCells (m+1)).image p.cell : Finset _) : Set _) =
      ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)
        (toRegistered p) := by
  rw [placedCells_eq, ← chairCells_eq]
  simp

#print axioms chairCells_eq
#print axioms inverseCell_mem_iff_placedCells
#print axioms moved_chairCells_eq
end
end ClarkSeed.PoseAdapter
