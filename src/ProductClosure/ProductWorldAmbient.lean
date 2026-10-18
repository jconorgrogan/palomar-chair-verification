module

public import ProductClosure.ProductWorldSplit
public import ProductClosure.ProductWorldPhysical

@[expose] public section

/-! Actual ambient registered carrier tilings supply complete cell worlds,
without a preselected common block chart or product pose decomposition. -/
namespace ProductClosure.World

open Set
noncomputable section

/-- Actual Euclidean tiling by arbitrary ambient registered poses of a
finite polycube. These poses need not preserve any chosen coordinate block. -/
structure RegisteredCarrierTiling {d : ℕ} (S : Finset (Lattice (d + 1))) where
  tiles : Set (RegisteredPrime.Pose (d + 1))
  cover : ∀ x, ∃ q ∈ tiles, x ∈ placedCarrier S q
  disjoint : ∀ q ∈ tiles, ∀ r ∈ tiles, q ≠ r →
    Disjoint (interior (placedCarrier S q)) (interior (placedCarrier S r))

namespace RegisteredCarrierTiling
variable {d : ℕ} {S : Finset (Lattice (d + 1))}
variable (W : RegisteredCarrierTiling S)

/-- The complete ambient lattice owner world follows from physical coverage
and nonoverlap alone. Empty native carriers are explicitly excluded. -/
def toCellWorld (hS : S.Nonempty) : CompleteTiling (placedCells S) where
  tiles := W.tiles
  cover z := by
    obtain ⟨q, hq, hz⟩ := W.cover (Polycube.latticeCenter z)
    exact ⟨q, hq, (center_mem_placedCarrier_iff S q z).mp hz⟩
  disjoint q hq r hr hne := placedCells_disjoint_of_interiors S q r
    (W.disjoint q hq r hr hne)
  nonempty q _ := placedCells_nonempty hS q

@[simp] theorem toCellWorld_tiles (hS : S.Nonempty) : (W.toCellWorld hS).tiles = W.tiles := rfl

/-- Two actual physical carriers contain neighboring complete unit cells.
This is the local physical contact interface to the mate-language theorem. -/
def CellFacetContact (_W : RegisteredCarrierTiling S) (q r : RegisteredPrime.Pose (d + 1)) : Prop :=
  ∃ z w, LatticeAdjacent z w ∧ Polycube.latticeCell z ⊆ placedCarrier S q ∧
    Polycube.latticeCell w ⊆ placedCarrier S r

theorem owner_cellFacetContact (hS : S.Nonempty) {z w : Lattice (d + 1)}
    (h : LatticeAdjacent z w) :
    W.CellFacetContact ((W.toCellWorld hS).owner z) ((W.toCellWorld hS).owner w) :=
  ⟨z, w, h, latticeCell_subset_placedCarrier S _ ((W.toCellWorld hS).mem_owner z),
    latticeCell_subset_placedCarrier S _ ((W.toCellWorld hS).mem_owner w)⟩

/-- Concrete local physical mate legality supplies the cell-owner law, even
before a common product block chart has been chosen. -/
theorem toCellWorld_legal (hS : S.Nonempty)
    {M : RegisteredPrime.Pose (d + 1) → RegisteredPrime.Pose (d + 1) → Prop}
    (hcontact : ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r → W.CellFacetContact q r → M q r) :
    (W.toCellWorld hS).IsLegal LatticeAdjacent M := by
  intro z w hadj hne
  exact hcontact _ ((W.toCellWorld hS).owner_mem z) _ ((W.toCellWorld hS).owner_mem w)
    hne (W.owner_cellFacetContact hS hadj)

#print axioms toCellWorld
#print axioms toCellWorld_legal

end RegisteredCarrierTiling
end
end ProductClosure.World
