module

public import ProductClosure.ProductWorldAmbient
public import ProductClosure.PolycubePacking

@[expose] public section

/-! Full Euclidean carrier tilings are realized from complete finite-cell
worlds. Thus cell-world existence is not merely a lattice surrogate. -/
namespace ProductClosure.World

open Set
noncomputable section

namespace CompleteTiling
variable {d : ℕ} {S : Finset (Lattice (d + 1))}

/-- A complete actual cell world gives a full Euclidean carrier tiling:
floor cells cover every real point, and disjoint finite cell sets give
disjoint actual carrier interiors. -/
def realize (W : CompleteTiling (placedCells S)) : RegisteredCarrierTiling S where
  tiles := W.tiles
  cover x := by
    obtain ⟨z, hz⟩ := Polycube.exists_latticeCell x
    exact ⟨W.owner z, W.owner_mem z,
      latticeCell_subset_placedCarrier S (W.owner z) (W.mem_owner z) hz⟩
  disjoint q hq r hr hne := by
    rw [placedCarrier_eq_carrier_image, placedCarrier_eq_carrier_image]
    apply Polycube.carrier_interiors_disjoint_of_disjoint
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hqz : z ∈ placedCells S q := by simpa [placedCells] using hz
    have hrz : z ∈ placedCells S r := by simpa [placedCells] using hz'
    exact Set.disjoint_left.mp (W.disjoint q hq r hr hne) hqz hrz

@[simp] theorem realize_tiles (W : CompleteTiling (placedCells S)) : W.realize.tiles = W.tiles := rfl

/-- Realization and lattice decoding retain exactly the same placed tile
states and cell-owner function. -/
theorem realize_toCellWorld_owner (W : CompleteTiling (placedCells S)) (hS : S.Nonempty)
    (z : Lattice (d + 1)) : (W.realize.toCellWorld hS).owner z = W.owner z :=
  (W.realize.toCellWorld hS).owner_eq_of_mem (W.owner_mem z) (W.mem_owner z)

/-- Actual complete Euclidean product carrier tilings exist whenever the two
factor cell worlds do. This includes the generator-world input case. -/
def realizeProduct {m n : ℕ} {S : Finset (Lattice (m + 1))} {T : Finset (Lattice (n + 1))}
    (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)) :
    RegisteredProductTiling S T where
  tiles := WA.tiles ×ˢ WB.tiles
  cover x := by
    obtain ⟨a, ha, hxa⟩ := WA.realize.cover x.1
    obtain ⟨b, hb, hxb⟩ := WB.realize.cover x.2
    exact ⟨(a, b), ⟨ha, hb⟩, hxa, hxb⟩
  disjoint p hp q hq hne := by
    simp only [placedProductCarrier, interior_prod_eq]
    apply Set.disjoint_left.mpr
    intro x hxp hxq
    by_cases ha : p.1 = q.1
    · have hb : p.2 ≠ q.2 := fun hb => hne (Prod.ext ha hb)
      exact Set.disjoint_left.mp (WB.realize.disjoint _ hp.2 _ hq.2 hb) hxp.2 hxq.2
    · exact Set.disjoint_left.mp (WA.realize.disjoint _ hp.1 _ hq.1 ha) hxp.1 hxq.1

@[simp] theorem realizeProduct_tiles {m n : ℕ}
    {S : Finset (Lattice (m + 1))} {T : Finset (Lattice (n + 1))}
    (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)) :
    (WA.realizeProduct WB).tiles = (WA.prod WB).tiles := rfl

#print axioms realize
#print axioms realize_toCellWorld_owner
#print axioms realizeProduct

end CompleteTiling
end
end ProductClosure.World
