module

public import ProductClosure.ProductWorldPlaced

@[expose] public section

/-!
# From complete physical registered product carriers to Cartesian worlds

Coverage and disjointness of the full integer-cell owner world are derived
from actual Euclidean carrier coverage and interior disjointness. The sole
contact-language interface concerns distinct physical carriers containing
neighboring full unit cells, so it is a local physical contact condition.
-/
namespace ProductClosure.World

open Set
noncomputable section

variable {m n : ℕ}

abbrev ProductPose (m n : ℕ) := RegisteredPrime.Pose (m + 1) × RegisteredPrime.Pose (n + 1)

def placedProductCarrier (S : Finset (Lattice (m + 1)))
    (T : Finset (Lattice (n + 1))) (q : ProductPose m n) :
    Set (Polycube.Space (m + 1) × Polycube.Space (n + 1)) :=
  placedCarrier S q.1 ×ˢ placedCarrier T q.2

/-- Actual complete tiling by registered product carriers. This structure
has no owner, Cartesian-world, factor-coverage, or section assumptions. -/
structure RegisteredProductTiling (S : Finset (Lattice (m + 1)))
    (T : Finset (Lattice (n + 1))) where
  tiles : Set (ProductPose m n)
  cover : ∀ x, ∃ q ∈ tiles, x ∈ placedProductCarrier S T q
  disjoint : ∀ q ∈ tiles, ∀ r ∈ tiles, q ≠ r →
    Disjoint (interior (placedProductCarrier S T q))
      (interior (placedProductCarrier S T r))

/-- The full closed unit product cell at an integer index. -/
def productLatticeCell (z : Lattice (m + 1) × Lattice (n + 1)) :
    Set (Polycube.Space (m + 1) × Polycube.Space (n + 1)) :=
  Polycube.latticeCell z.1 ×ˢ Polycube.latticeCell z.2

/-- A concrete full-unit-facet contact witness: neighboring unit cells are
contained in the respective actual placed carriers. For distinct tiles of
an interior-disjoint tiling this is a shared boundary unit facet. -/
def CarrierFacetContact (S : Finset (Lattice (m + 1)))
    (T : Finset (Lattice (n + 1))) (q r : ProductPose m n) : Prop :=
  ∃ z w, ProductAdjacent z w ∧ productLatticeCell z ⊆ placedProductCarrier S T q ∧
    productLatticeCell w ⊆ placedProductCarrier S T r

namespace RegisteredProductTiling
variable {S : Finset (Lattice (m + 1))} {T : Finset (Lattice (n + 1))}
variable (W : RegisteredProductTiling S T)

/-- Full lattice-cell coverage follows by evaluating actual carrier coverage
at every lattice center; overlap is ruled out by physical interior
nonoverlap. No chosen owner or cell completeness is postulated. -/
def toCellWorld (hS : S.Nonempty) (hT : T.Nonempty) :
    CompleteTiling (productCells (placedCells S) (placedCells T)) where
  tiles := W.tiles
  cover z := by
    obtain ⟨q, hq, hcenter⟩ := W.cover (Polycube.latticeCenter z.1, Polycube.latticeCenter z.2)
    exact ⟨q, hq, (center_mem_placedCarrier_iff S q.1 z.1).mp hcenter.1,
      (center_mem_placedCarrier_iff T q.2 z.2).mp hcenter.2⟩
  disjoint q hq r hr hne := Set.disjoint_left.mpr (by
    intro z hz hz'
    have hd := W.disjoint q hq r hr hne
    simp only [placedProductCarrier, interior_prod_eq] at hd
    have hqz : (Polycube.latticeCenter z.1, Polycube.latticeCenter z.2) ∈
        interior (placedCarrier S q.1) ×ˢ interior (placedCarrier T q.2) :=
      ⟨center_mem_interior_placedCarrier S q.1 hz.1,
        center_mem_interior_placedCarrier T q.2 hz.2⟩
    have hrz : (Polycube.latticeCenter z.1, Polycube.latticeCenter z.2) ∈
        interior (placedCarrier S r.1) ×ˢ interior (placedCarrier T r.2) :=
      ⟨center_mem_interior_placedCarrier S r.1 hz'.1,
        center_mem_interior_placedCarrier T r.2 hz'.2⟩
    exact Set.disjoint_left.mp hd hqz hrz)
  nonempty q _ := by
    obtain ⟨x, hx⟩ := placedCells_nonempty hS q.1
    obtain ⟨y, hy⟩ := placedCells_nonempty hT q.2
    exact ⟨(x, y), hx, hy⟩

@[simp] theorem toCellWorld_tiles (hS : S.Nonempty) (hT : T.Nonempty) :
    (W.toCellWorld hS hT).tiles = W.tiles := rfl

/-- Neighboring cell owners give actual carrier facet-contact witnesses. -/
theorem owner_carrierFacetContact (hS : S.Nonempty) (hT : T.Nonempty)
    {z w : Lattice (m + 1) × Lattice (n + 1)} (hadj : ProductAdjacent z w) :
    CarrierFacetContact S T ((W.toCellWorld hS hT).owner z)
      ((W.toCellWorld hS hT).owner w) := by
  refine ⟨z, w, hadj, ?_, ?_⟩
  · intro x hx
    exact ⟨latticeCell_subset_placedCarrier S _ ((W.toCellWorld hS hT).mem_owner z).1 hx.1,
      latticeCell_subset_placedCarrier T _ ((W.toCellWorld hS hT).mem_owner z).2 hx.2⟩
  · intro x hx
    exact ⟨latticeCell_subset_placedCarrier S _ ((W.toCellWorld hS hT).mem_owner w).1 hx.1,
      latticeCell_subset_placedCarrier T _ ((W.toCellWorld hS hT).mem_owner w).2 hx.2⟩

/-- A local mate-language theorem on actual carrier contacts gives the
owner-neighbor law needed by global Cartesian decoding. -/
theorem toCellWorld_legal (hS : S.Nonempty) (hT : T.Nonempty)
    {MA : RegisteredPrime.Pose (m + 1) → RegisteredPrime.Pose (m + 1) → Prop}
    {MB : RegisteredPrime.Pose (n + 1) → RegisteredPrime.Pose (n + 1) → Prop}
    (hcontact : ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r →
      CarrierFacetContact S T q r → ProductLanguage MA MB q r) :
    (W.toCellWorld hS hT).IsLegal ProductAdjacent (ProductLanguage MA MB) := by
  intro z w hadj hne
  exact hcontact _ ((W.toCellWorld hS hT).owner_mem z)
    _ ((W.toCellWorld hS hT).owner_mem w) hne (W.owner_carrierFacetContact hS hT hadj)

/-- Physical disjointness of every factor mate supplies exactly the
separation hypotheses; there is no abstract overlap axiom left over. -/
theorem factor_language_separates
    {MA : RegisteredPrime.Pose (m + 1) → RegisteredPrime.Pose (m + 1) → Prop}
    (hA : ∀ q r, MA q r → Disjoint (interior (placedCarrier S q))
      (interior (placedCarrier S r))) : Separates (placedCells S) MA := by
  intro q r hqr
  exact placedCells_disjoint_of_interiors S q r (hA q r hqr)

/-- Actual physical registered product worlds decode exactly, including
complete placed frames and translations, to two complete legal factors. -/
theorem physical_world_cartesian (hS : S.Nonempty) (hT : T.Nonempty)
    {MA : RegisteredPrime.Pose (m + 1) → RegisteredPrime.Pose (m + 1) → Prop}
    {MB : RegisteredPrime.Pose (n + 1) → RegisteredPrime.Pose (n + 1) → Prop}
    (hcontact : ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r →
      CarrierFacetContact S T q r → ProductLanguage MA MB q r)
    (hA : ∀ q r, MA q r → Disjoint (interior (placedCarrier S q))
      (interior (placedCarrier S r)))
    (hB : ∀ q r, MB q r → Disjoint (interior (placedCarrier T q))
      (interior (placedCarrier T r))) :
    ∃ (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)),
      WA.IsLegal LatticeAdjacent MA ∧ WB.IsLegal LatticeAdjacent MB ∧
      W.tiles = WA.tiles ×ˢ WB.tiles ∧
      ∀ z, (W.toCellWorld hS hT).owner z = (WA.owner z.1, WB.owner z.2) := by
  let C := W.toCellWorld hS hT
  have hlegal := W.toCellWorld_legal hS hT hcontact
  have hsA : Separates (placedCells S) MA := fun q r h =>
    placedCells_disjoint_of_interiors S q r (hA q r h)
  have hsB : Separates (placedCells T) MB := fun q r h =>
    placedCells_disjoint_of_interiors T q r (hB q r h)
  refine ⟨C.activeFactor hlegal hsA hsB, C.passiveFactor hlegal hsA hsB,
    C.activeFactor_legal hlegal hsA hsB, C.passiveFactor_legal hlegal hsA hsB,
    C.tiles_cartesian hlegal hsA hsB, ?_⟩
  intro z
  simp only [CompleteTiling.activeFactor_owner, CompleteTiling.passiveFactor_owner]
  exact C.owner_factorizes hlegal hsA hsB z.1 z.2

#print axioms toCellWorld
#print axioms toCellWorld_legal
#print axioms physical_world_cartesian

end RegisteredProductTiling
end
end ProductClosure.World
