module

public import ProductClosure.NativeGraphCoefficients
public import ProductClosure.ProductPolycube
public import PhysicalRegistration.RegisteredTubeOwners

@[expose] public section

/-! Exact embedding of the already verified chair carrier and exposed facets
into the generalized finite-polycube compiler. No hierarchy assumption. -/
namespace ProductClosure.ChairBridge
open Set
noncomputable section

/-- The actual finite set of proper binary occupied cells. -/
def cells (m : ℕ) : Finset (Polycube.LatticeIndex (m+1)) :=
  Finset.univ.image PhysicalRegistration.NativeChair.cellIndex

@[simp] theorem mem_cells {m : ℕ} (z : Polycube.LatticeIndex (m+1)) :
    z ∈ cells m ↔ RegisteredPrime.UnitChairCell z := by
  simp only [cells, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; exact PhysicalRegistration.NativeChair.cellIndex_unitChairCell c
  · exact PhysicalRegistration.NativeChair.unitChairCell_exists_native z

theorem cells_nonempty (m : ℕ) : (cells m).Nonempty :=
  ⟨PhysicalRegistration.NativeChair.cellIndex (PhysicalRegistration.NativeChair.zeroCell m), mem_cells _ |>.mpr (PhysicalRegistration.NativeChair.cellIndex_unitChairCell _)⟩

instance (m : ℕ) : Nonempty (Polycube.Cell (cells m)) := by
  obtain ⟨z,hz⟩ := cells_nonempty m
  exact ⟨⟨z,hz⟩⟩

def cellMap {m : ℕ} (c : PhysicalRegistration.NativeChair.Cell m) : Polycube.Cell (cells m) :=
  ⟨PhysicalRegistration.NativeChair.cellIndex c, (mem_cells _).mpr (PhysicalRegistration.NativeChair.cellIndex_unitChairCell c)⟩

theorem cellIndex_injective (m : ℕ) : Function.Injective (@PhysicalRegistration.NativeChair.cellIndex m) := by
  intro a b h
  apply Subtype.ext
  funext i
  have hi := congrFun h i
  cases ha : a.val i <;> cases hb : b.val i <;>
    simp_all [PhysicalRegistration.NativeChair.cellIndex]

theorem cellMap_bijective (m : ℕ) : Function.Bijective (@cellMap m) := by
  constructor
  · intro a b h
    exact cellIndex_injective m (congrArg Subtype.val h)
  · intro c
    obtain ⟨b,hb⟩ := PhysicalRegistration.NativeChair.unitChairCell_exists_native c.val ((mem_cells _).mp c.property)
    exact ⟨b, Subtype.ext hb⟩

def cellEquiv (m : ℕ) : PhysicalRegistration.NativeChair.Cell m ≃ Polycube.Cell (cells m) :=
  Equiv.ofBijective cellMap (cellMap_bijective m)

theorem carrier_eq (m : ℕ) : Polycube.carrier (cells m) = PhysicalRegistration.NativeChair.carrier m := by
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, hx⟩
    obtain ⟨b,hb⟩ := (cellMap_bijective m).2 c
    subst c
    exact mem_iUnion.mpr ⟨b, (PhysicalRegistration.NativeChair.latticeCell_cellIndex b) ▸ hx⟩
  · intro hx
    obtain ⟨c,hc⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨cellMap c, by
      change x ∈ PhysicalRegistration.NativeChair.latticeCell (PhysicalRegistration.NativeChair.cellIndex c)
      rw [PhysicalRegistration.NativeChair.latticeCell_cellIndex]
      exact hc⟩

/-- All old exposed facets have the exact occupied and missing new cells. -/
def facetMap {m : ℕ} (f : PhysicalRegistration.NativeChair.Facet m) : Polycube.Facet (cells m) where
  cell := cellMap (PhysicalRegistration.NativeChair.facetInsideCell f)
  axis := PhysicalRegistration.NativeChair.normalIndex f
  positive := PhysicalRegistration.NativeChair.facetPositive f
  outside := by
    change PhysicalRegistration.NativeChair.facetOutsideIndex f ∉ cells m
    exact fun h => PhysicalRegistration.NativeChair.facetOutsideIndex_not_unitChairCell f ((mem_cells _).mp h)

@[simp] theorem facetMap_inside {m : ℕ} (f : PhysicalRegistration.NativeChair.Facet m) :
    (facetMap f).cell = cellMap (PhysicalRegistration.NativeChair.facetInsideCell f) := rfl
@[simp] theorem facetMap_axis {m : ℕ} (f : PhysicalRegistration.NativeChair.Facet m) :
    (facetMap f).axis = PhysicalRegistration.NativeChair.normalIndex f := rfl
@[simp] theorem facetMap_positive {m : ℕ} (f : PhysicalRegistration.NativeChair.Facet m) :
    (facetMap f).positive = PhysicalRegistration.NativeChair.facetPositive f := rfl

@[simp] theorem facetMap_outward {m : ℕ} (f : PhysicalRegistration.NativeChair.Facet m) :
    Polycube.outward (facetMap f) = PhysicalRegistration.NativeChair.outward f := by
  cases f with
  | inl ci => rfl
  | inr i => simp [Polycube.outward, Polycube.sign, facetMap, PhysicalRegistration.NativeChair.outward,
      PhysicalRegistration.NativeChair.normalSign, PhysicalRegistration.NativeChair.normalIndex, PhysicalRegistration.NativeChair.facetPositive]

@[simp] theorem facetMap_center {m : ℕ} (f : PhysicalRegistration.NativeChair.Facet m) :
    Polycube.facetCenter (facetMap f) = PhysicalRegistration.NativeChair.facetCenter f := by
  rw [Polycube.facetCenter, facetMap_outward]
  change PhysicalRegistration.NativeChair.latticeCenter (PhysicalRegistration.NativeChair.cellIndex (PhysicalRegistration.NativeChair.facetInsideCell f)) + _ = _
  rw [PhysicalRegistration.NativeChair.latticeCenter_cellIndex, PhysicalRegistration.NativeChair.facetInsideCell_center]
  module

end
end ProductClosure.ChairBridge
