module

public import SpectreGeometry.PhysicalGridRootContact
public import SpectreClusters.StageDHierarchyNesting

@[expose] public section


/-! Pull the conditional native hierarchy back to the actual original physical
 tile indices. All finite capture and parent-occurrence premises remain explicit.
 No translation-equivariance hypothesis is imposed on the chosen hierarchy. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreFinite SpectreFinite.HexSearch

section Transport
variable {ι : Type*}
  (C : NativeHierarchy.ParentOccurrenceTheorem)
  (hA : StageA.FinalCaptures) (hD : StageD.FinalClusterCaptures)
  (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)
  (hs : StageA.SparseTurtles (physicalGridField f hdirect hdisjoint hcover root))
  (base : Cell)

/-- The original tile indices belonging to one actual extracted hierarchy block. -/
def physicalHierarchyIndices (n : Nat) (x : Position) : Set ι :=
  {i | tilingGridPlacement f hdirect hdisjoint hcover root i ∈
    StageD.actualHierarchyTiles C hA hD (physicalGridField f hdirect hdisjoint hcover root)
      (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n x}

/-- Finiteness is pulled back through the proved injective physical tile map. -/
theorem physicalHierarchyIndices_finite (n : Nat) (x : Position) :
    (physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x).Finite := by
  let L := StageD.actualHierarchyTiles C hA hD
    (physicalGridField f hdirect hdisjoint hcover root)
    (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n x
  change ((tilingGridPlacement f hdirect hdisjoint hcover root) ⁻¹' {p | p ∈ L}).Finite
  exact L.finite_toSet.preimage
    (tilingGridPlacement_injective f hdirect hdisjoint hcover root).injOn

/-- Every listed discrete tile is exactly one of the original physical tiles;
 the pullback neither loses a listed placement nor introduces a foreign one. -/
theorem physicalHierarchyIndices_image (n : Nat) (x : Position) :
    tilingGridPlacement f hdirect hdisjoint hcover root ''
      physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x =
    {p | p ∈ StageD.actualHierarchyTiles C hA hD
      (physicalGridField f hdirect hdisjoint hcover root)
      (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n x} := by
  ext p
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact hi
  · intro hp
    have ho := StageD.actualHierarchyTiles_owned C hA hD
      (physicalGridField f hdirect hdisjoint hcover root)
      (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n x p hp
    obtain ⟨i,hi⟩ := physicalGridField_owned_source f hdirect hdisjoint hcover root p ho
    refine ⟨i,?_,hi⟩
    change tilingGridPlacement f hdirect hdisjoint hcover root i ∈
      StageD.actualHierarchyTiles C hA hD
        (physicalGridField f hdirect hdisjoint hcover root)
        (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n x
    rw [hi]
    exact hp

/-- Every original physical tile is in exactly one block at every level. -/
theorem physicalHierarchyIndices_unique (hh : StageD.HaloOrderBinding)
    (n : Nat) (i : ι) :
    ∃! x, i ∈ physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x := by
  obtain ⟨x,hx⟩ := StageD.actualHierarchyTiles_cover C hA hD hh
    (physicalGridField f hdirect hdisjoint hcover root)
    (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n
    (tilingGridPlacement f hdirect hdisjoint hcover root i)
    (physicalGridField_owns f hdirect hdisjoint hcover root i)
  refine ⟨x,hx,?_⟩
  intro y hy
  exact StageD.actualHierarchyTiles_disjoint C hA hD
    (physicalGridField f hdirect hdisjoint hcover root)
    (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n y x
    (tilingGridPlacement f hdirect hdisjoint hcover root i) hy hx

/-- Distinct blocks at the same level contain disjoint sets of original indices. -/
theorem physicalHierarchyIndices_disjoint (n : Nat) :
    Pairwise (fun x y => Disjoint
      (physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x)
      (physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n y)) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro i hx hy
  exact hxy (StageD.actualHierarchyTiles_disjoint C hA hD
    (physicalGridField f hdirect hdisjoint hcover root)
    (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n x y
    (tilingGridPlacement f hdirect hdisjoint hcover root i) hx hy)

/-- Nesting of the actual discrete blocks is inherited by the same physical indices. -/
theorem physicalHierarchyIndices_nested (n : Nat) (x : Position) :
    ∃ y, physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x ⊆
      physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base (n+1) y := by
  obtain ⟨y,hy⟩ := StageD.actualHierarchyTiles_nested C hA hD
    (physicalGridField f hdirect hdisjoint hcover root)
    (physicalGridField_valid f hdirect hdisjoint hcover root) hs base n x
  exact ⟨y,fun _ hi => hy _ hi⟩

end Transport

/-- With the displayed finite hierarchy/capture inputs, every homochiral physical
 tiling has finite, covering, disjoint and nested blocks of its original indices.
 The source root and sparse phase are derived from the supplied physical tiling. -/
theorem homochiral_physical_hierarchy_of_certificates {ι : Type*}
    (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : StageA.FinalCaptures) (hD : StageD.FinalClusterCaptures)
    (hh : StageD.HaloOrderBinding)
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (base : Cell) :
    ∃ (root : ι) (hs : StageA.SparseTurtles (physicalGridField f hdirect hdisjoint hcover root)),
      (∀ n x, (physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x).Finite) ∧
      (∀ n i, ∃! x, i ∈ physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x) ∧
      (∀ n x, ∃ y,
        physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base n x ⊆
        physicalHierarchyIndices C hA hD f hdirect hdisjoint hcover root hs base (n+1) y) := by
  obtain ⟨r,_⟩ := hcover 0
  obtain ⟨root,hs⟩ := exists_root_sparseTurtles f hdirect hdisjoint hcover r hA
  exact ⟨root,hs,
    physicalHierarchyIndices_finite C hA hD f hdirect hdisjoint hcover root hs base,
    physicalHierarchyIndices_unique C hA hD f hdirect hdisjoint hcover root hs base hh,
    physicalHierarchyIndices_nested C hA hD f hdirect hdisjoint hcover root hs base⟩

/-- Conditional physical aperiodicity follows from the proved physical-to-grid
 period map and the existing conditional discrete obstruction. No covariance of
 a chosen hierarchy is an additional premise. -/
theorem homochiral_physical_period_eq_zero_of_certificates {ι : Type*}
    (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : StageA.FinalCaptures) (hD : StageD.FinalClusterCaptures)
    (hh : StageD.HaloOrderBinding)
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (v : EPlane) (hperiod : Deformation.CarrierCollectionPeriod f v) : v = 0 := by
  by_contra hv
  obtain ⟨root,_⟩ := hcover 0
  obtain ⟨g,hg,hs,u,hu,hup⟩ := physical_period_has_sparse_periodic_grid
    f hdirect hdisjoint hcover root hA v hv hperiod
  have hz := StageD.sparse_grid_period_eq_zero C hA hD hh g hg hs u hup
  exact hu hz

end
end SpectreGeometry
