module

public import SpectreGeometry.GridKiteProbeReal
public import SpectreClusters.GridCoverModel

@[expose] public section


/-! Genuine closed-body coverage and disjoint ordinary interiors induce the
source's cell-ownership field. No cell-coverage or recognition callback is used. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.GridKiteProbe

def placementKiteBody (p : HTPlacement) : Set RealPoint :=
  ⋃ c ∈ placementCells p, gridKiteBody c

theorem gridKiteBody_subset_placement (p : HTPlacement) (c : Cell)
    (hc : c ∈ placementCells p) : gridKiteBody c ⊆ placementKiteBody p := by
  intro x hx
  exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,hx⟩⟩

theorem gridProbe_mem_placement_iff (p : HTPlacement) (c : Cell) :
    integerPoint (probe c) ∈ placementKiteBody p ↔ c ∈ placementCells p := by
  constructor
  · intro hx
    obtain ⟨d,hd⟩ := mem_iUnion.mp hx
    obtain ⟨hd,hx⟩ := mem_iUnion.mp hd
    rwa [gridProbe_unique c d hx]
  · intro hc
    exact gridKiteBody_subset_placement p c hc (interior_subset (gridProbe_mem_interior c))

theorem gridProbe_interior_placement (p : HTPlacement) (c : Cell)
    (hc : c ∈ placementCells p) : integerPoint (probe c) ∈ interior (placementKiteBody p) :=
  interior_mono (gridKiteBody_subset_placement p c hc) (gridProbe_mem_interior c)

section Extraction
variable {ι : Type*} (p : ι → HTPlacement)
  (hcover : ∀ x : RealPoint, ∃ i, x ∈ placementKiteBody (p i))

def probeOwner (c : Cell) : ι := Classical.choose (hcover (integerPoint (probe c)))

theorem probeOwner_contains (c : Cell) : c ∈ placementCells (p (probeOwner p hcover c)) :=
  (gridProbe_mem_placement_iff _ _).mp (Classical.choose_spec (hcover (integerPoint (probe c))))

def fieldOfKiteTiling (c : Cell) : HTPlacement := p (probeOwner p hcover c)

variable (hdisjoint : Pairwise fun i j =>
  Disjoint (interior (placementKiteBody (p i))) (interior (placementKiteBody (p j))))

include hdisjoint in
theorem fieldOfKiteTiling_valid : ValidGridField (fieldOfKiteTiling p hcover) := by
  intro c
  refine ⟨probeOwner_contains p hcover c,?_⟩
  intro d hd
  have hsame : probeOwner p hcover d = probeOwner p hcover c := by
    by_contra hn
    have hi := gridProbe_interior_placement (p (probeOwner p hcover d)) d
      (probeOwner_contains p hcover d)
    have hj := gridProbe_interior_placement (p (probeOwner p hcover c)) d hd
    exact Set.disjoint_left.mp (hdisjoint hn) hi hj
  exact congrArg p hsame

include p hcover hdisjoint in
/-- Any actual real tiling by registered literal H/T carriers yields a valid
source grid field; the two geometric hypotheses are ordinary tiling hypotheses. -/
theorem exists_validGridField_of_kite_tiling : ∃ f : Cell → HTPlacement, ValidGridField f :=
  ⟨fieldOfKiteTiling p hcover,fieldOfKiteTiling_valid p hcover hdisjoint⟩

end Extraction
end
end SpectreGeometry
