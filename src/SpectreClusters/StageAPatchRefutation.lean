module

public import SpectreClusters.StageARegularHatCover

@[expose] public section


/-! Sound finite refutation trees over genuine owner fields. A branch uses
only the actual23-row capture theorem at an already owned tile. A leaf
exhibits two distinct owned placements sharing an exact grid cell. -/
namespace SpectreClusters.StageA

def PatchOwned (f : Cell → HTPlacement) (patch : List HTPlacement) : Prop :=
  ∀ p ∈ patch, RootOwned f p

def rowPatch (root : HTPlacement) (i : Nat) : List HTPlacement :=
  root :: (neighbors root.kind i).map (movePlacement root.turn root.center)

theorem actual_row_patch_owned (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (root : HTPlacement)
    (hr : RootOwned f root) :
    ∃ i ∈ keptIds 2 root.kind, PatchOwned f (rowPatch root i) := by
  have hv := normalizeField_valid f hf root
  have hn := normalizeField_rootOwned f root hr
  obtain ⟨i,hi,hword⟩ := hcaptures (normalizeField f root) hv root.kind hn
  refine ⟨i,hi,?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with hroot | hneighbor
  · exact hroot ▸ hr
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hneighbor
    have hqowned := ((row_neighbors_iff_fieldNeighbor (normalizeField f root) hv root.kind hn
      i hword q).mp hq).1
    exact owned_of_normalized_owned f root q hqowned

def subpatchB (small large : List HTPlacement) : Bool := small.all large.contains

theorem patchOwned_of_subpatch (f : Cell → HTPlacement) (small large : List HTPlacement)
    (h : subpatchB small large = true) (hlarge : PatchOwned f large) : PatchOwned f small := by
  intro p hp
  exact hlarge p (List.contains_iff_mem.mp (List.all_eq_true.mp h p hp))

theorem patch_not_owned_of_collision (f : Cell → HTPlacement) (patch : List HTPlacement)
    (p q : HTPlacement) (c : Cell) (hp : p ∈ patch) (hq : q ∈ patch)
    (hne : p ≠ q) (hcp : c ∈ placementCells p) (hcq : c ∈ placementCells q) :
    ¬PatchOwned f patch := by
  intro ho
  exact hne ((ho p hp c hcp).symm.trans (ho q hq c hcq))

theorem refute_patch_by_rows (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (patch : List HTPlacement)
    (root : HTPlacement) (hr : root ∈ patch)
    (hbranches : ∀ i ∈ keptIds 2 root.kind, ¬PatchOwned f (patch ++ rowPatch root i)) :
    ¬PatchOwned f patch := by
  intro ho
  obtain ⟨i,hi,hrow⟩ := actual_row_patch_owned hcaptures f hf root (ho root hr)
  apply hbranches i hi
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ho p hp
  · exact hrow p hp

end SpectreClusters.StageA
