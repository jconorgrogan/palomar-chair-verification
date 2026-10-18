module

public import SpectreClusters.NeighborCandidates
public import SpectreFinite.PatchEnumeration

@[expose] public section


/-! Complete finite corona model for exact cell tilings. The physical-to-grid
registration and realization obligations remain separate. No disk topology,
no-hole pruning, or completeness callback is assumed. -/
namespace SpectreClusters

def halo (root : List Cell) : List Cell :=
  (root.flatMap contacts).eraseDups.filter (fun c => !(root.contains c))

theorem mem_halo_iff (root : List Cell) (c : Cell) :
    c ∈ halo root ↔ c ∉ root ∧ ∃ a ∈ root, CellContact a c := by
  simp [halo,mem_contacts_iff,and_comm]

/-- Every cell names the placement containing it; all cells of that placement
name the same placement. This is a genuine partition of the discrete grid. -/
def ValidGridField (f : Cell → HTPlacement) : Prop :=
  ∀ c, c ∈ placementCells (f c) ∧ ∀ d ∈ placementCells (f c), f d = f c

/-- The root placement is genuinely present in the cell partition. -/
def RootOwned (f : Cell → HTPlacement) (root : HTPlacement) : Prop :=
  ∀ c ∈ placementCells root, f c = root

theorem field_compatible (f : Cell → HTPlacement) (hf : ValidGridField f) (a b : Cell) :
    f a = f b ∨ DisjointCells (placementCells (f a)) (placementCells (f b)) := by
  by_cases he : f a = f b
  · exact Or.inl he
  · refine Or.inr ?_
    intro c ha hb
    exact he (((hf a).2 c ha).symm.trans ((hf b).2 c hb))

theorem halo_field_neighbor (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root) (c : Cell)
    (hc : c ∈ halo (placementCells root)) :
    f c ∈ neighborPlacements (placementCells root) := by
  obtain ⟨hout,a,ha,hcontact⟩ := (mem_halo_iff _ _).mp hc
  apply neighborPlacements_complete
  · exact ⟨a,ha,c,(hf c).1,hcontact⟩
  · intro d hd hdf
    have hsame : f c = root := ((hf c).2 d hdf).symm.trans (hr d hd)
    exact hout (hsame ▸ (hf c).1)

def coronaChoices (root : HTPlacement) (c : Cell) : List HTPlacement :=
  (neighborPlacements (placementCells root)).filter (fun p => (placementCells p).contains c)

def CoronaCompatible (a b : Cell × HTPlacement) : Prop :=
  a.2 = b.2 ∨ DisjointCells (placementCells a.2) (placementCells b.2)
instance : DecidableRel CoronaCompatible := fun a b =>
  inferInstanceAs (Decidable (_ ∨ _))

def coronaAssignments (root : HTPlacement) : List (List (Cell × HTPlacement)) :=
  SpectreFinite.Search.enumerate (coronaChoices root) CoronaCompatible (halo (placementCells root))

/-- Exhaustiveness is derived from cell coverage and coherence. It does not
assume that an externally supplied list contains every actual corona. -/
theorem gridRestriction_mem_coronaAssignments (f : Cell → HTPlacement)
    (hf : ValidGridField f) (root : HTPlacement) (hr : RootOwned f root) :
    ((halo (placementCells root)).map (fun c => (c,f c))) ∈ coronaAssignments root := by
  apply (SpectreFinite.Search.mem_enumerate_iff _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · simp [List.map_map,Function.comp_def]
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.getElem_map]
    exact field_compatible f hf _ _
  · intro p hp
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
    apply List.mem_filter.mpr
    exact ⟨halo_field_neighbor f hf root hr c hc,by simpa using (hf c).1⟩

end SpectreClusters
