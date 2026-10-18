module

public import SpectreClusters.SparseClusterPartition

@[expose] public section


/-! The intrinsic cluster owner of each actual kite cell, with exact coherence
and translation covariance. This is still a field on the fine kite grid;
it is not a marked-hexagon Position-to-State field. -/
namespace SpectreClusters.StageA

noncomputable def assignedRoot (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (c : Cell) : HTPlacement :=
  Classical.choose (sparse_all_cells_covered hcaptures f hf hsparse c)

theorem assignedRoot_spec (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f) (c : Cell) :
    RootOwned f (assignedRoot hcaptures f hf hsparse c) ∧
    (assignedRoot hcaptures f hf hsparse c).kind = .turtle ∧
    c ∈ assignedCells f (assignedRoot hcaptures f hf hsparse c) :=
  Classical.choose_spec (sparse_all_cells_covered hcaptures f hf hsparse c)

theorem assignedRoot_unique (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (c : Cell) (r : HTPlacement) (hr : RootOwned f r) (hk : r.kind = .turtle)
    (hc : c ∈ assignedCells f r) : assignedRoot hcaptures f hf hsparse c = r := by
  classical
  by_cases hn : assignedRoot hcaptures f hf hsparse c = r
  · exact hn
  · have hs := assignedRoot_spec hcaptures f hf hsparse c
    exact False.elim (sparse_assigned_cells_disjoint hcaptures f hf hsparse _ r hs.1 hs.2.1 hr hk hn
      c hs.2.2 hc)

theorem assignedRoot_coherent (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (c d : Cell) (hd : d ∈ assignedCells f (assignedRoot hcaptures f hf hsparse c)) :
    assignedRoot hcaptures f hf hsparse d = assignedRoot hcaptures f hf hsparse c := by
  have hs := assignedRoot_spec hcaptures f hf hsparse c
  exact assignedRoot_unique hcaptures f hf hsparse d _ hs.1 hs.2.1 hd

theorem assignedRoot_piece_owned (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (c : Cell) (p : HTPlacement)
    (hp : p ∈ assignedPieces f (assignedRoot hcaptures f hf hsparse c)) : RootOwned f p := by
  have hs := assignedRoot_spec hcaptures f hf hsparse c
  exact (sparse_assigned_cluster_owned hcaptures f hf hsparse _ hs.1 hs.2.1).2 p hp

theorem assignedCells_translate_period (f : Cell → HTPlacement) (u : Point)
    (hperiod : GridFieldTranslationPeriod f u) (r : HTPlacement) :
    assignedCells f (movePlacement 0 u r) = (assignedCells f r).map (moveCell 0 u) := by
  simp only [assignedCells,assignedPieces_translate_period f u hperiod r,
    List.flatMap_map,List.map_flatMap]
  exact congrArg (fun h : HTPlacement → List Cell => (assignedPieces f r).flatMap h)
    (funext (fun p => placementCells_moved 0 u p))

/-- Every nonzero fine-grid period remains a period of the actual cluster
owner map in the same integer coordinates. No coarse chart is assumed. -/
theorem assignedRoot_translate_period (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (u : Point) (hperiod : GridFieldTranslationPeriod f u) (c : Cell) :
    assignedRoot hcaptures f hf hsparse (moveCell 0 u c) =
      movePlacement 0 u (assignedRoot hcaptures f hf hsparse c) := by
  have hs := assignedRoot_spec hcaptures f hf hsparse c
  apply assignedRoot_unique hcaptures f hf hsparse (moveCell 0 u c) _
    (GridFieldTranslationPeriod.rootOwned f u hperiod _ hs.1) hs.2.1
  rw [assignedCells_translate_period f u hperiod]
  exact List.mem_map.mpr ⟨c,hs.2.2,rfl⟩

end SpectreClusters.StageA
