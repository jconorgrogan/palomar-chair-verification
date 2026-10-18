module

public import SpectreClusters.StageDRawModel
public import SpectreClusters.FiniteCoverWords

@[expose] public section


/-! Generic indexing of a genuine partition restriction into a finite
candidate table. The literal candidate completeness and compatibility-bit
binding are intentionally separate, checkable obligations. -/
namespace SpectreClusters.StageD.Raw.Indexing

def compatibleB (a b : ClusterPlacement) : Bool :=
  Raw.poseEqB a b || disjointCellsB (clusterPlacementCells a) (clusterPlacementCells b)

theorem compatibleB_iff (a b : ClusterPlacement) : compatibleB a b = true ↔
    a = b ∨ DisjointCells (clusterPlacementCells a) (clusterPlacementCells b) := by
  simp [compatibleB,Raw.poseEqB_iff,disjointCellsB_iff]

def candidateAt (candidates : List ClusterPlacement) (fallback : ClusterPlacement) (i : Nat) :
    ClusterPlacement := candidates.getD i fallback

def indexedChoices (candidates : List ClusterPlacement) (fallback : ClusterPlacement)
    (c : Cell) : List Nat :=
  (List.range candidates.length).filter (fun i =>
    (clusterPlacementCells (candidateAt candidates fallback i)).contains c)

def indexWord (candidates : List ClusterPlacement) (cells : List Cell)
    (f : Cell → ClusterPlacement) : List Nat := cells.map (fun c => candidates.idxOf (f c))

def indexCompatible (candidates : List ClusterPlacement) (fallback : ClusterPlacement)
    (i j : Nat) : Bool :=
  compatibleB (candidateAt candidates fallback i) (candidateAt candidates fallback j)

theorem candidateAt_idxOf (candidates : List ClusterPlacement) (fallback p : ClusterPlacement)
    (hp : p ∈ candidates) : candidateAt candidates fallback (candidates.idxOf p) = p := by
  have h := List.idxOf_lt_length_of_mem hp
  simp [candidateAt,List.getD_eq_getElem?_getD,h]

theorem indexWord_overChoices (candidates : List ClusterPlacement) (fallback : ClusterPlacement)
    (cells : List Cell) (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hmem : ∀ c ∈ cells, f c ∈ candidates) :
    FiniteCoverWords.OverChoices (indexWord candidates cells f)
      (cells.map (indexedChoices candidates fallback)) := by
  induction cells with
  | nil => trivial
  | cons c cells ih =>
    refine ⟨?_,ih (fun d hd => hmem d (by simp [hd]))⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (List.idxOf_lt_length_of_mem (hmem c (by simp))),?_⟩
    rw [candidateAt_idxOf candidates fallback (f c) (hmem c (by simp))]
    simpa using (hf c).2.1

theorem indexWord_pairwise (candidates : List ClusterPlacement) (fallback : ClusterPlacement)
    (cells : List Cell) (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hmem : ∀ c ∈ cells, f c ∈ candidates) :
    (indexWord candidates cells f).Pairwise
      (fun i j => indexCompatible candidates fallback i j = true) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [indexWord,List.length_map] at hi hj
  simp only [indexWord,List.getElem_map,indexCompatible]
  rw [candidateAt_idxOf candidates fallback (f cells[i]) (hmem _ (List.getElem_mem _)),
    candidateAt_idxOf candidates fallback (f cells[j]) (hmem _ (List.getElem_mem _))]
  exact (compatibleB_iff _ _).mpr (clusterField_compatible f hf _ _)

/-- A genuine partition yields an enumerated ID word whenever the finite
candidate list has been shown to contain its represented placements. -/
theorem indexWord_mem_enumerate (candidates : List ClusterPlacement) (fallback : ClusterPlacement)
    (cells : List Cell) (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hmem : ∀ c ∈ cells, f c ∈ candidates) :
    indexWord candidates cells f ∈
      FiniteCoverWords.enumerate (indexCompatible candidates fallback)
        (cells.map (indexedChoices candidates fallback)) := by
  apply (FiniteCoverWords.mem_enumerate_iff _ _ _).mpr
  exact ⟨indexWord_overChoices candidates fallback cells f hf hmem,
    indexWord_pairwise candidates fallback cells f hf hmem⟩

end SpectreClusters.StageD.Raw.Indexing
