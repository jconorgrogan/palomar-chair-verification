module

public import SpectreClusters.StageDRawCaptureInterface
public import SpectreClusters.StageDRawIndexing

@[expose] public section

namespace SpectreClusters.StageD.Raw

/-- Positive row witness: all six original neighbor IDs occur among probe owners. -/
def wordCoversRowB (kind : ClusterKind) (word : List Nat) (i : Nat) : Bool :=
  i < (rawNeighborIDs kind).length &&
    ((rawNeighborIDs kind).getD i []).all word.contains

theorem wordCoversRowB_sound (kind : ClusterKind) (word : List Nat) (i : Nat)
    (h : wordCoversRowB kind word i = true) :
    i < (rawNeighborIDs kind).length ∧
      ∀ j ∈ (rawNeighborIDs kind).getD i [], j ∈ word := by
  simpa only [wordCoversRowB,Bool.and_eq_true,decide_eq_true_eq,
    List.all_eq_true,List.contains_iff_mem] using h

theorem rawPatch_owned_of_probe_word (f : Cell → ClusterPlacement)
    (hf : ValidClusterGridField f) (kind : ClusterKind)
    (hr : ClusterRootOwned f (canonical kind)) (cells : List Cell)
    (hmem : ∀ c ∈ cells, f c ∈ candidateList kind) (i : Nat)
    (hword : ∀ j ∈ (rawNeighborIDs kind).getD i [],
      j ∈ Indexing.indexWord (candidateList kind) cells f) :
    ClusterPatchOwned f (rawPatch kind i) := by
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · simpa only [hp] using hr
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    obtain ⟨c,hc,he⟩ := List.mem_map.mp (hword j hj)
    have hg : (candidateList kind).getD j fallback = f c := by
      rw [←he]
      exact Indexing.candidateAt_idxOf (candidateList kind) fallback (f c) (hmem c hc)
    rw [hg]
    exact (hf c).2.2
end SpectreClusters.StageD.Raw
