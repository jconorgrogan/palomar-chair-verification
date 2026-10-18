module

public import SpectreClusters.StageDRawOwnedProbes
public import SpectreClusters.StageDRawProbeData

@[expose] public section

namespace SpectreClusters.StageD.Raw

/-- Coverage of a finite probe word by the parallel literal choice lists. -/
theorem overChoices_of_indexed {α β : Type} (f : α → β)
    (cells : List α) (choices : List (List β))
    (hlen : cells.length = choices.length)
    (h : ∀ i (hi : i < cells.length), f cells[i] ∈ choices[i]'(hlen ▸ hi)) :
    FiniteCoverWords.OverChoices (cells.map f) choices := by
  induction cells generalizing choices with
  | nil =>
    cases choices with
    | nil => trivial
    | cons ys yss => simp at hlen
  | cons c cs ih =>
    cases choices with
    | nil => simp at hlen
    | cons ys yss =>
      refine ⟨h 0 (by simp),ih yss (by simpa using hlen) ?_⟩
      intro i hi
      exact h (i+1) (by simpa using Nat.add_lt_add_right hi 1)

/-- A probe outside the root must be owned by a disjoint cluster. -/
theorem probe_owner_disjoint (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (kind : ClusterKind) (hr : ClusterRootOwned f (canonical kind))
    (c : Cell) (hout : c ∉ clusterPlacementCells (canonical kind)) :
    DisjointCells (clusterPlacementCells (canonical kind)) (clusterPlacementCells (f c)) := by
  intro d hd hdc
  have he : f c = canonical kind := ((hf c).2.2 d hdc).symm.trans (hr d hd)
  exact hout (he ▸ (hf c).2.1)

theorem canonical_cluster_cells (kind : ClusterKind) :
    clusterPlacementCells (canonical kind) = clusterCells kind := by
  cases kind <;> rfl

/-- Positive alignment certificates cover arbitrary actual probe owners. -/
theorem probe_owner_candidate (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (kind : ClusterKind) (hr : ClusterRootOwned f (canonical kind))
    (c : Cell) (hout : c ∉ clusterCells kind) (ws : List CandidateWitness)
    (hc : alignedChecks (clusterCells kind) (candidateList kind) c ws = true) :
    f c ∈ candidateList kind := by
  apply alignedChecks_complete _ _ c ws hc (f c) (mem_alignedAt (f c) c (hf c).1 (hf c).2.1)
  rw [←canonical_cluster_cells kind]
  exact probe_owner_disjoint f hf kind hr c (by simpa only [canonical_cluster_cells] using hout)

/-- Pairwise soundness requires only the actually represented candidate IDs. -/
theorem probe_word_pairwise (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (kind : ClusterKind) (cells : List Cell)
    (hmem : ∀ c ∈ cells, f c ∈ candidateList kind)
    (hcompat : ∀ a ∈ cells, ∀ b ∈ cells,
      let i := (candidateList kind).idxOf (f a)
      let j := (candidateList kind).idxOf (f b)
      ((candidateList kind).getD i fallback = (candidateList kind).getD j fallback ∨
       DisjointCells (clusterPlacementCells ((candidateList kind).getD i fallback))
         (clusterPlacementCells ((candidateList kind).getD j fallback))) →
      idCompatible kind i j = true) :
    (Indexing.indexWord (candidateList kind) cells f).Pairwise
      (fun i j => idCompatible kind i j = true) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [Indexing.indexWord,List.length_map] at hi hj
  simp only [Indexing.indexWord,List.getElem_map]
  apply hcompat _ (List.getElem_mem hi) _ (List.getElem_mem hj)
  have ha : (candidateList kind).getD ((candidateList kind).idxOf (f cells[i])) fallback = f cells[i] :=
    Indexing.candidateAt_idxOf _ _ _ (hmem _ (List.getElem_mem hi))
  have hb : (candidateList kind).getD ((candidateList kind).idxOf (f cells[j])) fallback = f cells[j] :=
    Indexing.candidateAt_idxOf _ _ _ (hmem _ (List.getElem_mem hj))
  rw [ha,hb]
  exact clusterField_compatible f hf _ _
end SpectreClusters.StageD.Raw
