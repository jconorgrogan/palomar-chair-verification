module

public import SpectreClusters.StageDRawCompatibilityModel

@[expose] public section

namespace SpectreClusters.StageD.Raw

def indexedClusterCell (p : ClusterPlacement) (i : Nat) : Cell :=
  moveCell p.turn p.center ((clusterCells p.kind).getD i ⟨(0,0),0⟩)

theorem indexedClusterCell_mem (p : ClusterPlacement) (i : Nat)
    (hi : i < (clusterCells p.kind).length) : indexedClusterCell p i ∈ clusterPlacementCells p := by
  apply List.mem_map.mpr
  refine ⟨(clusterCells p.kind).getD i ⟨(0,0),0⟩,?_,rfl⟩
  simpa [List.getD_eq_getElem?_getD,hi] using (List.getElem_mem hi)

def indexedClashB (p q : ClusterPlacement) (ij : Nat × Nat) : Bool :=
  ij.1 < (clusterCells p.kind).length && ij.2 < (clusterCells q.kind).length &&
    !(poseEqB p q) && cellEqB (indexedClusterCell p ij.1) (indexedClusterCell q ij.2)

theorem indexedClashB_incompatible (p q : ClusterPlacement) (ij : Nat × Nat)
    (h : indexedClashB p q ij = true) :
    ¬ (p = q ∨ DisjointCells (clusterPlacementCells p) (clusterPlacementCells q)) := by
  simp only [indexedClashB,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true,cellEqB_iff] at h
  obtain ⟨⟨⟨hi,hj⟩,hne⟩,he⟩ := h
  intro hpq
  rcases hpq with hpq | hd
  · have ht := (poseEqB_iff p q).mpr hpq
    rw [ht] at hne
    contradiction
  · exact hd (indexedClusterCell p ij.1) (indexedClusterCell_mem p ij.1 hi)
      (he ▸ indexedClusterCell_mem q ij.2 hj)
end SpectreClusters.StageD.Raw
