module

public import SpectreClusters.StageDRawWordModel

@[expose] public section

namespace SpectreClusters.StageD.Raw

def pairWitnessCheck (a b : ClusterPlacement) (w : Cell) : Bool :=
  !(poseEqB a b) && (clusterPlacementCells a).any (cellEqB w) &&
    (clusterPlacementCells b).any (cellEqB w)

theorem pairWitnessCheck_incompatible (a b : ClusterPlacement) (w : Cell)
    (h : pairWitnessCheck a b w = true) :
    ¬ (a = b ∨ DisjointCells (clusterPlacementCells a) (clusterPlacementCells b)) := by
  simp only [pairWitnessCheck,Bool.and_eq_true,Bool.not_eq_true,
    List.any_eq_true,cellEqB_iff] at h
  obtain ⟨⟨hne,⟨ca,ha,hea⟩⟩,cb,hb,heb⟩ := h
  intro he
  rcases he with he | hd
  · have hp : poseEqB a b = true := (poseEqB_iff a b).mpr he
    simp [hp] at hne
  · exact hd w (by simpa only [hea] using ha) (by simpa only [heb] using hb)

def compatibilityRowCheck (k : ClusterKind) (a : Nat) (ws : List Cell) : Bool :=
  (List.range (candidateList k).length).all fun b =>
    idCompatible k a b || pairWitnessCheck
      ((candidateList k).getD a fallback) ((candidateList k).getD b fallback)
      (ws.getD b ⟨(0,0),0⟩)

theorem compatibilityRowCheck_sound (k : ClusterKind) (a b : Nat) (ws : List Cell)
    (h : compatibilityRowCheck k a ws = true) (hb : b < (candidateList k).length)
    (hc : (candidateList k).getD a fallback = (candidateList k).getD b fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList k).getD a fallback))
        (clusterPlacementCells ((candidateList k).getD b fallback))) :
    idCompatible k a b = true := by
  have ht := List.all_eq_true.mp h b (List.mem_range.mpr hb)
  simp only [Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact ht
  · exact False.elim (pairWitnessCheck_incompatible _ _ _ ht hc)
end SpectreClusters.StageD.Raw
