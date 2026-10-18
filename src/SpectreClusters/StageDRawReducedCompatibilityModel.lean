module

public import SpectreClusters.StageDRawIndexedCollision

@[expose] public section

namespace SpectreClusters.StageD.Raw

def reducedCompatibilityCheck (kind : ClusterKind) (a : Nat)
    (ws : List (Nat × (Nat × Nat))) : Bool :=
  ws.all fun w => idCompatible kind a w.1 || indexedClashB
    ((candidateList kind).getD a fallback) ((candidateList kind).getD w.1 fallback) w.2

theorem reducedCompatibilityCheck_sound (kind : ClusterKind) (a b : Nat)
    (ws : List (Nat × (Nat × Nat)))
    (h : reducedCompatibilityCheck kind a ws = true) (hb : b ∈ ws.map Prod.fst)
    (hc : (candidateList kind).getD a fallback = (candidateList kind).getD b fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList kind).getD a fallback))
        (clusterPlacementCells ((candidateList kind).getD b fallback))) : idCompatible kind a b = true := by
  obtain ⟨⟨b',ij⟩,hm,he⟩ := List.mem_map.mp hb
  have ht := List.all_eq_true.mp h (b',ij) hm
  simp only [Bool.or_eq_true] at ht
  have he' : b' = b := he
  subst b'
  rcases ht with ht | ht
  · exact ht
  · exact False.elim (indexedClashB_incompatible _ _ _ ht hc)
end SpectreClusters.StageD.Raw
