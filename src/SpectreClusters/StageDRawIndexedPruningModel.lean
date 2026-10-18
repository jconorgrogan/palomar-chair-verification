module

public import SpectreClusters.StageDRawIndexedCollision

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning

inductive ProbePruneWitness where
  | keep
  | blocked (otherProbe : Nat) (collisionIndices : List (Nat × Nat))

def probePruneEntryCheck (kind : ClusterKind) (old newer : List (List Nat))
    (i a : Nat) : ProbePruneWitness → Bool
  | .keep => (newer.getD i []).contains a
  | .blocked j ws => j < old.length && (old.getD j []).all fun b =>
      indexedClashB ((candidateList kind).getD a fallback)
        ((candidateList kind).getD b fallback) (ws.getD b (0,0))

def probePruneRowCheck (kind : ClusterKind) (old newer : List (List Nat))
    (i : Nat) (witnesses : List ProbePruneWitness) : Bool :=
  (old.getD i []).all fun a => probePruneEntryCheck kind old newer i a
    (witnesses.getD a .keep)

/-- Each removed owner clashes with every possible owner of another probe. -/
theorem probePruneEntryCheck_sound (kind : ClusterKind) (old newer : List (List Nat))
    (chosen : Nat → Nat) (i : Nat) (hi : i < old.length) (w : ProbePruneWitness)
    (h : probePruneEntryCheck kind old newer i (chosen i) w = true)
    (hchoices : ∀ j, j < old.length → chosen j ∈ old.getD j [])
    (hcompatible : ∀ j, j < old.length →
      (candidateList kind).getD (chosen i) fallback = (candidateList kind).getD (chosen j) fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList kind).getD (chosen i) fallback))
        (clusterPlacementCells ((candidateList kind).getD (chosen j) fallback))) :
    chosen i ∈ newer.getD i [] := by
  cases w with
  | keep => simpa only [probePruneEntryCheck,List.contains_iff_mem] using h
  | blocked j ws =>
    simp only [probePruneEntryCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨hj,hall⟩ := h
    have hb := List.all_eq_true.mp hall (chosen j) (hchoices j hj)
    exact False.elim (indexedClashB_incompatible _ _ _ hb (hcompatible j hj))

theorem probePruneRowCheck_sound (kind : ClusterKind) (old newer : List (List Nat))
    (chosen : Nat → Nat) (i : Nat) (hi : i < old.length)
    (witnesses : List ProbePruneWitness)
    (h : probePruneRowCheck kind old newer i witnesses = true)
    (hchoices : ∀ j, j < old.length → chosen j ∈ old.getD j [])
    (hcompatible : ∀ j, j < old.length →
      (candidateList kind).getD (chosen i) fallback = (candidateList kind).getD (chosen j) fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList kind).getD (chosen i) fallback))
        (clusterPlacementCells ((candidateList kind).getD (chosen j) fallback))) :
    chosen i ∈ newer.getD i [] := by
  exact probePruneEntryCheck_sound kind old newer chosen i hi _
    (List.all_eq_true.mp h (chosen i) (hchoices i hi)) hchoices hcompatible
theorem probePruneAll_sound (kind : ClusterKind) (old newer : List (List Nat))
    (chosen : Nat → Nat)
    (hchecks : ∀ i, i < old.length → ∃ ws, probePruneRowCheck kind old newer i ws = true)
    (hchoices : ∀ i, i < old.length → chosen i ∈ old.getD i [])
    (hcompatible : ∀ i, i < old.length → ∀ j, j < old.length →
      (candidateList kind).getD (chosen i) fallback = (candidateList kind).getD (chosen j) fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList kind).getD (chosen i) fallback))
        (clusterPlacementCells ((candidateList kind).getD (chosen j) fallback))) :
    ∀ i, i < old.length → chosen i ∈ newer.getD i [] := by
  intro i hi
  obtain ⟨ws,hws⟩ := hchecks i hi
  exact probePruneRowCheck_sound kind old newer chosen i hi ws hws hchoices (hcompatible i hi)
end SpectreClusters.StageD.Raw.IndexedPruning
