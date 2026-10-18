module

public import SpectreClusters.StageDFinalRows
public import SpectreClusters.FastChecks
public import SpectreClusters.ReverseClusterCocycleData

@[expose] public section


/-! Soundness of small final-row certificates. Final-row completeness is
not asserted here and must come from the separate exhaustive reduction. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch

abbrev Row := Fin 20

def canonical (k : ClusterKind) : ClusterPlacement := ⟨k,0,(0,0)⟩
def rowKind (i : Row) : ClusterKind := rowKinds.getD i.val .t7h
def rowMark (i : Row) : Fin 9 := rowMarks.getD i.val 0
def rowNeighbors (i : Row) : List ClusterPlacement := rowPorts.getD i.val []
def rowPort (i : Row) (d : Fin 6) : ClusterPlacement :=
  (rowNeighbors i).getD d.val (canonical (rowKind i))
def rowPatch (i : Row) : List ClusterPlacement := canonical (rowKind i) :: rowNeighbors i

def movedPatch (i : Row) (p : ClusterPlacement) : List ClusterPlacement :=
  (rowPatch i).map (moveClusterPlacement p.turn p.center)

def ClusterPatchOwned (f : Cell → ClusterPlacement) (patch : List ClusterPlacement) : Prop :=
  ∀ p ∈ patch, ClusterRootOwned f p

def clusterPoseEqB (a b : ClusterPlacement) : Bool :=
  a.kind == b.kind && a.turn.val == b.turn.val &&
    a.center.1 == b.center.1 && a.center.2 == b.center.2

theorem clusterPoseEqB_iff (a b : ClusterPlacement) : clusterPoseEqB a b = true ↔ a = b := by
  cases a with
  | mk ka ra ca =>
    cases b with
    | mk kb rb cb => simp [clusterPoseEqB,Prod.ext_iff,Fin.ext_iff,and_assoc]

def clashB (A B : List ClusterPlacement) : Option ClashWitness → Bool
  | none => false
  | some w =>
    w.first < A.length && w.second < B.length &&
    !(clusterPoseEqB (A.getD w.first (canonical .t7h)) (B.getD w.second (canonical .t7h))) &&
    (clusterPlacementCells (A.getD w.first (canonical .t7h))).any (cellEqB w.cell) &&
    (clusterPlacementCells (B.getD w.second (canonical .t7h))).any (cellEqB w.cell)

theorem clashB_not_owned (f : Cell → ClusterPlacement) (A B : List ClusterPlacement)
    (w : Option ClashWitness) (hc : clashB A B w = true)
    (ha : ClusterPatchOwned f A) (hb : ClusterPatchOwned f B) : False := by
  cases w with
  | none => simp [clashB] at hc
  | some w =>
    simp only [clashB,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true,
      List.any_eq_true,cellEqB_iff] at hc
    obtain ⟨⟨⟨⟨hia,hib⟩,hne⟩,ca,hca,hea⟩,cb,hcb,heb⟩ := hc
    have hma : A.getD w.first (canonical .t7h) ∈ A := by
      simpa [List.getD_eq_getElem?_getD,hia] using (List.getElem_mem hia)
    have hmb : B.getD w.second (canonical .t7h) ∈ B := by
      simpa [List.getD_eq_getElem?_getD,hib] using (List.getElem_mem hib)
    have he : A.getD w.first (canonical .t7h) = B.getD w.second (canonical .t7h) :=
      (ha _ hma w.cell (hea ▸ hca)).symm.trans (hb _ hmb w.cell (heb ▸ hcb))
    have ht := (clusterPoseEqB_iff _ _).mpr he
    rw [ht] at hne
    contradiction

def pairWitness (i : Row) (d : Fin 6) (j : Row) : Option ClashWitness :=
  (((pairWitnesses.getD i.val []).getD d.val []).getD j.val none)

def pairLawsB (i : Row) (d : Fin 6) (j : Row) : Bool :=
  let p := rowPort i d
  clusterPoseEqB (moveClusterPlacement p.turn p.center
    (rowPort j (turnDiff (opposite d) p.turn))) (canonical (rowKind i)) &&
  clusterPoseEqB (moveClusterPlacement p.turn p.center
    (rowPort j (turnDiff (rotateTurn 2 d) p.turn))) (rowPort i (rotateTurn 1 d)) &&
  decide (ReverseExistence.sideMatch (rowMark i,0) (rowMark j,p.turn) d)

def pairCheckB (i : Row) (d : Fin 6) (j : Row) : Bool :=
  !(rowKind j == (rowPort i d).kind) ||
    clashB (rowPatch i) (movedPatch j (rowPort i d)) (pairWitness i d j) || pairLawsB i d j

theorem pairLaws_of_checked (i : Row) (d : Fin 6) (j : Row)
    (hcheck : pairCheckB i d j = true) (hkind : rowKind j = (rowPort i d).kind)
    (f : Cell → ClusterPlacement) (hi : ClusterPatchOwned f (rowPatch i))
    (hj : ClusterPatchOwned f (movedPatch j (rowPort i d))) : pairLawsB i d j = true := by
  have hn : clashB (rowPatch i) (movedPatch j (rowPort i d)) (pairWitness i d j) = false := by
    cases he : clashB (rowPatch i) (movedPatch j (rowPort i d)) (pairWitness i d j)
    · rfl
    · exact False.elim (clashB_not_owned f _ _ _ he hi hj)
  simpa [pairCheckB,hkind,hn] using hcheck

def uniqueCheckB (i j : Row) : Bool :=
  !(rowKind i == rowKind j) || (i == j) ||
    clashB (rowPatch i) (rowPatch j) ((uniqueWitnesses.getD i.val []).getD j.val none)

theorem row_eq_of_checked (i j : Row) (hcheck : uniqueCheckB i j = true)
    (hkind : rowKind i = rowKind j) (f : Cell → ClusterPlacement)
    (hi : ClusterPatchOwned f (rowPatch i)) (hj : ClusterPatchOwned f (rowPatch j)) : i = j := by
  have hn : clashB (rowPatch i) (rowPatch j)
      ((uniqueWitnesses.getD i.val []).getD j.val none) = false := by
    cases he : clashB (rowPatch i) (rowPatch j)
      ((uniqueWitnesses.getD i.val []).getD j.val none)
    · rfl
    · exact False.elim (clashB_not_owned f _ _ _ he hi hj)
  unfold uniqueCheckB at hcheck
  rw [hn] at hcheck
  simpa [hkind] using hcheck

end SpectreClusters.StageD
