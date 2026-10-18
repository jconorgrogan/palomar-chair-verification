module

public import SpectreClusters.FastChecks
public import SpectreClusters.StageAData
public import SpectreClusters.StageAWordModel

@[expose] public section


/-! Boolean checks have declarative soundness. Literal proofs are split into
small bounded modules; no physical registration is asserted here. -/
namespace SpectreClusters.StageA

def canonicalRoot (kind : HTKind) : HTPlacement := ⟨kind,0,(0,0)⟩

def candidateAt (kind : HTKind) (i : Nat) : HTPlacement :=
  (candidateList kind).getD i (canonicalRoot kind)

def indexedChoices (kind : HTKind) (c : Cell) : List Nat :=
  (List.range (candidateList kind).length).filter fun i =>
    (placementCells (candidateAt kind i)).any (cellEqB c)

def candidateCheckB (kind : HTKind) (p : HTPlacement) : Bool :=
  !(disjointCellsB (htCells kind) (placementCells p)) ||
    (candidateList kind).any (poseEqB p)

def rawNeighborsAt (a : Cell) : List HTPlacement :=
  (contacts a).flatMap fun c =>
    [HTKind.hat,HTKind.turtle].flatMap fun kind =>
      (htCells kind).map fun b => alignPlacement kind b c

theorem candidateCheckB_sound (kind : HTKind) (p : HTPlacement)
    (hd : DisjointCells (htCells kind) (placementCells p))
    (h : candidateCheckB kind p = true) : p ∈ candidateList kind := by
  have hdis : disjointCellsB (htCells kind) (placementCells p) = true :=
    (disjointCellsB_iff _ _).mpr hd
  simp only [candidateCheckB,hdis,Bool.not_true,Bool.false_or,
    List.any_eq_true,poseEqB_iff] at h
  obtain ⟨q,hq,hpq⟩ := h
  simpa only [hpq] using hq

theorem candidateList_complete_of_check (kind : HTKind)
    (hc : (rawNeighborPlacements (htCells kind)).all (candidateCheckB kind) = true)
    (p : HTPlacement) (hp : ShapeContact (htCells kind) (placementCells p))
    (hd : DisjointCells (htCells kind) (placementCells p)) :
    p ∈ candidateList kind := by
  apply candidateCheckB_sound kind p hd
  exact List.all_eq_true.mp hc p (rawNeighborPlacements_complete _ _ hp)

theorem rawChecks_from_cells (kind : HTKind)
    (hc : (htCells kind).all (fun c => (rawNeighborsAt c).all (candidateCheckB kind)) = true) :
    (rawNeighborPlacements (htCells kind)).all (candidateCheckB kind) = true := by
  simpa only [rawNeighborPlacements,rawNeighborsAt,List.all_flatMap] using hc

end SpectreClusters.StageA
