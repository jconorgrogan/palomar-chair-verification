module

public import SpectreClusters.NeighborCandidates

@[expose] public section


namespace SpectreClusters

/-- Data-only comparisons avoid constructing large decidability proof trees. -/
def cellEqB (a b : Cell) : Bool :=
  a.center.1 == b.center.1 && a.center.2 == b.center.2 && a.sector.val == b.sector.val

theorem cellEqB_iff (a b : Cell) : cellEqB a b = true ↔ a = b := by
  cases a with
  | mk a k =>
    cases b with
    | mk b l =>
      simp [cellEqB,Prod.ext_iff,Fin.ext_iff,and_assoc]

def disjointCellsB (A B : List Cell) : Bool :=
  A.all (fun a => B.all (fun b => !(cellEqB a b)))

theorem disjointCellsB_iff (A B : List Cell) : disjointCellsB A B = true ↔ DisjointCells A B := by
  simp [disjointCellsB,DisjointCells,List.all_eq_true,← Bool.not_eq_true,cellEqB_iff]
  constructor
  · intro h c hc hd
    exact h c hc c hd rfl
  · intro h a ha b hb he
    subst b
    exact h a ha hb

def poseEqB (a b : HTPlacement) : Bool :=
  a.kind == b.kind && a.turn.val == b.turn.val &&
    a.center.1 == b.center.1 && a.center.2 == b.center.2

theorem poseEqB_iff (a b : HTPlacement) : poseEqB a b = true ↔ a = b := by
  cases a with
  | mk ka ra ca =>
    cases b with
    | mk kb rb cb =>
      simp [poseEqB,Prod.ext_iff,Fin.ext_iff,and_assoc]

def compatibleB (a b : HTPlacement) : Bool :=
  poseEqB a b || disjointCellsB (placementCells a) (placementCells b)

theorem compatibleB_iff (a b : HTPlacement) : compatibleB a b = true ↔
    a = b ∨ DisjointCells (placementCells a) (placementCells b) := by
  simp [compatibleB,poseEqB_iff,disjointCellsB_iff]

end SpectreClusters
