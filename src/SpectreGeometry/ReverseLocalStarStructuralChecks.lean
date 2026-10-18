module

public import SpectreGeometry.ReverseLocalStarOccurrencesData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch

/-- Structurally recursive sorting keeps finite replay inside the Lean kernel;
no native evaluator or well-founded recursion reduction is required. -/
def insertB {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b::l => if le a b then a::b::l else b::insertB le a l

def sortB {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a::l => insertB le a (sortB le l)

def normalizedStructural (ts : List (List Point)) : List (List Point) :=
  sortB triangleLE (ts.map (sortB pointLE))

def occurrenceStructuralB (ts : List (List Point)) (code : Nat) : Bool :=
  decide (code<744) &&
    (normalizedStructural (ts.map (fun t => t.map (SpectreClusters.rotate ⟨code%6,Nat.mod_lt _ (by decide)⟩))) ==
      normalizedStructural (canonicalStars.getD (code/6) []))

def sideStructuralB (a b : State) (d : Fin 6) (j : Nat) : Bool :=
  let ids := stateBoundaryIds a d
  let ids' := stateBoundaryIds b (opposite d)
  occurrenceStructuralB (localStar a (ids.getD j 0) ++ localStar b (ids'.getD (ids'.length-1-j) 0))
    (sideCode a b d j)
def tripleStructuralB (a b c : State) (d : Fin 6) : Bool :=
  occurrenceStructuralB (localStar a ((stateBoundaryIds a d).getLastD 0) ++
    localStar b ((stateBoundaryIds b (opposite d)).headD 0) ++
    localStar c ((stateBoundaryIds c (rotateTurn 4 (rotateTurn 1 d))).headD 0))
    (tripleCode a b c d)

def SideStructuralCertificate (a : State) : Prop := ∀ (bk : Fin 9) (br d : Fin 6) (j : Fin 12),
  sideMatch a (bk,br) d → 0<j.val → j.val+1<(stateBoundaryIds a d).length →
    sideStructuralB a (bk,br) d j.val = true

def TripleStructuralCertificate (a : State) : Prop := ∀ (bk : Fin 9) (br : Fin 6)
    (ck : Fin 9) (cr d : Fin 6),
  sideMatch a (bk,br) d → sideMatch a (ck,cr) (rotateTurn 1 d) →
    sideMatch (bk,br) (ck,cr) (rotateTurn 2 d) → tripleStructuralB a (bk,br) (ck,cr) d = true

end SpectreGeometry.ReverseLocalStarOccurrences
