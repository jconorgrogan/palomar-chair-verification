module

public import SpectreFinite.ParentBoundaryConsequences
public import SpectreFinite.ParentRotation

@[expose] public section


/-!
Exact local frames of the six adjacent parents, with explicit cyclic side
indices. A full parent shape is not inferred from a bounded projection without
the separately stated global nine-parent-shape premise.
-/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

abbrev NativeSide := Position × Fin 6

structure FrameInfo where
  anchor : Position
  turn : Fin 6
  kind : TileKind
  mateSide : Fin 6
  deriving DecidableEq

def defaultFrame : FrameInfo := ⟨(0,0),0,0,0⟩
def frameAt (frames : List FrameInfo) (s : Fin 6) : FrameInfo := frames.getD s.val defaultFrame

def inFive (x : Position) : Prop :=
  -5 ≤ x.1 ∧ x.1 ≤ 5 ∧ -5 ≤ x.2 ∧ x.2 ≤ 5 ∧ -5 ≤ x.1+x.2 ∧ x.1+x.2 ≤ 5
instance (x : Position) : Decidable (inFive x) := inferInstanceAs (Decidable (_ ∧ _))

theorem inFive_iff (x : Position) : inFive x ↔ x ∈ hexRegion 5 :=
  (mem_hexRegion_iff 5 x).symm

def placedPosition (a : Position) (t : Fin 6) (c : PlacedHex) : Position :=
  addPos a (rotatePosition t (pos c))

/-- Compare only genuinely displayed child cells. This is intentionally weaker
than saying that the whole neighboring parent has the proposed shape. -/
def ChildAgreement (f : Position → State) (a : Position) (t : Fin 6) (j : TileKind) : Prop :=
  ∀ c ∈ children j, inFive (placedPosition a t c) →
    f (placedPosition a t c) = rotateState t (c.kind,c.turn)
instance (f : Position → State) (a : Position) (t : Fin 6) (j : TileKind) :
    Decidable (ChildAgreement f a t j) :=
  inferInstanceAs (Decidable (∀ c ∈ children j, _ → _))

def matchingKinds (f : Position → State) (a : Position) (t : Fin 6) : List TileKind :=
  (List.finRange 9).filter (fun j => decide (ChildAgreement f a t j))

theorem mem_matchingKinds_iff (f : Position → State) (a : Position)
    (t : Fin 6) (j : TileKind) : j ∈ matchingKinds f a t ↔ ChildAgreement f a t j := by
  simp [matchingKinds]

def placedSide (j : TileKind) (a : Position) (t : Fin 6) (e : SideRef) : NativeSide :=
  (placedPosition a t (hexAt (children j) e), rotateTurn t e.side)
def placedSegment (j : TileKind) (a : Position) (t s : Fin 6) : List NativeSide :=
  (segment j s).map (placedSide j a t)

def acrossSide (e : NativeSide) : NativeSide :=
  (addPos e.1 (direction e.2),opposite e.2)

def matingSegment (es : List NativeSide) : List NativeSide := es.reverse.map acrossSide

def frameSegment (n : FrameInfo) (s : Fin 6) : List NativeSide :=
  placedSegment n.kind n.anchor n.turn s

def adjustedDirection (n : FrameInfo) (s : Fin 6) : Fin 6 := rotateTurn n.turn s

def FrameGeometry (k : TileKind) (ns : List Position) (frames : List FrameInfo) : Prop :=
  frames.length = 6 ∧ frames.map FrameInfo.anchor = ns ∧
  (∀ s : Fin 6, inFive (frameAt frames s).anchor) ∧
  (∀ s : Fin 6,
    frameSegment (frameAt frames s) (frameAt frames s).mateSide =
      matingSegment (placedSegment k (0,0) 0 s) ∧
    macroLabel k s = -macroLabel (frameAt frames s).kind (frameAt frames s).mateSide ∧
    adjustedDirection (frameAt frames s) (frameAt frames s).mateSide = opposite s) ∧
  (∀ s : Fin 6,
    let a := frameAt frames (rotateTurn 5 s)
    let b := frameAt frames s
    frameSegment b (rotateTurn 1 b.mateSide) =
      matingSegment (frameSegment a (rotateTurn 5 a.mateSide)) ∧
    macroLabel a.kind (rotateTurn 5 a.mateSide) =
      -macroLabel b.kind (rotateTurn 1 b.mateSide) ∧
    adjustedDirection a (rotateTurn 5 a.mateSide) = rotateTurn 1 s ∧
    adjustedDirection b (rotateTurn 1 b.mateSide) = rotateTurn 4 s)
instance (k : TileKind) (ns : List Position) (frames : List FrameInfo) :
    Decidable (FrameGeometry k ns frames) := inferInstanceAs (Decidable (_ ∧ _))

def FrameRows (f : Position → State) (frames : List FrameInfo) : Prop :=
  ∀ s : Fin 6,
    f (frameAt frames s).anchor = (0,(frameAt frames s).turn) ∧
    matchingKinds f (frameAt frames s).anchor (frameAt frames s).turn = [(frameAt frames s).kind]
instance (f : Position → State) (frames : List FrameInfo) : Decidable (FrameRows f frames) :=
  inferInstanceAs (Decidable (∀ s : Fin 6, _ ∧ _))

def FramedRootStructure (f : Position → State) : Prop :=
  ∃ k : TileKind, ∃ ns : List Position, ∃ frames : List FrameInfo,
    rootParent f = childPatch k ∧ Structure (owners f) k ns ∧
      FrameGeometry k ns frames ∧ FrameRows f frames

#print axioms inFive_iff
#print axioms mem_matchingKinds_iff
end SpectreFinite.HexSearch.ParentBoundary
