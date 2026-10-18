module

public import SpectreFinite.TaggedHexCells
public import SpectreFinite.ForwardPortActions
public import SpectreFinite.ReflectedMacroLabels

@[expose] public section


/-! Literal tagged forward substitution. Internal ports come from exact child
adjacency; external ports cross the parent's actual port and select the
reversed matching macro-segment entry. All missing ports are computed. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

/-- The reflection converts a parent world direction to a native macro-side.
The same involution converts a native macro-side back to a world direction. -/
def macroSide (turn d : Fin 6) : Fin 6 := rotateTurn turn (inverseTurn d)

def localDirection (turn d : Fin 6) : Fin 6 := rotateTurn turn d

def childFin8 (S : PartialMarkedHexSystem) (x : ChildTag S) : Fin 8 :=
  ⟨x.child.val, Nat.lt_of_lt_of_le x.child.isLt (supertile_area_bounds _).2⟩

def tagAt (S : PartialMarkedHexSystem) (p : S.Cell) (i : Fin 8) : Option (ChildTag S) :=
  if h : i.val < (children (S.label p).1).length then some ⟨p,⟨i.val,h⟩⟩ else none

/-- A total executable definition on arbitrary finite input systems; legality
is a theorem to be proved from the actual finite routing laws. -/
def taggedStep (S : PartialMarkedHexSystem) (d : Fin 6) (x : ChildTag S) :
    Option (ChildTag S) :=
  let u := (S.label x.parent).2
  match portAction (S.label x.parent).1 (S.childFin8 x) (localDirection u d) with
  | .internal j => S.tagAt x.parent j
  | .external s n =>
      let D := macroSide u s
      (S.step D x.parent).bind fun q =>
        let t := macroSide (S.label q).2 (opposite D)
        S.tagAt q (matingPort (S.label q).1 t n).1

def refine (S : PartialMarkedHexSystem) : PartialMarkedHexSystem where
  cellCount := S.childTags.length
  label := fun i => S.childLabel (S.decodeChild i)
  step := fun d i => (S.taggedStep d (S.decodeChild i)).map S.encodeChild

@[simp] theorem refine_cellCount (S : PartialMarkedHexSystem) :
    S.refine.cellCount = S.childTags.length := rfl

theorem refine_cellCount_bounds (S : PartialMarkedHexSystem) :
    7*S.cellCount ≤ S.refine.cellCount ∧ S.refine.cellCount ≤ 8*S.cellCount :=
  S.childTags_growth

@[simp] theorem refine_label_encode (S : PartialMarkedHexSystem) (x : ChildTag S) :
    S.refine.label (S.encodeChild x) = S.childLabel x := by simp [refine]

@[simp] theorem refine_step_encode (S : PartialMarkedHexSystem) (x : ChildTag S) (d : Fin 6) :
    S.refine.step d (S.encodeChild x) = (S.taggedStep d x).map S.encodeChild := by
  simp [refine]

@[simp] theorem macroSide_involutive (u d : Fin 6) :
    macroSide u (macroSide u d) = d := by revert u d; decide

theorem macroSide_mark (k : TileKind) (u d : Fin 6) :
    macroLabel k (macroSide u d) = facingMark (placed ((0,0),(k,u))) d := by
  revert k u d
  decide

@[simp] theorem tagAt_isSome (S : PartialMarkedHexSystem) (p : S.Cell) (i : Fin 8) :
    (S.tagAt p i).isSome ↔ i.val < (children (S.label p).1).length := by
  simp [tagAt]

@[simp] theorem tagAt_childFin8 (S : PartialMarkedHexSystem) (x : ChildTag S) :
    S.tagAt x.parent (S.childFin8 x) = some x := by
  rcases x with ⟨p,i⟩
  simp [tagAt, childFin8, i.isLt]

/-- Iteration is already defined from the literal one-cell seed, independently
of any claimed local-law or boundary-growth preservation theorem. -/
def iterateRefinement (s : State) : Nat → PartialMarkedHexSystem
  | 0 => singleton s
  | n+1 => (iterateRefinement s n).refine

theorem iterateRefinement_area (s : State) (n : Nat) :
    7^n ≤ (iterateRefinement s n).cellCount := by
  induction n with
  | zero => simp [iterateRefinement, singleton]
  | succ n ih =>
      have h := (iterateRefinement s n).refine_cellCount_bounds.1
      change 7^(n+1) ≤ (iterateRefinement s n).refine.cellCount
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans (Nat.mul_le_mul_left 7 ih) h

end SpectreFinite.HexSearch.PartialMarkedHexSystem
