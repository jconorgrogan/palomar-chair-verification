module

public import SpectreFinite.TaggedHexRefinement

@[expose] public section


/-! Exact frame and tag identities used by forward-substitution law
preservation. All turn identities are finite kernel decisions. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

theorem childFin8_bound (S : PartialMarkedHexSystem) (x : ChildTag S) :
    (S.childFin8 x).val < (children (S.label x.parent).1).length := x.child.isLt

theorem tagAt_eq_some_iff (S : PartialMarkedHexSystem) (p : S.Cell)
    (i : Fin 8) (y : ChildTag S) :
    S.tagAt p i = some y ↔ y.parent = p ∧ S.childFin8 y = i := by
  constructor
  · intro h
    unfold tagAt at h
    split at h
    next hi =>
      have he : (⟨p,⟨i.val,hi⟩⟩ : ChildTag S) = y := Option.some.inj h
      cases he
      exact ⟨rfl,Fin.ext rfl⟩
    next hi => contradiction
  · rintro ⟨hp,hi⟩
    have h := S.tagAt_childFin8 y
    rw [hp,hi] at h
    exact h

theorem childAt_childFin8 (S : PartialMarkedHexSystem) (x : ChildTag S) :
    childAt (S.label x.parent).1 (S.childFin8 x) = S.childHex x := by
  simp [childAt,childFin8,childHex,List.getD_eq_getElem?_getD,x.child.isLt]

theorem childLabel_mark (S : PartialMarkedHexSystem) (x : ChildTag S) (d : Fin 6) :
    facingMark (placed ((0,0),S.childLabel x)) d =
      facingMark (childAt (S.label x.parent).1 (S.childFin8 x))
        (localDirection (S.label x.parent).2 d) := by
  rw [S.childAt_childFin8 x]
  have h := facingMark_rotate (inverseTurn (S.label x.parent).2)
    ((0,0),((S.childHex x).kind,(S.childHex x).turn))
    (localDirection (S.label x.parent).2 d)
  rw [localDirection,rotateTurn_inverse] at h
  exact h

theorem localDirection_opposite (u d : Fin 6) :
    localDirection u (opposite d) = opposite (localDirection u d) :=
  rotateTurn_opposite u d

theorem opposite_opposite_port (d : Fin 6) : opposite (opposite d) = d := by
  revert d; decide

theorem seam_localDirection (u v s d f : Fin 6)
    (h : rotateTurn (seamTurn s (macroSide v (opposite (macroSide u s)))) f =
      opposite (localDirection u d)) :
    f = localDirection v (opposite d) := by
  revert u v s d f
  decide

theorem macroSide_return (u v s : Fin 6) :
    macroSide u (opposite (macroSide v
      (macroSide v (opposite (macroSide u s))))) = s := by
  rw [macroSide_involutive,opposite_opposite_port,macroSide_involutive]

end SpectreFinite.HexSearch.PartialMarkedHexSystem
