module

public import SpectreFinite.TaggedHexPortFrames
public import SpectreFinite.ForwardTrianglePortDefinitions

@[expose] public section


namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

theorem localDirection_rotate (u a d : Fin 6) :
    localDirection u (rotateTurn a d) = rotateTurn a (localDirection u d) := by
  revert u a d
  decide

theorem seamLocal_direction (u v s d : Fin 6) :
    seamLocal s (macroSide v (opposite (macroSide u s))) (localDirection u d) =
      localDirection v d := by
  revert u v s d
  decide

theorem macroSide_next (u s : Fin 6) :
    macroSide u (rotateTurn 1 s) = rotateTurn 5 (macroSide u s) := by
  revert u s
  decide

theorem macroSide_triangle_left (u v s : Fin 6) :
    macroSide v (rotateTurn 5 (macroSide v (opposite (macroSide u s)))) =
      rotateTurn 4 (macroSide u s) := by
  revert u v s
  decide

theorem macroSide_triangle_right (u v w s : Fin 6) :
    macroSide w (opposite (macroSide v
      (rotateTurn 5 (macroSide v (opposite (macroSide u s)))))) =
      rotateTurn 1 (macroSide w (opposite (macroSide u (rotateTurn 1 s)))) := by
  revert u v w s
  decide

theorem reversed_triangle (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (p q r : S.Cell)
    (hq : S.step d p = some q) (hr : S.step (rotateTurn 5 d) p = some r) :
    S.step (rotateTurn 4 d) q = some r := by
  have h1 : rotateTurn 1 (rotateTurn 5 d) = d :=
    (by decide : ∀ a : Fin 6, rotateTurn 1 (rotateTurn 5 a) = a) d
  have h2 : opposite (rotateTurn 2 (rotateTurn 5 d)) = rotateTurn 4 d :=
    (by decide : ∀ a : Fin 6, opposite (rotateTurn 2 (rotateTurn 5 a)) = rotateTurn 4 a) d
  have hq' : S.step (rotateTurn 1 (rotateTurn 5 d)) p = some q := by rw [h1]; exact hq
  have h := hs.triangle (rotateTurn 5 d) p r q hr hq'
  have h' := hs.opposite_inverse _ _ _ h
  simpa only [h2] using h'

theorem taggedStep_internal_eq (S : PartialMarkedHexSystem) (x y : ChildTag S)
    (d : Fin 6) (j : Fin 8)
    (ha : portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 d) = .internal j)
    (hp : y.parent = x.parent) (hi : S.childFin8 y = j) :
    S.taggedStep d x = some y := by
  simp only [taggedStep,ha]
  exact (S.tagAt_eq_some_iff _ _ _).mpr ⟨hp,hi⟩

theorem taggedStep_external_eq (S : PartialMarkedHexSystem) (x y : ChildTag S)
    (d s n : Fin 6) (q : S.Cell)
    (ha : portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 d) = .external s n)
    (hq : S.step (macroSide (S.label x.parent).2 s) x.parent = some q)
    (hp : y.parent = q)
    (hi : S.childFin8 y =
      (matingPort (S.label q).1
        (macroSide (S.label q).2 (opposite (macroSide (S.label x.parent).2 s))) n).1) :
    S.taggedStep d x = some y := by
  simp only [taggedStep,ha,hq,Option.bind_some]
  exact (S.tagAt_eq_some_iff _ _ _).mpr ⟨hp,hi⟩

end SpectreFinite.HexSearch.PartialMarkedHexSystem
