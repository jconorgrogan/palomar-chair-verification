module

public import SpectreFinite.BoundaryWords
public import SpectreFinite.HexRotationComposition

@[expose] public section


/-! Exact reflection convention needed to read a parent field as another
field in the original nine-marked-hexagon alphabet. This supplies label and
coordinate identities, not a coarse-coordinate existence theorem. -/
namespace SpectreFinite.HexSearch
open Boundary

def reflectPosition (x : Position) : Position := (x.1+x.2,-x.2)

theorem reflectPosition_involutive (x : Position) :
    reflectPosition (reflectPosition x) = x := by
  apply Prod.ext <;> simp only [reflectPosition] <;> omega

theorem reflectPosition_add (x y : Position) :
    reflectPosition (addPos x y) = addPos (reflectPosition x) (reflectPosition y) := by
  apply Prod.ext <;> simp only [reflectPosition,addPos] <;> omega

theorem reflectPosition_direction : ∀ d : Fin 6,
    reflectPosition (direction d) = direction (inverseTurn d) := by decide

theorem inverseTurn_opposite : ∀ d : Fin 6,
    inverseTurn (opposite d) = opposite (inverseTurn d) := by decide

/-- A parent Gamma turn `t` becomes turn `-t` after reflecting coarse
coordinates. Omitting this reflection would use the wrong edge alphabet. -/
theorem reflected_macro_facing : ∀ (k : TileKind) (t d : Fin 6),
    macroLabel k (rotateTurn (inverseTurn t) (inverseTurn d)) =
      facingMark (placed ((0,0),(k,inverseTurn t))) d := by decide

theorem reflected_macro_matching (k l : TileKind) (t u d : Fin 6)
    (hm : macroLabel k (rotateTurn (inverseTurn t) (inverseTurn d)) =
      -macroLabel l (rotateTurn (inverseTurn u) (inverseTurn (opposite d)))) :
    facingMark (placed ((0,0),(k,inverseTurn t))) d =
      -facingMark (placed ((0,0),(l,inverseTurn u))) (opposite d) := by
  simpa only [reflected_macro_facing] using hm

end SpectreFinite.HexSearch
