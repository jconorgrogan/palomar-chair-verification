module

public import SpectreGeometry.ReverseLocalStarFastData
public import SpectreClusters.GridMotions

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch

set_option maxRecDepth 100000

theorem sideTurn_covariant : ∀ r t d : Fin 6,
    sideTurn (rotateTurn r t) (rotateTurn r d) = sideTurn t d := by decide

theorem sideTurn_eq_inverse : ∀ r d : Fin 6,
    sideTurn r d = rotateTurn (inverseTurn r) d := by decide

theorem rotateTurn_zero_right : ∀ r : Fin 6, rotateTurn r 0 = r := by decide

theorem facingMark_state_rotate (r : Fin 6) (a : State) (d : Fin 6) :
    facingMark (placed ((0,0),rotateState r a)) (rotateTurn r d) =
      facingMark (placed ((0,0),a)) d := by
  simpa only [facingMark,placed,rotateEntry,rotateState] using
    facingMark_rotate r ((0,0),a) d

theorem sideMatch_rotate (r : Fin 6) (a b : State) (d : Fin 6)
    (h : sideMatch a b d) :
    sideMatch (rotateState r a) (rotateState r b) (rotateTurn r d) := by
  unfold sideMatch at *
  rw [facingMark_state_rotate,←rotateTurn_opposite,facingMark_state_rotate]
  exact h

theorem stateBoundaryIds_rotate (r : Fin 6) (a : State) (d : Fin 6) :
    stateBoundaryIds (rotateState r a) (rotateTurn r d) = stateBoundaryIds a d := by
  simp only [stateBoundaryIds,rotateState,sideTurn_covariant]

theorem localStar_rotate (r : Fin 6) (a : State) (v : Nat) :
    localStar (rotateState r a) v =
      (localStar a v).map (fun t => t.map (SpectreClusters.rotate r)) := by
  simp only [localStar,rotateState,List.map_map,Function.comp_apply]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply,List.map_map]
  apply List.map_congr_left
  intro p hp
  exact (rotate_compose r a.2 _).symm

theorem fastLocalStar_rotate (r : Fin 6) (a : State) (v : Nat) :
    fastLocalStar (rotateState r a) v =
      (fastLocalStar a v).map (fun t => t.map (SpectreClusters.rotate r)) := by
  simp only [fastLocalStar,rotateState,List.map_map,Function.comp_apply]
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply,List.map_map]
  apply List.map_congr_left
  intro p hp
  exact (rotate_compose r a.2 p).symm

theorem state_normalized (a : State) :
    rotateState (inverseTurn a.2) a = (a.1,0) := by
  apply Prod.ext
  · rfl
  · change rotateTurn (inverseTurn a.2) a.2 = 0
    have h : ∀ r : Fin 6, rotateTurn (inverseTurn r) r = 0 := by decide
    exact h a.2

end SpectreGeometry.ReverseLocalStarOccurrences
