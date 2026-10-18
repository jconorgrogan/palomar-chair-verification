module

public import SpectreClusters.StageDFinalModel

@[expose] public section


/-! Exact compatibility of literal cluster frames and marked axial directions. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch

theorem turnDiff_compose : ∀ d r s : Turn,
    turnDiff d (turnAdd r s) = turnDiff (turnDiff d r) s := by decide

theorem turnDiff_opposite : ∀ d r : Turn,
    turnDiff (opposite d) r = opposite (turnDiff d r) := by decide

theorem turnDiff_rotate : ∀ a d r : Turn,
    turnDiff (rotateTurn a d) r = rotateTurn a (turnDiff d r) := by decide

theorem turnAdd_diff : ∀ d r : Turn, turnAdd r (turnDiff d r) = d := by decide

theorem turnDiff_turnAdd : ∀ d r : Turn, turnDiff (turnAdd r d) r = d := by decide

theorem sideMatch_rotated (a b : State) (r d : Turn)
    (h : ReverseExistence.sideMatch a b d) :
    ReverseExistence.sideMatch (rotateState r a) (rotateState r b) (rotateTurn r d) := by
  have h1 := facingMark_rotate r ((0,0),a) d
  have h2 := facingMark_rotate r ((0,0),b) (opposite d)
  change facingMark (placed ((0,0),rotateState r a)) (rotateTurn r d) = _ at h1
  change facingMark (placed ((0,0),rotateState r b)) (rotateTurn r (opposite d)) = _ at h2
  unfold ReverseExistence.sideMatch at *
  rw [←rotateTurn_opposite,h1,h2]
  exact h

theorem sideMatch_in_frame (a b : Fin 9) (r s d : Turn)
    (h : ReverseExistence.sideMatch (a,0) (b,s) (turnDiff d r)) :
    ReverseExistence.sideMatch (a,r) (b,turnAdd r s) d := by
  have hm := sideMatch_rotated (a,0) (b,s) r (turnDiff d r) h
  have hz : ∀ k : Turn, rotateTurn k 0 = k := by decide
  simp only [rotateState,hz,show rotateTurn r (turnDiff d r) = d from turnAdd_diff d r] at hm
  simpa only [rotateTurn,turnAdd] using hm

end SpectreClusters.StageD
