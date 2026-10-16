module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! A literal polynomial edge replacement. No physical tiling conclusion is
asserted. The slope expression below is algebraic; analytic differentiability
and the assembled body's geometry are separate obligations. -/
namespace LiteralPlanar.Quintic
noncomputable section

/-- Signed height over a unit segment centered at the origin. -/
def height (ε t : ℝ) : ℝ := ε * t * (t ^ 2 - 1 / 4) ^ 2

def arc (ε t : ℝ) : ℝ × ℝ := (t, height ε t)

def slope (ε t : ℝ) : ℝ := ε * (5 * t ^ 4 - 3 / 2 * t ^ 2 + 1 / 16)

def amplitude : ℝ := 1 / 1024

theorem amplitude_pos : 0 < amplitude := by norm_num [amplitude]

theorem height_expanded (ε t : ℝ) :
    height ε t = ε * (t ^ 5 - 1 / 2 * t ^ 3 + 1 / 16 * t) := by
  unfold height
  ring

theorem height_neg (ε t : ℝ) : height ε (-t) = -height ε t := by
  unfold height
  ring

theorem arc_halfturn (ε t : ℝ) : arc ε (-t) = -(arc ε t) := by
  apply Prod.ext
  · rfl
  · exact height_neg ε t

theorem arc_injective (ε : ℝ) : Function.Injective (arc ε) := by
  intro t u h
  exact congrArg Prod.fst h

@[simp] theorem height_left (ε : ℝ) : height ε (-1 / 2) = 0 := by
  norm_num [height]
@[simp] theorem height_right (ε : ℝ) : height ε (1 / 2) = 0 := by
  norm_num [height]
@[simp] theorem slope_left (ε : ℝ) : slope ε (-1 / 2) = 0 := by
  norm_num [slope]
@[simp] theorem slope_right (ε : ℝ) : slope ε (1 / 2) = 0 := by
  norm_num [slope]

/-- The edge formula is polynomial in barycentric coordinates on a fan triangle.
It vanishes on both radial sides, so these local displacements can be pasted. -/
def fanHeight (ε α β : ℝ) : ℝ := ε / 2 * (β - α) * α ^ 2 * β ^ 2

theorem fanHeight_edge (ε α β : ℝ) (h : α + β = 1) :
    fanHeight ε α β = height ε (β - 1 / 2) := by
  have ha : α = 1 - β := by linarith
  rw [ha]
  unfold fanHeight height
  ring

@[simp] theorem fanHeight_radial_left (ε β : ℝ) : fanHeight ε 0 β = 0 := by
  simp [fanHeight]
@[simp] theorem fanHeight_radial_right (ε α : ℝ) : fanHeight ε α 0 = 0 := by
  simp [fanHeight]

end
end LiteralPlanar.Quintic
