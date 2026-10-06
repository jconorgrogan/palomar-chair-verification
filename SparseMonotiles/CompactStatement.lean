module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.Isometry
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Exact S54 sparse-key bodies: independent statement draft

Definition-only copy of the independent main Challenge, for Solution bindings.
The separate Challenge contains two deliberately unfinished theorem statements.
No unfinished theorem or missing definition is imported into this module.

Only Lean core and Mathlib are imported. Each placement is an explicit tuple
(cell mask, normal axis, positive outward side, signed tangential labels, bump).
The cell mask is ordinary binary: coordinate i is its ith least significant bit.
Tangential coordinates are the remaining axes in increasing order. A signed
label ±j means the jth reference coordinate with the indicated sign, 1-based.
Thus these are geometric placement tables, not a hash or an opaque data blob.
The 256 / 1024 records preserve the order in the exact pinned S54 inputs.
-/
namespace PalomarMonotiles

/-- Euclidean d-space with its usual inner-product metric. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A reference-pyramid placement on one exposed binary-chair unit facet. -/
structure Placement (k : ℕ) where
  cellMask : ℕ
  axis : Fin (k + 1)
  positiveSide : Bool
  labels : Fin k → ℤ
  bump : Bool

/-- The ordered tangential coordinate of a world axis different from the normal. -/
def tangentIndex {k : ℕ} (a i : Fin (k + 1)) (h : i ≠ a) : Fin k :=
  if hi : i.val < a.val then ⟨i.val, by omega⟩ else ⟨i.val - 1, by
    have hn : i.val ≠ a.val := fun he => h (Fin.ext he)
    omega⟩

/-- Binary coordinate of the explicitly listed carrier cell. -/
def cellBit {k : ℕ} (p : Placement k) (i : Fin (k + 1)) : ℚ :=
  ((p.cellMask / 2 ^ i.val) % 2 : ℕ)

/-- Exact rational centre, half-widths, apex, and addition/removal bit. -/
structure Key (d : ℕ) where
  centre : Fin d → ℚ
  radius : Fin d → ℚ
  apex : Fin d → ℚ
  bump : Bool

/-- The facet centre plus the signed labels divided by 4d. -/
def placementCentre {k : ℕ} (p : Placement k) (i : Fin (k + 1)) : ℚ :=
  if h : i = p.axis then cellBit p i + (if p.positiveSide then 1 else 0)
  else cellBit p i + 1 / 2 + (p.labels (tangentIndex p.axis i h) : ℚ) / (4 * (k + 1))

/-- Place the rational reference pyramid. Width/offset functions are indexed
from zero; all table labels have absolute values between 1 and k. -/
def placedKey {k : ℕ} (w o : ℕ → ℚ) (p : Placement k) : Key (k + 1) where
  centre := placementCentre p
  radius := fun i => if h : i = p.axis then 0 else
    w ((p.labels (tangentIndex p.axis i h)).natAbs - 1)
  apex := fun i => if h : i = p.axis then placementCentre p i +
      (if p.positiveSide then 1 else -1) * (if p.bump then 1 else -1) / (48 * (k + 1))
    else let z := p.labels (tangentIndex p.axis i h)
      placementCentre p i + (if z < 0 then -1 else 1) * o (z.natAbs - 1)
  bump := p.bump

/-- The four exact T5 reference half-widths; other indices are unused. -/
def widths5 : ℕ → ℚ | 0 => 1/80 | 1 => 1/64 | 2 => 3/160 | 3 => 7/320 | _ => 0
/-- The four exact T5 tangential apex offsets. -/
def offsets5 : ℕ → ℚ | 0 => 1/240 | 1 => 1/256 | 2 => 3/800 | 3 => 7/1920 | _ => 0
/-- The six exact T7 reference half-widths; other indices are unused. -/
def widths7 : ℕ → ℚ
  | 0 => 1/112 | 1 => 1/96 | 2 => 1/84 | 3 => 3/224 | 4 => 5/336 | 5 => 11/672 | _ => 0
/-- The six exact T7 tangential apex offsets. -/
def offsets7 : ℕ → ℚ
  | 0 => 1/336 | 1 => 1/384 | 2 => 1/420 | 3 => 1/448 | 4 => 5/2352 | 5 => 11/5376 | _ => 0

/-- Consecutive explicit T5 placements 0 through 63. -/
def placements5_0 : List (Placement 4) := [
  ⟨0, 0, false, ![-4, -1, -2, -3], true⟩, ⟨0, 0, false, ![-3, -2, -1, -4], true⟩,
  ⟨0, 0, false, ![-2, -4, -3, -1], false⟩, ⟨0, 0, false, ![-1, -3, -4, -2], false⟩,
  ⟨0, 1, false, ![3, -4, -1, 2], true⟩, ⟨0, 2, false, ![3, -1, 2, -4], false⟩,
  ⟨0, 3, false, ![3, -4, 2, -1], false⟩, ⟨0, 4, false, ![3, 2, -1, -4], true⟩,
  ⟨16, 0, false, ![-4, -1, 2, -3], false⟩, ⟨16, 1, false, ![-1, 2, -4, -3], true⟩,
  ⟨16, 2, false, ![-4, 2, -1, -3], true⟩, ⟨16, 3, false, ![2, -1, -4, -3], false⟩,
  ⟨16, 4, true, ![-4, -1, -2, -3], false⟩, ⟨16, 4, true, ![-3, -2, -1, -4], false⟩,
  ⟨16, 4, true, ![-2, -4, -3, -1], true⟩, ⟨16, 4, true, ![-1, -3, -4, -2], true⟩,
  ⟨8, 0, false, ![2, -4, -3, -1], true⟩, ⟨8, 1, false, ![2, -1, -3, -4], true⟩,
  ⟨8, 2, false, ![-1, -4, -3, 2], false⟩, ⟨8, 3, true, ![-4, -3, -1, -2], true⟩,
  ⟨8, 3, true, ![-3, -4, -2, -1], true⟩, ⟨8, 3, true, ![-2, -1, -4, -3], false⟩,
  ⟨8, 3, true, ![-1, -2, -3, -4], false⟩, ⟨8, 4, false, ![-4, -1, 2, -3], false⟩,
  ⟨24, 0, false, ![3, 2, 1, 4], true⟩, ⟨24, 1, false, ![-4, -3, 2, 1], true⟩,
  ⟨24, 1, false, ![-3, -4, 1, 2], true⟩, ⟨24, 1, false, ![-2, -1, 3, 4], false⟩,
  ⟨24, 1, false, ![-1, -2, 4, 3], false⟩, ⟨24, 2, false, ![2, 3, 4, 1], true⟩,
  ⟨24, 3, true, ![-4, 3, -1, -2], false⟩, ⟨24, 4, true, ![-1, 3, -4, -2], false⟩,
  ⟨4, 0, false, ![-1, -3, -4, 2], true⟩, ⟨4, 1, false, ![-4, -3, 2, -1], false⟩,
  ⟨4, 2, true, ![-4, -2, -1, -3], true⟩, ⟨4, 2, true, ![-3, -1, -2, -4], true⟩,
  ⟨4, 2, true, ![-2, -3, -4, -1], false⟩, ⟨4, 2, true, ![-1, -4, -3, -2], false⟩,
  ⟨4, 3, false, ![-1, 2, -3, -4], false⟩, ⟨4, 4, false, ![2, -4, -3, -1], true⟩,
  ⟨20, 0, false, ![2, 4, 3, 1], false⟩, ⟨20, 1, false, ![2, 1, 3, 4], false⟩,
  ⟨20, 2, true, ![-1, -4, 3, -2], true⟩, ⟨20, 3, false, ![-4, -3, 1, 2], false⟩,
  ⟨20, 3, false, ![-3, -4, 2, 1], false⟩, ⟨20, 3, false, ![-2, -1, 4, 3], true⟩,
  ⟨20, 3, false, ![-1, -2, 3, 4], true⟩, ⟨20, 4, true, ![-4, -1, -2, 3], true⟩,
  ⟨12, 0, false, ![-4, 1, 2, -3], true⟩, ⟨12, 0, false, ![-3, 2, 1, -4], true⟩,
  ⟨12, 0, false, ![-2, 4, 3, -1], false⟩, ⟨12, 0, false, ![-1, 3, 4, -2], false⟩,
  ⟨12, 1, false, ![3, 4, 1, 2], true⟩, ⟨12, 2, true, ![3, -1, -2, -4], false⟩,
  ⟨12, 3, true, ![3, -4, -2, -1], false⟩, ⟨12, 4, false, ![3, 2, 1, 4], true⟩,
  ⟨28, 0, false, ![2, 4, -3, 1], true⟩, ⟨28, 1, false, ![2, 1, -3, 4], true⟩,
  ⟨28, 2, true, ![-1, -4, -3, -2], false⟩, ⟨28, 3, true, ![-4, -3, 1, 2], true⟩,
  ⟨28, 3, true, ![-3, -4, 2, 1], true⟩, ⟨28, 3, true, ![-2, -1, 4, 3], false⟩,
  ⟨28, 3, true, ![-1, -2, 3, 4], false⟩, ⟨28, 4, true, ![-4, -1, -2, -3], false⟩
]
/-- Consecutive explicit T5 placements 64 through 127. -/
def placements5_1 : List (Placement 4) := [
  ⟨2, 0, false, ![-3, 2, -1, -4], false⟩, ⟨2, 1, true, ![-4, -3, -2, -1], false⟩,
  ⟨2, 1, true, ![-3, -4, -1, -2], false⟩, ⟨2, 1, true, ![-2, -1, -3, -4], true⟩,
  ⟨2, 1, true, ![-1, -2, -4, -3], true⟩, ⟨2, 2, false, ![2, -3, -4, -1], false⟩,
  ⟨2, 3, false, ![-4, -3, -1, 2], true⟩, ⟨2, 4, false, ![-1, -3, -4, 2], true⟩,
  ⟨18, 0, false, ![1, -3, -4, 2], false⟩, ⟨18, 0, false, ![2, -4, -3, 1], false⟩,
  ⟨18, 0, false, ![3, -2, -1, 4], true⟩, ⟨18, 0, false, ![4, -1, -2, 3], true⟩,
  ⟨18, 1, true, ![3, -4, -1, -2], true⟩, ⟨18, 2, false, ![3, 1, 2, 4], false⟩,
  ⟨18, 3, false, ![3, 4, 2, 1], false⟩, ⟨18, 4, true, ![3, -2, -1, -4], true⟩,
  ⟨10, 0, false, ![1, 3, 4, 2], false⟩, ⟨10, 1, true, ![-4, 3, -2, -1], true⟩,
  ⟨10, 2, false, ![-4, 2, 1, -3], false⟩, ⟨10, 2, false, ![-3, 1, 2, -4], false⟩,
  ⟨10, 2, false, ![-2, 3, 4, -1], true⟩, ⟨10, 2, false, ![-1, 4, 3, -2], true⟩,
  ⟨10, 3, true, ![-1, -2, 3, -4], true⟩, ⟨10, 4, false, ![2, 4, 3, 1], false⟩,
  ⟨26, 0, false, ![-3, 2, 1, 4], false⟩, ⟨26, 1, true, ![-4, -3, 2, 1], false⟩,
  ⟨26, 1, true, ![-3, -4, 1, 2], false⟩, ⟨26, 1, true, ![-2, -1, 3, 4], true⟩,
  ⟨26, 1, true, ![-1, -2, 4, 3], true⟩, ⟨26, 2, false, ![2, -3, 4, 1], false⟩,
  ⟨26, 3, true, ![-4, -3, -1, -2], true⟩, ⟨26, 4, true, ![-1, -3, -4, -2], true⟩,
  ⟨6, 0, false, ![4, 1, 2, 3], true⟩, ⟨6, 1, true, ![-1, -2, -4, 3], false⟩,
  ⟨6, 2, true, ![-4, -2, -1, 3], false⟩, ⟨6, 3, false, ![2, 1, 4, 3], true⟩,
  ⟨6, 4, false, ![-4, 1, 2, -3], true⟩, ⟨6, 4, false, ![-3, 2, 1, -4], true⟩,
  ⟨6, 4, false, ![-2, 4, 3, -1], false⟩, ⟨6, 4, false, ![-1, 3, 4, -2], false⟩,
  ⟨22, 0, false, ![4, 1, 2, -3], false⟩, ⟨22, 1, true, ![-1, -2, -4, -3], true⟩,
  ⟨22, 2, true, ![-4, -2, -1, -3], true⟩, ⟨22, 3, false, ![2, 1, 4, -3], false⟩,
  ⟨22, 4, true, ![-4, 1, 2, -3], false⟩, ⟨22, 4, true, ![-3, 2, 1, -4], false⟩,
  ⟨22, 4, true, ![-2, 4, 3, -1], true⟩, ⟨22, 4, true, ![-1, 3, 4, -2], true⟩,
  ⟨14, 0, false, ![1, -3, 4, 2], true⟩, ⟨14, 1, true, ![-4, -3, -2, -1], false⟩,
  ⟨14, 2, true, ![-4, 2, 1, -3], true⟩, ⟨14, 2, true, ![-3, 1, 2, -4], true⟩,
  ⟨14, 2, true, ![-2, 3, 4, -1], false⟩, ⟨14, 2, true, ![-1, 4, 3, -2], false⟩,
  ⟨14, 3, true, ![-1, -2, -3, -4], false⟩, ⟨14, 4, false, ![2, 4, -3, 1], true⟩,
  ⟨30, 0, false, ![1, 3, 4, 2], false⟩, ⟨30, 0, false, ![2, 4, 3, 1], false⟩,
  ⟨30, 0, false, ![3, 2, 1, 4], true⟩, ⟨30, 0, false, ![4, 1, 2, 3], true⟩,
  ⟨30, 0, true, ![-4, -1, -2, -3], false⟩, ⟨30, 0, true, ![-3, -2, -1, -4], false⟩,
  ⟨30, 0, true, ![-2, -4, -3, -1], true⟩, ⟨30, 0, true, ![-1, -3, -4, -2], true⟩
]
/-- Consecutive explicit T5 placements 128 through 191. -/
def placements5_2 : List (Placement 4) := [
  ⟨30, 1, true, ![3, 4, 1, -2], true⟩, ⟨30, 2, true, ![3, 1, -2, 4], false⟩,
  ⟨30, 3, true, ![3, 4, -2, 1], false⟩, ⟨30, 4, true, ![3, -2, 1, 4], true⟩,
  ⟨1, 0, true, ![-4, -1, -2, -3], false⟩, ⟨1, 0, true, ![-3, -2, -1, -4], false⟩,
  ⟨1, 0, true, ![-2, -4, -3, -1], true⟩, ⟨1, 0, true, ![-1, -3, -4, -2], true⟩,
  ⟨1, 1, false, ![-3, -4, -1, 2], false⟩, ⟨1, 2, false, ![-3, -1, 2, -4], true⟩,
  ⟨1, 3, false, ![-3, -4, 2, -1], true⟩, ⟨1, 4, false, ![-3, 2, -1, -4], false⟩,
  ⟨17, 0, true, ![-1, 3, -4, -2], false⟩, ⟨17, 1, false, ![4, 3, 2, 1], true⟩,
  ⟨17, 2, false, ![1, -4, -3, 2], true⟩, ⟨17, 2, false, ![2, -3, -4, 1], true⟩,
  ⟨17, 2, false, ![3, -1, -2, 4], false⟩, ⟨17, 2, false, ![4, -2, -1, 3], false⟩,
  ⟨17, 3, false, ![1, 2, 3, 4], true⟩, ⟨17, 4, true, ![-2, -4, 3, -1], false⟩,
  ⟨9, 0, true, ![-4, -1, -2, 3], true⟩, ⟨9, 1, false, ![1, 2, 4, 3], false⟩,
  ⟨9, 2, false, ![4, 2, 1, 3], false⟩, ⟨9, 3, true, ![-2, -1, -4, 3], true⟩,
  ⟨9, 4, false, ![1, -3, -4, 2], false⟩, ⟨9, 4, false, ![2, -4, -3, 1], false⟩,
  ⟨9, 4, false, ![3, -2, -1, 4], true⟩, ⟨9, 4, false, ![4, -1, -2, 3], true⟩,
  ⟨25, 0, true, ![-4, -1, -2, -3], false⟩, ⟨25, 1, false, ![1, 2, 4, -3], true⟩,
  ⟨25, 2, false, ![4, 2, 1, -3], true⟩, ⟨25, 3, true, ![-2, -1, -4, -3], false⟩,
  ⟨25, 4, true, ![1, -3, -4, 2], true⟩, ⟨25, 4, true, ![2, -4, -3, 1], true⟩,
  ⟨25, 4, true, ![3, -2, -1, 4], false⟩, ⟨25, 4, true, ![4, -1, -2, 3], false⟩,
  ⟨5, 0, true, ![3, -2, -1, -4], true⟩, ⟨5, 1, false, ![1, 2, -4, -3], false⟩,
  ⟨5, 1, false, ![2, 1, -3, -4], false⟩, ⟨5, 1, false, ![3, 4, -1, -2], true⟩,
  ⟨5, 1, false, ![4, 3, -2, -1], true⟩, ⟨5, 2, true, ![-2, 3, -4, -1], true⟩,
  ⟨5, 3, false, ![4, 3, 1, 2], false⟩, ⟨5, 4, false, ![1, 3, 4, 2], false⟩,
  ⟨21, 0, true, ![-1, -3, -4, -2], true⟩, ⟨21, 1, false, ![4, -3, 2, 1], false⟩,
  ⟨21, 2, true, ![1, -4, -3, 2], false⟩, ⟨21, 2, true, ![2, -3, -4, 1], false⟩,
  ⟨21, 2, true, ![3, -1, -2, 4], true⟩, ⟨21, 2, true, ![4, -2, -1, 3], true⟩,
  ⟨21, 3, false, ![1, 2, -3, 4], false⟩, ⟨21, 4, true, ![-2, -4, -3, -1], true⟩,
  ⟨13, 0, true, ![-4, 1, 2, -3], false⟩, ⟨13, 0, true, ![-3, 2, 1, -4], false⟩,
  ⟨13, 0, true, ![-2, 4, 3, -1], true⟩, ⟨13, 0, true, ![-1, 3, 4, -2], true⟩,
  ⟨13, 1, false, ![-3, 4, 1, 2], false⟩, ⟨13, 2, true, ![-3, -1, -2, -4], true⟩,
  ⟨13, 3, true, ![-3, -4, -2, -1], true⟩, ⟨13, 4, false, ![-3, 2, 1, 4], false⟩,
  ⟨29, 0, true, ![3, -2, 1, 4], true⟩, ⟨29, 1, false, ![1, 2, 4, 3], false⟩,
  ⟨29, 1, false, ![2, 1, 3, 4], false⟩, ⟨29, 1, false, ![3, 4, 1, 2], true⟩
]
/-- Consecutive explicit T5 placements 192 through 255. -/
def placements5_3 : List (Placement 4) := [
  ⟨29, 1, false, ![4, 3, 2, 1], true⟩, ⟨29, 1, true, ![3, -4, -1, 2], false⟩,
  ⟨29, 2, true, ![-2, 3, 4, 1], true⟩, ⟨29, 3, true, ![4, 3, 1, -2], false⟩,
  ⟨29, 4, true, ![1, 3, 4, -2], false⟩, ⟨3, 0, true, ![-2, -4, 3, -1], false⟩,
  ⟨3, 1, true, ![-2, -1, 3, -4], false⟩, ⟨3, 2, false, ![1, 4, 3, 2], true⟩,
  ⟨3, 3, false, ![1, 2, -3, -4], true⟩, ⟨3, 3, false, ![2, 1, -4, -3], true⟩,
  ⟨3, 3, false, ![3, 4, -2, -1], false⟩, ⟨3, 3, false, ![4, 3, -1, -2], false⟩,
  ⟨3, 4, false, ![4, 1, 2, 3], true⟩, ⟨19, 0, true, ![1, -3, -4, 2], true⟩,
  ⟨19, 0, true, ![2, -4, -3, 1], true⟩, ⟨19, 0, true, ![3, -2, -1, 4], false⟩,
  ⟨19, 0, true, ![4, -1, -2, 3], false⟩, ⟨19, 1, true, ![-3, -4, -1, -2], false⟩,
  ⟨19, 2, false, ![-3, 1, 2, 4], true⟩, ⟨19, 3, false, ![-3, 4, 2, 1], true⟩,
  ⟨19, 4, true, ![-3, -2, -1, -4], false⟩, ⟨11, 0, true, ![-2, -4, -3, -1], true⟩,
  ⟨11, 1, true, ![-2, -1, -3, -4], true⟩, ⟨11, 2, false, ![1, 4, -3, 2], false⟩,
  ⟨11, 3, true, ![1, 2, -3, -4], false⟩, ⟨11, 3, true, ![2, 1, -4, -3], false⟩,
  ⟨11, 3, true, ![3, 4, -2, -1], true⟩, ⟨11, 3, true, ![4, 3, -1, -2], true⟩,
  ⟨11, 4, false, ![4, 1, 2, -3], false⟩, ⟨27, 0, true, ![1, 3, 4, -2], false⟩,
  ⟨27, 1, true, ![4, 3, -2, 1], true⟩, ⟨27, 2, false, ![1, 4, 3, 2], true⟩,
  ⟨27, 2, false, ![2, 3, 4, 1], true⟩, ⟨27, 2, false, ![3, 1, 2, 4], false⟩,
  ⟨27, 2, false, ![4, 2, 1, 3], false⟩, ⟨27, 2, true, ![3, -1, 2, -4], true⟩,
  ⟨27, 3, true, ![1, -2, 3, 4], true⟩, ⟨27, 4, true, ![-2, 4, 3, 1], false⟩,
  ⟨7, 0, true, ![-3, -2, -1, -4], false⟩, ⟨7, 1, true, ![1, 2, -4, -3], true⟩,
  ⟨7, 1, true, ![2, 1, -3, -4], true⟩, ⟨7, 1, true, ![3, 4, -1, -2], false⟩,
  ⟨7, 1, true, ![4, 3, -2, -1], false⟩, ⟨7, 2, true, ![-2, -3, -4, -1], false⟩,
  ⟨7, 3, false, ![4, -3, 1, 2], true⟩, ⟨7, 4, false, ![1, -3, 4, 2], true⟩,
  ⟨23, 0, true, ![-2, 4, 3, 1], false⟩, ⟨23, 1, true, ![-2, 1, 3, 4], false⟩,
  ⟨23, 2, true, ![1, 4, 3, -2], true⟩, ⟨23, 3, false, ![1, 2, 3, 4], true⟩,
  ⟨23, 3, false, ![2, 1, 4, 3], true⟩, ⟨23, 3, false, ![3, 4, 2, 1], false⟩,
  ⟨23, 3, false, ![4, 3, 1, 2], false⟩, ⟨23, 3, true, ![3, -4, 2, -1], true⟩,
  ⟨23, 4, true, ![4, 1, -2, 3], true⟩, ⟨15, 0, true, ![4, 1, -2, 3], true⟩,
  ⟨15, 1, true, ![1, -2, 4, 3], false⟩, ⟨15, 2, true, ![4, -2, 1, 3], false⟩,
  ⟨15, 3, true, ![-2, 1, 4, 3], true⟩, ⟨15, 4, false, ![1, 3, 4, 2], false⟩,
  ⟨15, 4, false, ![2, 4, 3, 1], false⟩, ⟨15, 4, false, ![3, 2, 1, 4], true⟩,
  ⟨15, 4, false, ![4, 1, 2, 3], true⟩, ⟨15, 4, true, ![3, 2, -1, -4], false⟩
]
/-- All 256 exact T5 key placements, in pinned source order. -/
def placements5 : List (Placement 4) := placements5_0 ++ placements5_1 ++ placements5_2 ++ placements5_3

/-- Consecutive explicit T7 placements 0 through 63. -/
def placements7_0 : List (Placement 6) := [
  ⟨0, 0, false, ![-3, 2, 1, 6, 5, -4], false⟩, ⟨0, 0, false, ![-4, 5, 6, 1, 2, -3], true⟩,
  ⟨0, 1, false, ![3, 4, -5, -6, 1, 2], true⟩, ⟨0, 2, false, ![-5, 4, 3, 2, 1, 6], true⟩,
  ⟨0, 3, false, ![5, -4, 3, 2, 1, -6], false⟩, ⟨0, 4, false, ![5, -6, 1, 2, 3, -4], true⟩,
  ⟨0, 5, false, ![-5, 6, 1, 2, 3, 4], false⟩, ⟨0, 6, false, ![3, 2, 1, -6, -5, 4], false⟩,
  ⟨64, 0, false, ![4, -5, -6, 1, 2, -3], false⟩, ⟨64, 1, false, ![4, 3, 2, 1, 6, 5], false⟩,
  ⟨64, 2, false, ![-4, 3, 2, 1, -6, -5], true⟩, ⟨64, 3, false, ![-6, 1, 2, 3, -4, -5], false⟩,
  ⟨64, 4, false, ![6, 1, 2, 3, 4, 5], true⟩, ⟨64, 5, false, ![2, 1, -6, -5, 4, -3], true⟩,
  ⟨64, 6, true, ![-3, 2, 1, 6, 5, -4], true⟩, ⟨64, 6, true, ![-4, 5, 6, 1, 2, -3], false⟩,
  ⟨32, 0, false, ![3, 2, 1, 6, 5, 4], false⟩, ⟨32, 1, false, ![3, 2, 1, -6, -5, -4], true⟩,
  ⟨32, 2, false, ![1, 2, 3, -4, -5, -6], false⟩, ⟨32, 3, false, ![1, 2, 3, 4, 5, 6], true⟩,
  ⟨32, 4, false, ![1, -6, -5, 4, -3, 2], true⟩, ⟨32, 5, true, ![2, 1, 6, 5, -4, -3], true⟩,
  ⟨32, 5, true, ![5, 6, 1, 2, -3, -4], false⟩, ⟨32, 6, false, ![4, -5, -6, 1, 2, -3], false⟩,
  ⟨96, 0, false, ![4, -5, 6, 1, -2, -3], false⟩, ⟨96, 1, false, ![4, 3, 2, 1, 6, 5], false⟩,
  ⟨96, 2, false, ![2, -3, -4, 5, -6, -1], true⟩, ⟨96, 2, false, ![5, -4, -3, 2, -1, -6], false⟩,
  ⟨96, 3, false, ![1, 2, 3, 4, 5, 6], true⟩, ⟨96, 4, false, ![1, 6, -5, 4, -3, -2], true⟩,
  ⟨96, 5, true, ![1, -6, 5, -4, 3, -2], false⟩, ⟨96, 6, true, ![3, -4, 5, -6, 1, -2], true⟩,
  ⟨16, 0, false, ![2, 1, -6, -5, -4, 3], true⟩, ⟨16, 1, false, ![2, 3, -4, -5, -6, 1], false⟩,
  ⟨16, 2, false, ![2, 3, 4, 5, 6, 1], true⟩, ⟨16, 3, false, ![-6, -5, 4, -3, 2, 1], true⟩,
  ⟨16, 4, true, ![1, 6, 5, -4, -3, 2], true⟩, ⟨16, 4, true, ![6, 1, 2, -3, -4, 5], false⟩,
  ⟨16, 5, false, ![-5, -6, 1, 2, -3, 4], false⟩, ⟨16, 6, false, ![3, 2, 1, 6, 5, 4], false⟩,
  ⟨80, 0, false, ![3, 2, 1, -6, -5, -4], true⟩, ⟨80, 1, false, ![3, 2, 1, 6, 5, 4], false⟩,
  ⟨80, 2, false, ![1, 2, 3, 4, 5, 6], true⟩, ⟨80, 3, false, ![1, 2, 3, -4, -5, -6], false⟩,
  ⟨80, 4, true, ![1, -6, -5, 4, 3, -2], false⟩, ⟨80, 5, false, ![2, 1, 6, 5, 4, 3], false⟩,
  ⟨80, 5, false, ![5, 6, 1, 2, 3, 4], true⟩, ⟨80, 6, true, ![4, -5, -6, 1, -2, 3], true⟩,
  ⟨48, 0, false, ![3, 2, 1, 6, 5, 4], false⟩, ⟨48, 1, false, ![-3, -4, 5, -6, -1, 2], true⟩,
  ⟨48, 1, false, ![-4, -3, 2, -1, -6, 5], false⟩, ⟨48, 2, false, ![2, 3, 4, 5, 6, 1], true⟩,
  ⟨48, 3, false, ![6, -5, 4, -3, -2, 1], true⟩, ⟨48, 4, true, ![-6, 5, -4, 3, -2, 1], false⟩,
  ⟨48, 5, true, ![-4, 5, -6, 1, -2, 3], true⟩, ⟨48, 6, false, ![4, -5, 6, 1, -2, -3], false⟩,
  ⟨112, 0, false, ![3, 2, 1, -6, 5, -4], false⟩, ⟨112, 1, false, ![3, 2, 1, 6, -5, 4], true⟩,
  ⟨112, 2, false, ![1, 2, 3, 4, -5, 6], false⟩, ⟨112, 3, false, ![1, 2, 3, -4, 5, -6], true⟩,
  ⟨112, 4, true, ![1, -6, -5, 4, -3, -2], true⟩, ⟨112, 5, true, ![2, 1, 6, 5, 4, 3], true⟩,
  ⟨112, 5, true, ![5, 6, 1, 2, 3, 4], false⟩, ⟨112, 6, true, ![4, -5, -6, 1, -2, -3], false⟩
]
/-- Consecutive explicit T7 placements 64 through 127. -/
def placements7_1 : List (Placement 6) := [
  ⟨8, 0, false, ![3, -4, -5, -6, 1, 2], false⟩, ⟨8, 1, false, ![3, 4, 5, 6, 1, 2], true⟩,
  ⟨8, 2, false, ![-5, 4, -3, 2, 1, -6], true⟩, ⟨8, 3, true, ![1, 2, -3, -4, 5, 6], false⟩,
  ⟨8, 3, true, ![6, 5, -4, -3, 2, 1], true⟩, ⟨8, 4, false, ![-6, 1, 2, -3, 4, -5], false⟩,
  ⟨8, 5, false, ![2, 1, 6, 5, 4, 3], false⟩, ⟨8, 6, false, ![2, 1, -6, -5, -4, 3], true⟩,
  ⟨72, 0, false, ![3, 2, -1, -6, -5, -4], false⟩, ⟨72, 1, false, ![-3, -4, -5, 6, 1, -2], true⟩,
  ⟨72, 1, false, ![-4, -3, -2, 1, 6, -5], false⟩, ⟨72, 2, false, ![2, 3, -4, -5, -6, -1], true⟩,
  ⟨72, 3, true, ![6, -5, 4, 3, 2, -1], true⟩, ⟨72, 4, false, ![-6, 5, -4, -3, 2, -1], false⟩,
  ⟨72, 5, false, ![-4, 5, -6, -1, 2, -3], true⟩, ⟨72, 6, true, ![4, -5, 6, -1, 2, 3], false⟩,
  ⟨40, 0, false, ![2, 1, 6, 5, 4, 3], false⟩, ⟨40, 1, false, ![2, 3, 4, 5, 6, 1], true⟩,
  ⟨40, 2, false, ![2, 3, -4, -5, -6, 1], false⟩, ⟨40, 3, true, ![-6, -5, 4, 3, -2, 1], false⟩,
  ⟨40, 4, false, ![1, 6, 5, 4, 3, 2], false⟩, ⟨40, 4, false, ![6, 1, 2, 3, 4, 5], true⟩,
  ⟨40, 5, true, ![-5, -6, 1, -2, 3, 4], true⟩, ⟨40, 6, false, ![3, 2, 1, -6, -5, -4], true⟩,
  ⟨104, 0, false, ![-3, 2, -1, 6, -5, 4], true⟩, ⟨104, 0, false, ![-4, 5, -6, 1, -2, 3], false⟩,
  ⟨104, 1, false, ![3, 4, 5, -6, -1, -2], false⟩, ⟨104, 2, false, ![-5, 4, -3, 2, -1, -6], false⟩,
  ⟨104, 3, true, ![5, -4, 3, 2, -1, 6], true⟩, ⟨104, 4, false, ![5, -6, 1, -2, -3, 4], false⟩,
  ⟨104, 5, true, ![-5, 6, 1, -2, 3, -4], true⟩, ⟨104, 6, true, ![3, 2, 1, 6, -5, -4], true⟩,
  ⟨24, 0, false, ![-3, 2, -1, -6, 5, -4], false⟩, ⟨24, 0, false, ![-4, 5, -6, -1, 2, -3], true⟩,
  ⟨24, 1, false, ![3, 4, 5, 6, 1, 2], true⟩, ⟨24, 2, false, ![-5, 4, -3, -2, 1, 6], true⟩,
  ⟨24, 3, true, ![5, -4, 3, -2, 1, -6], false⟩, ⟨24, 4, true, ![5, -6, 1, -2, 3, -4], true⟩,
  ⟨24, 5, false, ![-5, 6, 1, -2, -3, 4], false⟩, ⟨24, 6, false, ![3, 2, 1, 6, 5, 4], false⟩,
  ⟨88, 0, false, ![4, -5, -6, -1, 2, -3], true⟩, ⟨88, 1, false, ![4, 3, -2, -1, -6, 5], true⟩,
  ⟨88, 2, false, ![2, -3, 4, -5, 6, -1], false⟩, ⟨88, 2, false, ![5, -4, 3, -2, 1, -6], true⟩,
  ⟨88, 3, true, ![1, 2, 3, -4, -5, 6], false⟩, ⟨88, 4, true, ![1, 6, -5, -4, 3, -2], false⟩,
  ⟨88, 5, false, ![1, -6, 5, 4, -3, -2], true⟩, ⟨88, 6, true, ![3, -4, 5, 6, -1, 2], false⟩,
  ⟨56, 0, false, ![2, 1, 6, -5, 4, 3], true⟩, ⟨56, 1, false, ![2, 3, 4, -5, 6, 1], false⟩,
  ⟨56, 2, false, ![2, 3, -4, 5, -6, 1], true⟩, ⟨56, 3, true, ![-6, -5, 4, -3, -2, 1], true⟩,
  ⟨56, 4, true, ![1, 6, 5, 4, 3, 2], true⟩, ⟨56, 4, true, ![6, 1, 2, 3, 4, 5], false⟩,
  ⟨56, 5, true, ![-5, -6, 1, -2, -3, 4], false⟩, ⟨56, 6, false, ![3, 2, 1, -6, 5, -4], false⟩,
  ⟨120, 0, false, ![3, 2, -1, 6, 5, -4], false⟩, ⟨120, 1, false, ![-3, -4, -5, -6, -1, -2], true⟩,
  ⟨120, 1, false, ![-4, -3, -2, -1, -6, -5], false⟩, ⟨120, 2, false, ![2, 3, -4, 5, 6, -1], true⟩,
  ⟨120, 3, true, ![6, -5, 4, -3, -2, -1], true⟩, ⟨120, 4, true, ![-6, 5, -4, -3, -2, -1], false⟩,
  ⟨120, 5, true, ![-4, 5, -6, -1, -2, -3], true⟩, ⟨120, 6, true, ![4, -5, 6, -1, -2, -3], false⟩
]
/-- Consecutive explicit T7 placements 128 through 191. -/
def placements7_2 : List (Placement 6) := [
  ⟨4, 0, false, ![4, 5, 6, 1, 2, 3], true⟩, ⟨4, 1, false, ![4, -3, 2, 1, -6, -5], true⟩,
  ⟨4, 2, true, ![2, -3, -4, 5, 6, 1], false⟩, ⟨4, 2, true, ![5, -4, -3, 2, 1, 6], true⟩,
  ⟨4, 3, false, ![1, 2, -3, 4, -5, -6], false⟩, ⟨4, 4, false, ![1, 6, 5, 4, 3, 2], false⟩,
  ⟨4, 5, false, ![1, -6, -5, -4, 3, 2], true⟩, ⟨4, 6, false, ![3, -4, -5, -6, 1, 2], false⟩,
  ⟨68, 0, false, ![2, -1, -6, 5, -4, -3], false⟩, ⟨68, 1, false, ![2, -3, -4, 5, -6, -1], true⟩,
  ⟨68, 2, true, ![2, 3, 4, -5, 6, -1], false⟩, ⟨68, 3, false, ![-6, -5, -4, 3, 2, -1], false⟩,
  ⟨68, 4, false, ![1, 6, -5, -4, -3, -2], false⟩, ⟨68, 4, false, ![6, 1, -2, -3, -4, -5], true⟩,
  ⟨68, 5, false, ![-5, -6, -1, 2, 3, -4], true⟩, ⟨68, 6, true, ![3, 2, -1, 6, -5, 4], true⟩,
  ⟨36, 0, false, ![-3, -2, 1, 6, -5, -4], false⟩, ⟨36, 0, false, ![-4, -5, 6, 1, -2, -3], true⟩,
  ⟨36, 1, false, ![3, -4, -5, -6, -1, 2], true⟩, ⟨36, 2, true, ![-5, 4, 3, 2, -1, 6], true⟩,
  ⟨36, 3, false, ![5, -4, -3, 2, -1, -6], false⟩, ⟨36, 4, false, ![5, -6, -1, 2, -3, -4], true⟩,
  ⟨36, 5, true, ![-5, 6, -1, 2, 3, 4], false⟩, ⟨36, 6, false, ![3, 2, -1, -6, -5, -4], false⟩,
  ⟨100, 0, false, ![4, 5, 6, 1, -2, -3], true⟩, ⟨100, 1, false, ![4, -3, 2, 1, 6, 5], true⟩,
  ⟨100, 2, true, ![2, -3, -4, 5, -6, -1], false⟩, ⟨100, 2, true, ![5, -4, -3, 2, -1, -6], true⟩,
  ⟨100, 3, false, ![1, 2, -3, 4, 5, 6], false⟩, ⟨100, 4, false, ![1, 6, 5, 4, -3, -2], false⟩,
  ⟨100, 5, true, ![1, -6, -5, -4, 3, -2], true⟩, ⟨100, 6, true, ![3, -4, -5, -6, 1, -2], false⟩,
  ⟨20, 0, false, ![3, 4, 5, 6, 1, 2], true⟩, ⟨20, 1, false, ![3, -4, -5, -6, 1, 2], false⟩,
  ⟨20, 2, true, ![-5, 4, 3, -2, 1, -6], false⟩, ⟨20, 3, false, ![1, 2, 3, 4, 5, 6], true⟩,
  ⟨20, 3, false, ![6, 5, 4, 3, 2, 1], false⟩, ⟨20, 4, true, ![-6, 1, -2, 3, 4, -5], true⟩,
  ⟨20, 5, false, ![2, 1, -6, -5, -4, 3], true⟩, ⟨20, 6, false, ![2, 1, 6, 5, 4, 3], false⟩,
  ⟨84, 0, false, ![2, -1, -6, -5, -4, -3], true⟩, ⟨84, 1, false, ![2, -3, -4, -5, -6, -1], false⟩,
  ⟨84, 2, true, ![2, 3, 4, 5, 6, -1], true⟩, ⟨84, 3, false, ![-6, -5, -4, -3, 2, -1], true⟩,
  ⟨84, 4, true, ![1, 6, -5, -4, -3, -2], true⟩, ⟨84, 4, true, ![6, 1, -2, -3, -4, -5], false⟩,
  ⟨84, 5, false, ![-5, -6, -1, 2, -3, -4], false⟩, ⟨84, 6, true, ![3, 2, -1, 6, 5, 4], false⟩,
  ⟨52, 0, false, ![4, 5, -6, -1, -2, 3], false⟩, ⟨52, 1, false, ![4, -3, 2, -1, -6, -5], false⟩,
  ⟨52, 2, true, ![-4, 3, 2, -1, 6, 5], true⟩, ⟨52, 3, false, ![-6, 1, -2, -3, 4, 5], false⟩,
  ⟨52, 4, true, ![6, 1, -2, 3, -4, -5], true⟩, ⟨52, 5, true, ![2, 1, 6, -5, -4, 3], true⟩,
  ⟨52, 6, false, ![-3, 2, -1, 6, -5, 4], true⟩, ⟨52, 6, false, ![-4, 5, -6, 1, -2, 3], false⟩,
  ⟨116, 0, false, ![4, 5, -6, -1, -2, -3], true⟩, ⟨116, 1, false, ![4, -3, 2, -1, -6, 5], true⟩,
  ⟨116, 2, true, ![-4, 3, 2, -1, 6, -5], false⟩, ⟨116, 3, false, ![-6, 1, -2, -3, 4, -5], true⟩,
  ⟨116, 4, true, ![6, 1, -2, 3, -4, 5], false⟩, ⟨116, 5, true, ![2, 1, 6, -5, -4, -3], false⟩,
  ⟨116, 6, true, ![-3, 2, -1, 6, -5, 4], false⟩, ⟨116, 6, true, ![-4, 5, -6, 1, -2, 3], true⟩
]
/-- Consecutive explicit T7 placements 192 through 255. -/
def placements7_3 : List (Placement 6) := [
  ⟨12, 0, false, ![4, 5, 6, 1, 2, 3], true⟩, ⟨12, 1, false, ![4, -3, -2, 1, 6, -5], true⟩,
  ⟨12, 2, true, ![-4, 3, -2, 1, -6, 5], false⟩, ⟨12, 3, true, ![-6, 1, -2, 3, -4, 5], true⟩,
  ⟨12, 4, false, ![6, 1, -2, -3, 4, -5], false⟩, ⟨12, 5, false, ![2, 1, 6, 5, 4, 3], false⟩,
  ⟨12, 6, false, ![-3, 2, -1, -6, 5, -4], false⟩, ⟨12, 6, false, ![-4, 5, -6, -1, 2, -3], true⟩,
  ⟨76, 0, false, ![4, 5, 6, 1, 2, -3], false⟩, ⟨76, 1, false, ![4, -3, -2, 1, 6, 5], false⟩,
  ⟨76, 2, true, ![-4, 3, -2, 1, -6, -5], true⟩, ⟨76, 3, true, ![-6, 1, -2, 3, -4, -5], false⟩,
  ⟨76, 4, false, ![6, 1, -2, -3, 4, 5], true⟩, ⟨76, 5, false, ![2, 1, 6, 5, 4, -3], true⟩,
  ⟨76, 6, true, ![-3, 2, -1, -6, 5, -4], true⟩, ⟨76, 6, true, ![-4, 5, -6, -1, 2, -3], false⟩,
  ⟨44, 0, false, ![3, -2, -1, -6, 5, 4], true⟩, ⟨44, 1, false, ![-3, 4, -5, 6, -1, 2], false⟩,
  ⟨44, 1, false, ![-4, 3, -2, 1, -6, 5], true⟩, ⟨44, 2, true, ![2, 3, -4, -5, 6, 1], false⟩,
  ⟨44, 3, true, ![6, -5, -4, 3, -2, 1], false⟩, ⟨44, 4, false, ![-6, 5, 4, -3, -2, 1], true⟩,
  ⟨44, 5, true, ![-4, 5, 6, -1, 2, 3], false⟩, ⟨44, 6, false, ![4, -5, -6, -1, 2, -3], true⟩,
  ⟨108, 0, false, ![2, -1, 6, 5, 4, -3], false⟩, ⟨108, 1, false, ![2, -3, 4, 5, 6, -1], true⟩,
  ⟨108, 2, true, ![2, 3, -4, -5, -6, -1], false⟩, ⟨108, 3, true, ![-6, -5, -4, 3, -2, -1], false⟩,
  ⟨108, 4, false, ![1, 6, -5, 4, 3, -2], false⟩, ⟨108, 4, false, ![6, 1, -2, 3, 4, -5], true⟩,
  ⟨108, 5, true, ![-5, -6, -1, -2, 3, -4], true⟩, ⟨108, 6, true, ![3, 2, -1, -6, -5, -4], true⟩,
  ⟨28, 0, false, ![3, 4, -5, 6, 1, 2], false⟩, ⟨28, 1, false, ![3, -4, 5, -6, 1, 2], true⟩,
  ⟨28, 2, true, ![-5, 4, -3, -2, 1, -6], true⟩, ⟨28, 3, true, ![1, 2, 3, 4, 5, 6], false⟩,
  ⟨28, 3, true, ![6, 5, 4, 3, 2, 1], true⟩, ⟨28, 4, true, ![-6, 1, -2, -3, 4, -5], false⟩,
  ⟨28, 5, false, ![2, 1, -6, 5, -4, 3], false⟩, ⟨28, 6, false, ![2, 1, 6, -5, 4, 3], true⟩,
  ⟨92, 0, false, ![4, 5, -6, -1, 2, -3], false⟩, ⟨92, 1, false, ![4, -3, -2, -1, -6, 5], false⟩,
  ⟨92, 2, true, ![2, -3, 4, -5, 6, -1], true⟩, ⟨92, 2, true, ![5, -4, 3, -2, 1, -6], false⟩,
  ⟨92, 3, true, ![1, 2, -3, -4, -5, 6], true⟩, ⟨92, 4, true, ![1, 6, 5, -4, 3, -2], true⟩,
  ⟨92, 5, false, ![1, -6, -5, 4, -3, -2], false⟩, ⟨92, 6, true, ![3, -4, -5, 6, -1, 2], true⟩,
  ⟨60, 0, false, ![-3, -2, -1, -6, -5, -4], false⟩, ⟨60, 0, false, ![-4, -5, -6, -1, -2, -3], true⟩,
  ⟨60, 1, false, ![3, -4, 5, 6, -1, 2], true⟩, ⟨60, 2, true, ![-5, 4, -3, -2, -1, 6], true⟩,
  ⟨60, 3, true, ![5, -4, -3, -2, -1, -6], false⟩, ⟨60, 4, true, ![5, -6, -1, -2, -3, -4], true⟩,
  ⟨60, 5, true, ![-5, 6, -1, -2, -3, 4], false⟩, ⟨60, 6, false, ![3, 2, -1, 6, 5, -4], false⟩,
  ⟨124, 0, false, ![2, -1, 6, -5, 4, -3], true⟩, ⟨124, 1, false, ![2, -3, 4, -5, 6, -1], false⟩,
  ⟨124, 2, true, ![2, 3, -4, 5, -6, -1], true⟩, ⟨124, 3, true, ![-6, -5, -4, -3, -2, -1], true⟩,
  ⟨124, 4, true, ![1, 6, -5, 4, 3, -2], true⟩, ⟨124, 4, true, ![6, 1, -2, 3, 4, -5], false⟩,
  ⟨124, 5, true, ![-5, -6, -1, -2, -3, -4], false⟩, ⟨124, 6, true, ![3, 2, -1, -6, 5, -4], false⟩
]
/-- Consecutive explicit T7 placements 256 through 319. -/
def placements7_4 : List (Placement 6) := [
  ⟨2, 0, false, ![-3, 2, 1, -6, -5, 4], true⟩, ⟨2, 1, true, ![-3, -4, 5, 6, 1, 2], false⟩,
  ⟨2, 1, true, ![-4, -3, 2, 1, 6, 5], true⟩, ⟨2, 2, false, ![2, -3, 4, -5, -6, 1], false⟩,
  ⟨2, 3, false, ![6, 5, 4, 3, 2, 1], false⟩, ⟨2, 4, false, ![-6, -5, -4, 3, 2, 1], true⟩,
  ⟨2, 5, false, ![-4, -5, -6, 1, 2, 3], false⟩, ⟨2, 6, false, ![4, 5, 6, 1, 2, 3], true⟩,
  ⟨66, 0, false, ![3, 2, 1, 6, 5, 4], false⟩, ⟨66, 0, false, ![4, 5, 6, 1, 2, 3], true⟩,
  ⟨66, 1, true, ![3, 4, -5, -6, 1, -2], true⟩, ⟨66, 2, false, ![-5, -4, 3, 2, 1, -6], true⟩,
  ⟨66, 3, false, ![5, 4, 3, 2, 1, 6], false⟩, ⟨66, 4, false, ![5, 6, 1, 2, 3, 4], true⟩,
  ⟨66, 5, false, ![-5, -6, 1, 2, 3, -4], false⟩, ⟨66, 6, true, ![3, -2, 1, -6, -5, 4], false⟩,
  ⟨34, 0, false, ![-3, -4, 5, -6, -1, 2], true⟩, ⟨34, 1, true, ![3, 4, -5, 6, -1, 2], false⟩,
  ⟨34, 2, false, ![-5, -4, 3, 2, -1, -6], false⟩, ⟨34, 3, false, ![1, -2, -3, -4, -5, 6], true⟩,
  ⟨34, 3, false, ![6, -5, -4, -3, -2, 1], false⟩, ⟨34, 4, false, ![-6, -1, 2, 3, -4, -5], true⟩,
  ⟨34, 5, true, ![2, -1, 6, -5, 4, 3], true⟩, ⟨34, 6, false, ![2, -1, -6, 5, -4, -3], false⟩,
  ⟨98, 0, false, ![-2, 1, -6, 5, 4, -3], true⟩, ⟨98, 1, true, ![2, 3, -4, 5, 6, -1], false⟩,
  ⟨98, 2, false, ![2, -3, 4, -5, -6, -1], true⟩, ⟨98, 3, false, ![-6, 5, 4, 3, -2, -1], true⟩,
  ⟨98, 4, false, ![1, -6, 5, -4, 3, -2], true⟩, ⟨98, 4, false, ![6, -1, 2, -3, 4, -5], false⟩,
  ⟨98, 5, true, ![-5, 6, 1, 2, 3, -4], false⟩, ⟨98, 6, true, ![3, -2, 1, 6, -5, -4], false⟩,
  ⟨18, 0, false, ![-4, -5, -6, -1, 2, 3], true⟩, ⟨18, 1, true, ![4, 3, 2, -1, 6, -5], true⟩,
  ⟨18, 2, false, ![-4, -3, 2, -1, -6, 5], false⟩, ⟨18, 3, false, ![-6, -1, 2, -3, -4, 5], true⟩,
  ⟨18, 4, true, ![6, -1, 2, 3, 4, -5], false⟩, ⟨18, 5, false, ![2, -1, -6, -5, -4, 3], false⟩,
  ⟨18, 6, false, ![-3, -2, 1, 6, -5, -4], false⟩, ⟨18, 6, false, ![-4, -5, 6, 1, -2, -3], true⟩,
  ⟨82, 0, false, ![-4, -5, -6, -1, 2, -3], false⟩, ⟨82, 1, true, ![4, 3, 2, -1, 6, 5], false⟩,
  ⟨82, 2, false, ![-4, -3, 2, -1, -6, -5], true⟩, ⟨82, 3, false, ![-6, -1, 2, -3, -4, -5], false⟩,
  ⟨82, 4, true, ![6, -1, 2, 3, 4, 5], true⟩, ⟨82, 5, false, ![2, -1, -6, -5, -4, -3], true⟩,
  ⟨82, 6, true, ![-3, -2, 1, 6, -5, -4], true⟩, ⟨82, 6, true, ![-4, -5, 6, 1, -2, -3], false⟩,
  ⟨50, 0, false, ![-3, 2, 1, 6, 5, 4], true⟩, ⟨50, 1, true, ![-3, -4, 5, -6, -1, 2], false⟩,
  ⟨50, 1, true, ![-4, -3, 2, -1, -6, 5], true⟩, ⟨50, 2, false, ![2, -3, 4, 5, 6, 1], false⟩,
  ⟨50, 3, false, ![6, 5, 4, -3, -2, 1], false⟩, ⟨50, 4, true, ![-6, -5, -4, 3, -2, 1], true⟩,
  ⟨50, 5, true, ![-4, -5, -6, 1, -2, 3], false⟩, ⟨50, 6, false, ![4, 5, 6, 1, -2, -3], true⟩,
  ⟨114, 0, false, ![-2, 1, -6, -5, 4, -3], false⟩, ⟨114, 1, true, ![2, 3, -4, -5, 6, -1], true⟩,
  ⟨114, 2, false, ![2, -3, 4, 5, -6, -1], false⟩, ⟨114, 3, false, ![-6, 5, 4, -3, -2, -1], false⟩,
  ⟨114, 4, true, ![1, -6, 5, -4, 3, -2], false⟩, ⟨114, 4, true, ![6, -1, 2, -3, 4, -5], true⟩,
  ⟨114, 5, true, ![-5, 6, 1, 2, -3, -4], true⟩, ⟨114, 6, true, ![3, -2, 1, 6, 5, -4], true⟩
]
/-- Consecutive explicit T7 placements 320 through 383. -/
def placements7_5 : List (Placement 6) := [
  ⟨10, 0, false, ![-4, -5, -6, 1, 2, 3], false⟩, ⟨10, 1, true, ![4, 3, -2, 1, -6, -5], false⟩,
  ⟨10, 2, false, ![2, 3, 4, 5, 6, 1], true⟩, ⟨10, 2, false, ![5, 4, 3, 2, 1, 6], false⟩,
  ⟨10, 3, true, ![1, -2, 3, 4, -5, -6], true⟩, ⟨10, 4, false, ![1, -6, -5, -4, 3, 2], true⟩,
  ⟨10, 5, false, ![1, 6, 5, 4, 3, 2], false⟩, ⟨10, 6, false, ![3, 4, 5, 6, 1, 2], true⟩,
  ⟨74, 0, false, ![-3, 2, -1, -6, -5, -4], true⟩, ⟨74, 1, true, ![-3, -4, -5, 6, 1, -2], false⟩,
  ⟨74, 1, true, ![-4, -3, -2, 1, 6, -5], true⟩, ⟨74, 2, false, ![2, -3, -4, -5, -6, -1], false⟩,
  ⟨74, 3, true, ![6, 5, 4, 3, 2, -1], false⟩, ⟨74, 4, false, ![-6, -5, -4, -3, 2, -1], true⟩,
  ⟨74, 5, false, ![-4, -5, -6, -1, 2, -3], false⟩, ⟨74, 6, true, ![4, 5, 6, -1, 2, 3], true⟩,
  ⟨42, 0, false, ![-3, -4, -5, -6, -1, 2], false⟩, ⟨42, 1, true, ![3, 4, 5, 6, -1, 2], true⟩,
  ⟨42, 2, false, ![-5, -4, -3, 2, -1, -6], true⟩, ⟨42, 3, true, ![1, -2, -3, -4, -5, 6], false⟩,
  ⟨42, 3, true, ![6, -5, -4, -3, -2, 1], true⟩, ⟨42, 4, false, ![-6, -1, 2, -3, -4, -5], false⟩,
  ⟨42, 5, true, ![2, -1, 6, 5, 4, 3], false⟩, ⟨42, 6, false, ![2, -1, -6, -5, -4, -3], true⟩,
  ⟨106, 0, false, ![-4, -5, -6, 1, -2, -3], false⟩, ⟨106, 1, true, ![4, 3, -2, 1, 6, 5], false⟩,
  ⟨106, 2, false, ![2, 3, 4, 5, -6, -1], true⟩, ⟨106, 2, false, ![5, 4, 3, 2, -1, -6], false⟩,
  ⟨106, 3, true, ![1, -2, 3, 4, 5, 6], true⟩, ⟨106, 4, false, ![1, -6, -5, -4, -3, -2], true⟩,
  ⟨106, 5, true, ![1, 6, 5, 4, 3, -2], false⟩, ⟨106, 6, true, ![3, 4, 5, 6, 1, -2], true⟩,
  ⟨26, 0, false, ![-3, 2, -1, -6, -5, 4], false⟩, ⟨26, 1, true, ![3, 2, -1, 6, 5, -4], true⟩,
  ⟨26, 2, false, ![1, -2, -3, 4, 5, -6], false⟩, ⟨26, 3, true, ![1, -2, 3, -4, -5, 6], true⟩,
  ⟨26, 4, true, ![1, 6, -5, -4, 3, 2], true⟩, ⟨26, 5, false, ![2, -1, 6, -5, 4, -3], true⟩,
  ⟨26, 5, false, ![5, -6, 1, -2, 3, -4], false⟩, ⟨26, 6, false, ![4, 5, -6, -1, -2, 3], false⟩,
  ⟨90, 0, false, ![3, 2, -1, -6, 5, 4], false⟩, ⟨90, 0, false, ![4, 5, -6, -1, 2, 3], true⟩,
  ⟨90, 1, true, ![3, 4, 5, 6, 1, -2], true⟩, ⟨90, 2, false, ![-5, -4, -3, -2, 1, -6], true⟩,
  ⟨90, 3, true, ![5, 4, 3, -2, 1, 6], false⟩, ⟨90, 4, true, ![5, 6, 1, -2, 3, 4], true⟩,
  ⟨90, 5, false, ![-5, -6, 1, -2, -3, -4], false⟩, ⟨90, 6, true, ![3, -2, 1, 6, 5, 4], false⟩,
  ⟨58, 0, false, ![-3, 2, -1, -6, 5, 4], true⟩, ⟨58, 1, true, ![3, 2, -1, 6, -5, -4], false⟩,
  ⟨58, 2, false, ![1, -2, -3, 4, -5, -6], true⟩, ⟨58, 3, true, ![1, -2, 3, -4, 5, 6], false⟩,
  ⟨58, 4, true, ![1, 6, -5, -4, -3, 2], false⟩, ⟨58, 5, true, ![2, -1, 6, -5, 4, -3], false⟩,
  ⟨58, 5, true, ![5, -6, 1, -2, 3, -4], true⟩, ⟨58, 6, false, ![4, 5, -6, -1, -2, -3], true⟩,
  ⟨122, 0, false, ![-3, 2, -1, 6, 5, -4], true⟩, ⟨122, 1, true, ![-3, -4, -5, -6, -1, -2], false⟩,
  ⟨122, 1, true, ![-4, -3, -2, -1, -6, -5], true⟩, ⟨122, 2, false, ![2, -3, -4, 5, 6, -1], false⟩,
  ⟨122, 3, true, ![6, 5, 4, -3, -2, -1], false⟩, ⟨122, 4, true, ![-6, -5, -4, -3, -2, -1], true⟩,
  ⟨122, 5, true, ![-4, -5, -6, -1, -2, -3], false⟩, ⟨122, 6, true, ![4, 5, 6, -1, -2, -3], true⟩
]
/-- Consecutive explicit T7 placements 384 through 447. -/
def placements7_6 : List (Placement 6) := [
  ⟨6, 0, false, ![-3, -2, 1, 6, -5, 4], true⟩, ⟨6, 1, true, ![3, -2, 1, -6, 5, -4], false⟩,
  ⟨6, 2, true, ![1, -2, 3, -4, 5, -6], true⟩, ⟨6, 3, false, ![1, -2, -3, 4, -5, 6], false⟩,
  ⟨6, 4, false, ![1, 6, 5, 4, 3, 2], false⟩, ⟨6, 5, false, ![2, -1, -6, 5, -4, -3], false⟩,
  ⟨6, 5, false, ![5, -6, -1, 2, -3, -4], true⟩, ⟨6, 6, false, ![4, 5, 6, 1, 2, 3], true⟩,
  ⟨70, 0, false, ![-3, 4, 5, -6, 1, -2], false⟩, ⟨70, 1, true, ![3, -4, -5, 6, 1, -2], true⟩,
  ⟨70, 2, true, ![-5, -4, 3, 2, 1, 6], true⟩, ⟨70, 3, false, ![1, -2, 3, -4, 5, -6], false⟩,
  ⟨70, 3, false, ![6, -5, 4, -3, 2, -1], true⟩, ⟨70, 4, false, ![-6, -1, -2, 3, 4, 5], false⟩,
  ⟨70, 5, false, ![2, -1, -6, -5, 4, -3], false⟩, ⟨70, 6, true, ![2, -1, 6, 5, -4, 3], true⟩,
  ⟨38, 0, false, ![-3, -2, 1, 6, 5, 4], false⟩, ⟨38, 1, true, ![3, -2, 1, -6, -5, -4], true⟩,
  ⟨38, 2, true, ![1, -2, 3, -4, -5, -6], false⟩, ⟨38, 3, false, ![1, -2, -3, 4, 5, 6], true⟩,
  ⟨38, 4, false, ![1, 6, 5, 4, -3, 2], true⟩, ⟨38, 5, true, ![2, -1, -6, 5, -4, -3], true⟩,
  ⟨38, 5, true, ![5, -6, -1, 2, -3, -4], false⟩, ⟨38, 6, false, ![4, 5, 6, 1, 2, -3], false⟩,
  ⟨102, 0, false, ![3, -2, 1, 6, -5, 4], false⟩, ⟨102, 0, false, ![4, -5, 6, 1, -2, 3], true⟩,
  ⟨102, 1, true, ![3, -4, -5, -6, -1, -2], true⟩, ⟨102, 2, true, ![-5, -4, 3, 2, -1, -6], true⟩,
  ⟨102, 3, false, ![5, 4, -3, 2, -1, 6], false⟩, ⟨102, 4, false, ![5, 6, -1, 2, -3, 4], true⟩,
  ⟨102, 5, true, ![-5, -6, -1, 2, 3, -4], false⟩, ⟨102, 6, true, ![3, -2, -1, -6, -5, -4], false⟩,
  ⟨22, 0, false, ![3, -2, 1, -6, 5, -4], true⟩, ⟨22, 0, false, ![4, -5, 6, -1, 2, -3], false⟩,
  ⟨22, 1, true, ![3, -4, -5, 6, 1, 2], false⟩, ⟨22, 2, true, ![-5, -4, 3, -2, 1, 6], false⟩,
  ⟨22, 3, false, ![5, 4, -3, -2, 1, -6], true⟩, ⟨22, 4, true, ![5, 6, -1, 2, 3, -4], false⟩,
  ⟨22, 5, false, ![-5, -6, -1, 2, -3, 4], true⟩, ⟨22, 6, false, ![3, -2, -1, -6, 5, 4], true⟩,
  ⟨86, 0, false, ![-3, -2, 1, -6, -5, -4], true⟩, ⟨86, 1, true, ![3, -2, 1, 6, 5, 4], false⟩,
  ⟨86, 2, true, ![1, -2, 3, 4, 5, 6], true⟩, ⟨86, 3, false, ![1, -2, -3, -4, -5, -6], false⟩,
  ⟨86, 4, true, ![1, 6, 5, 4, 3, -2], false⟩, ⟨86, 5, false, ![2, -1, -6, 5, 4, 3], false⟩,
  ⟨86, 5, false, ![5, -6, -1, 2, 3, 4], true⟩, ⟨86, 6, true, ![4, 5, 6, 1, -2, 3], true⟩,
  ⟨54, 0, false, ![-3, 4, 5, 6, -1, 2], true⟩, ⟨54, 1, true, ![3, -4, -5, -6, -1, 2], false⟩,
  ⟨54, 2, true, ![-5, -4, 3, -2, -1, -6], false⟩, ⟨54, 3, false, ![1, -2, 3, 4, -5, 6], true⟩,
  ⟨54, 3, false, ![6, -5, 4, 3, -2, 1], false⟩, ⟨54, 4, true, ![-6, -1, -2, 3, -4, -5], true⟩,
  ⟨54, 5, true, ![2, -1, -6, -5, -4, 3], true⟩, ⟨54, 6, false, ![2, -1, 6, 5, 4, -3], false⟩,
  ⟨118, 0, false, ![-3, -2, 1, -6, 5, -4], false⟩, ⟨118, 1, true, ![3, -2, 1, 6, -5, 4], true⟩,
  ⟨118, 2, true, ![1, -2, 3, 4, -5, 6], false⟩, ⟨118, 3, false, ![1, -2, -3, -4, 5, -6], true⟩,
  ⟨118, 4, true, ![1, 6, 5, 4, -3, -2], true⟩, ⟨118, 5, true, ![2, -1, -6, 5, 4, 3], true⟩,
  ⟨118, 5, true, ![5, -6, -1, 2, 3, 4], false⟩, ⟨118, 6, true, ![4, 5, 6, 1, -2, -3], false⟩
]
/-- Consecutive explicit T7 placements 448 through 511. -/
def placements7_7 : List (Placement 6) := [
  ⟨14, 0, false, ![-4, 5, -6, 1, 2, 3], true⟩, ⟨14, 1, true, ![4, -3, -2, 1, -6, -5], true⟩,
  ⟨14, 2, true, ![2, 3, 4, 5, 6, 1], false⟩, ⟨14, 2, true, ![5, 4, 3, 2, 1, 6], true⟩,
  ⟨14, 3, true, ![1, -2, -3, 4, -5, -6], false⟩, ⟨14, 4, false, ![1, -6, 5, -4, 3, 2], false⟩,
  ⟨14, 5, false, ![1, 6, -5, 4, 3, 2], true⟩, ⟨14, 6, false, ![3, 4, -5, 6, 1, 2], false⟩,
  ⟨78, 0, false, ![-3, 4, -5, -6, 1, -2], true⟩, ⟨78, 1, true, ![3, -4, 5, 6, 1, -2], false⟩,
  ⟨78, 2, true, ![-5, -4, -3, 2, 1, 6], false⟩, ⟨78, 3, true, ![1, -2, 3, -4, 5, -6], true⟩,
  ⟨78, 3, true, ![6, -5, 4, -3, 2, -1], false⟩, ⟨78, 4, false, ![-6, -1, -2, -3, 4, 5], true⟩,
  ⟨78, 5, false, ![2, -1, -6, 5, 4, -3], true⟩, ⟨78, 6, true, ![2, -1, 6, -5, -4, 3], false⟩,
  ⟨46, 0, false, ![-3, -2, -1, -6, 5, 4], false⟩, ⟨46, 1, true, ![-3, 4, -5, 6, -1, 2], true⟩,
  ⟨46, 1, true, ![-4, 3, -2, 1, -6, 5], false⟩, ⟨46, 2, true, ![2, -3, -4, -5, 6, 1], true⟩,
  ⟨46, 3, true, ![6, 5, -4, 3, -2, 1], true⟩, ⟨46, 4, false, ![-6, -5, 4, -3, -2, 1], false⟩,
  ⟨46, 5, true, ![-4, -5, 6, -1, 2, 3], true⟩, ⟨46, 6, false, ![4, 5, -6, -1, 2, -3], false⟩,
  ⟨110, 0, false, ![-4, 5, -6, 1, -2, -3], true⟩, ⟨110, 1, true, ![4, -3, -2, 1, 6, 5], true⟩,
  ⟨110, 2, true, ![2, 3, 4, 5, -6, -1], false⟩, ⟨110, 2, true, ![5, 4, 3, 2, -1, -6], true⟩,
  ⟨110, 3, true, ![1, -2, -3, 4, 5, 6], false⟩, ⟨110, 4, false, ![1, -6, 5, -4, -3, -2], false⟩,
  ⟨110, 5, true, ![1, 6, -5, 4, 3, -2], true⟩, ⟨110, 6, true, ![3, 4, -5, 6, 1, -2], false⟩,
  ⟨30, 0, false, ![-4, 5, 6, -1, 2, 3], true⟩, ⟨30, 1, true, ![4, -3, -2, -1, 6, -5], true⟩,
  ⟨30, 2, true, ![-4, -3, -2, -1, -6, 5], false⟩, ⟨30, 3, true, ![-6, -1, -2, -3, -4, 5], true⟩,
  ⟨30, 4, true, ![6, -1, -2, -3, 4, -5], false⟩, ⟨30, 5, false, ![2, -1, 6, 5, -4, 3], false⟩,
  ⟨30, 6, false, ![-3, -2, -1, -6, -5, -4], false⟩, ⟨30, 6, false, ![-4, -5, -6, -1, -2, -3], true⟩,
  ⟨94, 0, false, ![-4, 5, 6, -1, 2, -3], false⟩, ⟨94, 1, true, ![4, -3, -2, -1, 6, 5], false⟩,
  ⟨94, 2, true, ![-4, -3, -2, -1, -6, -5], true⟩, ⟨94, 3, true, ![-6, -1, -2, -3, -4, -5], false⟩,
  ⟨94, 4, true, ![6, -1, -2, -3, 4, 5], true⟩, ⟨94, 5, false, ![2, -1, 6, 5, -4, -3], true⟩,
  ⟨94, 6, true, ![-3, -2, -1, -6, -5, -4], true⟩, ⟨94, 6, true, ![-4, -5, -6, -1, -2, -3], false⟩,
  ⟨62, 0, false, ![-3, 4, -5, 6, -1, 2], false⟩, ⟨62, 1, true, ![3, -4, 5, -6, -1, 2], true⟩,
  ⟨62, 2, true, ![-5, -4, -3, -2, -1, -6], true⟩, ⟨62, 3, true, ![1, -2, 3, 4, -5, 6], false⟩,
  ⟨62, 3, true, ![6, -5, 4, 3, -2, 1], true⟩, ⟨62, 4, true, ![-6, -1, -2, -3, -4, -5], false⟩,
  ⟨62, 5, true, ![2, -1, -6, 5, -4, 3], false⟩, ⟨62, 6, false, ![2, -1, 6, -5, 4, -3], true⟩,
  ⟨126, 0, false, ![3, -2, -1, -6, -5, 4], false⟩, ⟨126, 0, false, ![4, -5, -6, -1, -2, 3], true⟩,
  ⟨126, 0, true, ![-3, 2, 1, 6, 5, -4], true⟩, ⟨126, 0, true, ![-4, 5, 6, 1, 2, -3], false⟩,
  ⟨126, 1, true, ![3, -4, 5, 6, -1, -2], true⟩, ⟨126, 2, true, ![-5, -4, -3, -2, -1, -6], true⟩,
  ⟨126, 3, true, ![5, 4, -3, -2, -1, 6], false⟩, ⟨126, 4, true, ![5, 6, -1, -2, -3, 4], true⟩
]
/-- Consecutive explicit T7 placements 512 through 575. -/
def placements7_8 : List (Placement 6) := [
  ⟨126, 5, true, ![-5, -6, -1, -2, -3, -4], false⟩, ⟨126, 6, true, ![3, -2, -1, 6, 5, -4], false⟩,
  ⟨1, 0, true, ![-3, 2, 1, 6, 5, -4], true⟩, ⟨1, 0, true, ![-4, 5, 6, 1, 2, -3], false⟩,
  ⟨1, 1, false, ![-3, 4, -5, -6, 1, 2], false⟩, ⟨1, 2, false, ![5, 4, 3, 2, 1, 6], false⟩,
  ⟨1, 3, false, ![-5, -4, 3, 2, 1, -6], true⟩, ⟨1, 4, false, ![-5, -6, 1, 2, 3, -4], false⟩,
  ⟨1, 5, false, ![5, 6, 1, 2, 3, 4], true⟩, ⟨1, 6, false, ![-3, 2, 1, -6, -5, 4], true⟩,
  ⟨65, 0, true, ![3, -4, 5, -6, 1, -2], true⟩, ⟨65, 1, false, ![-3, 4, -5, 6, 1, -2], false⟩,
  ⟨65, 2, false, ![5, 4, 3, 2, 1, 6], false⟩, ⟨65, 3, false, ![-1, 2, -3, -4, 5, -6], true⟩,
  ⟨65, 3, false, ![-6, 5, -4, -3, 2, -1], false⟩, ⟨65, 4, false, ![6, 1, 2, 3, 4, 5], true⟩,
  ⟨65, 5, false, ![-2, 1, 6, -5, 4, -3], true⟩, ⟨65, 6, true, ![-2, 1, -6, 5, -4, 3], false⟩,
  ⟨33, 0, true, ![4, -5, -6, 1, -2, 3], true⟩, ⟨33, 1, false, ![-4, 3, 2, 1, -6, -5], true⟩,
  ⟨33, 2, false, ![4, 3, 2, 1, 6, 5], false⟩, ⟨33, 3, false, ![6, 1, 2, 3, 4, 5], true⟩,
  ⟨33, 4, false, ![-6, 1, 2, 3, -4, -5], false⟩, ⟨33, 5, true, ![-2, 1, -6, -5, 4, 3], false⟩,
  ⟨33, 6, false, ![3, 2, 1, 6, 5, 4], false⟩, ⟨33, 6, false, ![4, 5, 6, 1, 2, 3], true⟩,
  ⟨97, 0, true, ![4, -5, -6, 1, -2, -3], false⟩, ⟨97, 1, false, ![-4, 3, 2, 1, -6, 5], false⟩,
  ⟨97, 2, false, ![4, 3, 2, 1, 6, -5], true⟩, ⟨97, 3, false, ![6, 1, 2, 3, 4, -5], false⟩,
  ⟨97, 4, false, ![-6, 1, 2, 3, -4, 5], true⟩, ⟨97, 5, true, ![-2, 1, -6, -5, 4, -3], true⟩,
  ⟨97, 6, true, ![3, 2, 1, 6, 5, 4], true⟩, ⟨97, 6, true, ![4, 5, 6, 1, 2, 3], false⟩,
  ⟨17, 0, true, ![4, -5, 6, -1, 2, 3], false⟩, ⟨17, 1, false, ![-4, 3, 2, -1, -6, -5], false⟩,
  ⟨17, 2, false, ![-2, -3, -4, -5, 6, 1], true⟩, ⟨17, 2, false, ![-5, -4, -3, -2, 1, 6], false⟩,
  ⟨17, 3, false, ![-1, 2, 3, -4, -5, -6], true⟩, ⟨17, 4, true, ![-1, 6, -5, 4, 3, 2], true⟩,
  ⟨17, 5, false, ![-1, -6, 5, -4, -3, 2], false⟩, ⟨17, 6, false, ![-3, -4, 5, -6, -1, 2], true⟩,
  ⟨81, 0, true, ![3, 2, 1, 6, -5, -4], true⟩, ⟨81, 1, false, ![3, -4, 5, -6, 1, -2], false⟩,
  ⟨81, 1, false, ![4, -3, 2, -1, 6, -5], true⟩, ⟨81, 2, false, ![-2, 3, 4, 5, -6, -1], false⟩,
  ⟨81, 3, false, ![-6, -5, 4, -3, 2, -1], false⟩, ⟨81, 4, true, ![6, 5, -4, 3, 2, -1], true⟩,
  ⟨81, 5, false, ![4, 5, -6, 1, -2, -3], false⟩, ⟨81, 6, true, ![-4, -5, 6, 1, -2, 3], true⟩,
  ⟨49, 0, true, ![3, -4, 5, 6, -1, 2], false⟩, ⟨49, 1, false, ![-3, 4, -5, -6, -1, 2], true⟩,
  ⟨49, 2, false, ![5, 4, 3, -2, -1, -6], true⟩, ⟨49, 3, false, ![-1, 2, -3, 4, -5, 6], false⟩,
  ⟨49, 3, false, ![-6, 5, -4, 3, -2, 1], true⟩, ⟨49, 4, true, ![6, 1, 2, 3, -4, -5], false⟩,
  ⟨49, 5, true, ![-2, 1, 6, -5, -4, 3], false⟩, ⟨49, 6, false, ![-2, 1, -6, 5, 4, -3], true⟩,
  ⟨113, 0, true, ![4, -5, 6, -1, -2, -3], false⟩, ⟨113, 1, false, ![-4, 3, 2, -1, 6, 5], false⟩,
  ⟨113, 2, false, ![-2, -3, -4, -5, -6, -1], true⟩, ⟨113, 2, false, ![-5, -4, -3, -2, -1, -6], false⟩,
  ⟨113, 3, false, ![-1, 2, 3, -4, 5, 6], true⟩, ⟨113, 4, true, ![-1, 6, -5, 4, -3, -2], true⟩
]
/-- Consecutive explicit T7 placements 576 through 639. -/
def placements7_9 : List (Placement 6) := [
  ⟨113, 5, true, ![-1, -6, 5, -4, -3, -2], false⟩, ⟨113, 6, true, ![-3, -4, 5, -6, -1, -2], true⟩,
  ⟨9, 0, true, ![3, 2, -1, 6, -5, 4], true⟩, ⟨9, 1, false, ![-3, 2, -1, -6, 5, -4], false⟩,
  ⟨9, 2, false, ![-1, 2, -3, -4, 5, -6], true⟩, ⟨9, 3, true, ![-1, 2, 3, 4, -5, 6], false⟩,
  ⟨9, 4, false, ![-1, -6, -5, -4, 3, 2], false⟩, ⟨9, 5, false, ![-2, 1, 6, -5, -4, -3], false⟩,
  ⟨9, 5, false, ![-5, 6, 1, -2, -3, -4], true⟩, ⟨9, 6, false, ![-4, -5, -6, -1, 2, 3], true⟩,
  ⟨73, 0, true, ![3, -4, -5, -6, 1, -2], false⟩, ⟨73, 1, false, ![-3, 4, 5, 6, 1, -2], true⟩,
  ⟨73, 2, false, ![5, 4, -3, 2, 1, 6], true⟩, ⟨73, 3, true, ![-1, 2, -3, -4, 5, -6], false⟩,
  ⟨73, 3, true, ![-6, 5, -4, -3, 2, -1], true⟩, ⟨73, 4, false, ![6, 1, 2, -3, 4, 5], false⟩,
  ⟨73, 5, false, ![-2, 1, 6, 5, 4, -3], false⟩, ⟨73, 6, true, ![-2, 1, -6, -5, -4, 3], true⟩,
  ⟨41, 0, true, ![3, 2, -1, 6, 5, 4], false⟩, ⟨41, 1, false, ![-3, 2, -1, -6, -5, -4], true⟩,
  ⟨41, 2, false, ![-1, 2, -3, -4, -5, -6], false⟩, ⟨41, 3, true, ![-1, 2, 3, 4, 5, 6], true⟩,
  ⟨41, 4, false, ![-1, -6, -5, -4, -3, 2], true⟩, ⟨41, 5, true, ![-2, 1, 6, -5, -4, -3], true⟩,
  ⟨41, 5, true, ![-5, 6, 1, -2, -3, -4], false⟩, ⟨41, 6, false, ![-4, -5, -6, -1, 2, -3], false⟩,
  ⟨105, 0, true, ![-3, 2, -1, 6, -5, 4], false⟩, ⟨105, 0, true, ![-4, 5, -6, 1, -2, 3], true⟩,
  ⟨105, 1, false, ![-3, 4, 5, -6, -1, -2], true⟩, ⟨105, 2, false, ![5, 4, -3, 2, -1, -6], true⟩,
  ⟨105, 3, true, ![-5, -4, 3, 2, -1, 6], false⟩, ⟨105, 4, false, ![-5, -6, 1, -2, -3, 4], true⟩,
  ⟨105, 5, true, ![5, 6, 1, -2, 3, -4], false⟩, ⟨105, 6, true, ![-3, 2, 1, 6, -5, -4], false⟩,
  ⟨25, 0, true, ![-3, 2, -1, -6, 5, -4], true⟩, ⟨25, 0, true, ![-4, 5, -6, -1, 2, -3], false⟩,
  ⟨25, 1, false, ![-3, 4, 5, 6, 1, 2], false⟩, ⟨25, 2, false, ![5, 4, -3, -2, 1, 6], false⟩,
  ⟨25, 3, true, ![-5, -4, 3, -2, 1, -6], true⟩, ⟨25, 4, true, ![-5, -6, 1, -2, 3, -4], false⟩,
  ⟨25, 5, false, ![5, 6, 1, -2, -3, 4], true⟩, ⟨25, 6, false, ![-3, 2, 1, 6, 5, 4], true⟩,
  ⟨89, 0, true, ![3, 2, -1, -6, -5, -4], true⟩, ⟨89, 1, false, ![-3, 2, -1, 6, 5, 4], false⟩,
  ⟨89, 2, false, ![-1, 2, -3, 4, 5, 6], true⟩, ⟨89, 3, true, ![-1, 2, 3, -4, -5, -6], false⟩,
  ⟨89, 4, true, ![-1, -6, -5, -4, 3, -2], false⟩, ⟨89, 5, false, ![-2, 1, 6, -5, 4, 3], false⟩,
  ⟨89, 5, false, ![-5, 6, 1, -2, 3, 4], true⟩, ⟨89, 6, true, ![-4, -5, -6, -1, -2, 3], true⟩,
  ⟨57, 0, true, ![3, -4, -5, 6, -1, 2], true⟩, ⟨57, 1, false, ![-3, 4, 5, -6, -1, 2], false⟩,
  ⟨57, 2, false, ![5, 4, -3, -2, -1, -6], false⟩, ⟨57, 3, true, ![-1, 2, -3, 4, -5, 6], true⟩,
  ⟨57, 3, true, ![-6, 5, -4, 3, -2, 1], false⟩, ⟨57, 4, true, ![6, 1, 2, -3, -4, -5], true⟩,
  ⟨57, 5, true, ![-2, 1, 6, 5, -4, 3], true⟩, ⟨57, 6, false, ![-2, 1, -6, -5, 4, -3], false⟩,
  ⟨121, 0, true, ![3, 2, -1, -6, 5, -4], false⟩, ⟨121, 1, false, ![-3, 2, -1, 6, -5, 4], true⟩,
  ⟨121, 2, false, ![-1, 2, -3, 4, -5, 6], false⟩, ⟨121, 3, true, ![-1, 2, 3, -4, 5, -6], true⟩,
  ⟨121, 4, true, ![-1, -6, -5, -4, -3, -2], true⟩, ⟨121, 5, true, ![-2, 1, 6, -5, 4, 3], true⟩
]
/-- Consecutive explicit T7 placements 640 through 703. -/
def placements7_10 : List (Placement 6) := [
  ⟨121, 5, true, ![-5, 6, 1, -2, 3, 4], false⟩, ⟨121, 6, true, ![-4, -5, -6, -1, -2, -3], false⟩,
  ⟨5, 0, true, ![3, -2, 1, -6, -5, 4], false⟩, ⟨5, 1, false, ![3, 4, 5, 6, 1, 2], true⟩,
  ⟨5, 1, false, ![4, 3, 2, 1, 6, 5], false⟩, ⟨5, 2, true, ![-2, 3, 4, -5, -6, 1], true⟩,
  ⟨5, 3, false, ![-6, -5, -4, 3, 2, 1], true⟩, ⟨5, 4, false, ![6, 5, 4, 3, 2, 1], false⟩,
  ⟨5, 5, false, ![4, 5, 6, 1, 2, 3], true⟩, ⟨5, 6, false, ![-4, -5, -6, 1, 2, 3], false⟩,
  ⟨69, 0, true, ![3, -2, 1, 6, -5, -4], false⟩, ⟨69, 1, false, ![-3, -2, 1, -6, 5, 4], true⟩,
  ⟨69, 2, true, ![-1, 2, 3, -4, 5, 6], false⟩, ⟨69, 3, false, ![-1, 2, -3, 4, -5, -6], true⟩,
  ⟨69, 4, false, ![-1, -6, 5, 4, 3, -2], true⟩, ⟨69, 5, false, ![-2, 1, -6, 5, -4, 3], true⟩,
  ⟨69, 5, false, ![-5, 6, -1, 2, -3, 4], false⟩, ⟨69, 6, true, ![-4, -5, 6, 1, 2, 3], false⟩,
  ⟨37, 0, true, ![-3, -2, 1, 6, -5, -4], true⟩, ⟨37, 0, true, ![-4, -5, 6, 1, -2, -3], false⟩,
  ⟨37, 1, false, ![-3, -4, -5, -6, -1, 2], false⟩, ⟨37, 2, true, ![5, 4, 3, 2, -1, 6], false⟩,
  ⟨37, 3, false, ![-5, -4, -3, 2, -1, -6], true⟩, ⟨37, 4, false, ![-5, -6, -1, 2, -3, -4], false⟩,
  ⟨37, 5, true, ![5, 6, -1, 2, 3, 4], true⟩, ⟨37, 6, false, ![-3, 2, -1, -6, -5, -4], true⟩,
  ⟨101, 0, true, ![3, -2, 1, 6, 5, -4], true⟩, ⟨101, 1, false, ![-3, -2, 1, -6, -5, 4], false⟩,
  ⟨101, 2, true, ![-1, 2, 3, -4, -5, 6], true⟩, ⟨101, 3, false, ![-1, 2, -3, 4, 5, -6], false⟩,
  ⟨101, 4, false, ![-1, -6, 5, 4, -3, -2], false⟩, ⟨101, 5, true, ![-2, 1, -6, 5, -4, 3], false⟩,
  ⟨101, 5, true, ![-5, 6, -1, 2, -3, 4], true⟩, ⟨101, 6, true, ![-4, -5, 6, 1, 2, -3], true⟩,
  ⟨21, 0, true, ![4, 5, 6, -1, 2, 3], true⟩, ⟨21, 1, false, ![-4, -3, 2, -1, -6, -5], true⟩,
  ⟨21, 2, true, ![-2, -3, -4, -5, 6, 1], false⟩, ⟨21, 2, true, ![-5, -4, -3, -2, 1, 6], true⟩,
  ⟨21, 3, false, ![-1, 2, -3, -4, -5, -6], false⟩, ⟨21, 4, true, ![-1, 6, 5, 4, 3, 2], false⟩,
  ⟨21, 5, false, ![-1, -6, -5, -4, -3, 2], true⟩, ⟨21, 6, false, ![-3, -4, -5, -6, -1, 2], false⟩,
  ⟨85, 0, true, ![3, 4, 5, 6, 1, -2], true⟩, ⟨85, 1, false, ![-3, -4, -5, -6, 1, -2], false⟩,
  ⟨85, 2, true, ![5, 4, 3, -2, 1, 6], false⟩, ⟨85, 3, false, ![-1, 2, 3, 4, 5, -6], true⟩,
  ⟨85, 3, false, ![-6, 5, 4, 3, 2, -1], false⟩, ⟨85, 4, true, ![6, 1, -2, 3, 4, 5], true⟩,
  ⟨85, 5, false, ![-2, 1, -6, -5, -4, -3], true⟩, ⟨85, 6, true, ![-2, 1, 6, 5, 4, 3], false⟩,
  ⟨53, 0, true, ![3, -2, 1, 6, 5, 4], false⟩, ⟨53, 1, false, ![3, 4, 5, -6, -1, 2], true⟩,
  ⟨53, 1, false, ![4, 3, 2, -1, -6, 5], false⟩, ⟨53, 2, true, ![-2, 3, 4, 5, 6, 1], true⟩,
  ⟨53, 3, false, ![-6, -5, -4, -3, -2, 1], true⟩, ⟨53, 4, true, ![6, 5, 4, 3, -2, 1], false⟩,
  ⟨53, 5, true, ![4, 5, 6, 1, -2, 3], true⟩, ⟨53, 6, false, ![-4, -5, -6, 1, -2, -3], false⟩,
  ⟨117, 0, true, ![4, 5, 6, -1, -2, -3], true⟩, ⟨117, 1, false, ![-4, -3, 2, -1, 6, 5], true⟩,
  ⟨117, 2, true, ![-2, -3, -4, -5, -6, -1], false⟩, ⟨117, 2, true, ![-5, -4, -3, -2, -1, -6], true⟩,
  ⟨117, 3, false, ![-1, 2, -3, -4, 5, 6], false⟩, ⟨117, 4, true, ![-1, 6, 5, 4, -3, -2], false⟩
]
/-- Consecutive explicit T7 placements 704 through 767. -/
def placements7_11 : List (Placement 6) := [
  ⟨117, 5, true, ![-1, -6, -5, -4, -3, -2], true⟩, ⟨117, 6, true, ![-3, -4, -5, -6, -1, -2], false⟩,
  ⟨13, 0, true, ![2, -1, 6, 5, -4, 3], true⟩, ⟨13, 1, false, ![-2, -3, 4, 5, -6, 1], false⟩,
  ⟨13, 2, true, ![-2, 3, -4, -5, 6, 1], true⟩, ⟨13, 3, true, ![6, -5, -4, 3, 2, 1], true⟩,
  ⟨13, 4, false, ![-1, 6, -5, 4, -3, 2], true⟩, ⟨13, 4, false, ![-6, 1, -2, 3, -4, 5], false⟩,
  ⟨13, 5, false, ![5, -6, -1, -2, 3, 4], false⟩, ⟨13, 6, false, ![-3, 2, -1, -6, -5, 4], false⟩,
  ⟨77, 0, true, ![3, -2, -1, -6, -5, -4], false⟩, ⟨77, 1, false, ![3, 4, -5, 6, 1, -2], true⟩,
  ⟨77, 1, false, ![4, 3, -2, 1, 6, -5], false⟩, ⟨77, 2, true, ![-2, 3, -4, -5, -6, -1], true⟩,
  ⟨77, 3, true, ![-6, -5, -4, 3, 2, -1], true⟩, ⟨77, 4, false, ![6, 5, 4, -3, 2, -1], false⟩,
  ⟨77, 5, false, ![4, 5, 6, -1, 2, -3], true⟩, ⟨77, 6, true, ![-4, -5, -6, -1, 2, 3], false⟩,
  ⟨45, 0, true, ![4, 5, 6, 1, -2, 3], true⟩, ⟨45, 1, false, ![-4, -3, -2, 1, -6, -5], true⟩,
  ⟨45, 2, true, ![4, 3, -2, 1, 6, 5], false⟩, ⟨45, 3, true, ![6, 1, -2, 3, 4, 5], true⟩,
  ⟨45, 4, false, ![-6, 1, -2, -3, -4, -5], false⟩, ⟨45, 5, true, ![-2, 1, 6, 5, 4, 3], false⟩,
  ⟨45, 6, false, ![3, 2, -1, -6, 5, 4], false⟩, ⟨45, 6, false, ![4, 5, -6, -1, 2, 3], true⟩,
  ⟨109, 0, true, ![4, 5, 6, 1, -2, -3], false⟩, ⟨109, 1, false, ![-4, -3, -2, 1, -6, 5], false⟩,
  ⟨109, 2, true, ![4, 3, -2, 1, 6, -5], true⟩, ⟨109, 3, true, ![6, 1, -2, 3, 4, -5], false⟩,
  ⟨109, 4, false, ![-6, 1, -2, -3, -4, 5], true⟩, ⟨109, 5, true, ![-2, 1, 6, 5, 4, -3], true⟩,
  ⟨109, 6, true, ![3, 2, -1, -6, 5, 4], true⟩, ⟨109, 6, true, ![4, 5, -6, -1, 2, 3], false⟩,
  ⟨29, 0, true, ![2, -1, 6, -5, -4, 3], false⟩, ⟨29, 1, false, ![-2, -3, 4, -5, -6, 1], true⟩,
  ⟨29, 2, true, ![-2, 3, -4, 5, 6, 1], false⟩, ⟨29, 3, true, ![6, -5, -4, -3, 2, 1], false⟩,
  ⟨29, 4, true, ![-1, 6, -5, 4, -3, 2], false⟩, ⟨29, 4, true, ![-6, 1, -2, 3, -4, 5], true⟩,
  ⟨29, 5, false, ![5, -6, -1, -2, -3, 4], true⟩, ⟨29, 6, false, ![-3, 2, -1, -6, 5, 4], true⟩,
  ⟨93, 0, true, ![3, 4, -5, 6, 1, -2], false⟩, ⟨93, 1, false, ![-3, -4, 5, -6, 1, -2], true⟩,
  ⟨93, 2, true, ![5, 4, -3, -2, 1, 6], true⟩, ⟨93, 3, true, ![-1, 2, 3, 4, 5, -6], false⟩,
  ⟨93, 3, true, ![-6, 5, 4, 3, 2, -1], true⟩, ⟨93, 4, true, ![6, 1, -2, -3, 4, 5], false⟩,
  ⟨93, 5, false, ![-2, 1, -6, 5, -4, -3], false⟩, ⟨93, 6, true, ![-2, 1, 6, -5, 4, 3], true⟩,
  ⟨61, 0, true, ![-3, -2, -1, -6, -5, -4], true⟩, ⟨61, 0, true, ![-4, -5, -6, -1, -2, -3], false⟩,
  ⟨61, 1, false, ![-3, -4, 5, 6, -1, 2], false⟩, ⟨61, 2, true, ![5, 4, -3, -2, -1, 6], false⟩,
  ⟨61, 3, true, ![-5, -4, -3, -2, -1, -6], true⟩, ⟨61, 4, true, ![-5, -6, -1, -2, -3, -4], false⟩,
  ⟨61, 5, true, ![5, 6, -1, -2, -3, 4], true⟩, ⟨61, 6, false, ![-3, 2, -1, 6, 5, -4], true⟩,
  ⟨125, 0, true, ![3, -2, -1, 6, 5, -4], false⟩, ⟨125, 1, false, ![3, 4, -5, -6, -1, -2], true⟩,
  ⟨125, 1, false, ![4, 3, -2, -1, -6, -5], false⟩, ⟨125, 1, true, ![3, 4, -5, -6, 1, 2], false⟩,
  ⟨125, 2, true, ![-2, 3, -4, 5, 6, -1], true⟩, ⟨125, 3, true, ![-6, -5, -4, -3, -2, -1], true⟩
]
/-- Consecutive explicit T7 placements 768 through 831. -/
def placements7_12 : List (Placement 6) := [
  ⟨125, 4, true, ![6, 5, 4, -3, -2, -1], false⟩, ⟨125, 5, true, ![4, 5, 6, -1, -2, -3], true⟩,
  ⟨125, 6, true, ![-4, -5, -6, -1, -2, -3], false⟩, ⟨3, 0, true, ![-2, 1, -6, 5, -4, 3], false⟩,
  ⟨3, 1, true, ![-2, 3, -4, 5, -6, 1], true⟩, ⟨3, 2, false, ![-2, -3, 4, -5, 6, 1], false⟩,
  ⟨3, 3, false, ![6, 5, 4, 3, 2, 1], false⟩, ⟨3, 4, false, ![-1, -6, 5, -4, -3, 2], false⟩,
  ⟨3, 4, false, ![-6, -1, 2, -3, -4, 5], true⟩, ⟨3, 5, false, ![5, 6, 1, 2, 3, 4], true⟩,
  ⟨3, 6, false, ![-3, -2, 1, 6, -5, 4], true⟩, ⟨67, 0, true, ![3, 2, 1, 6, 5, 4], true⟩,
  ⟨67, 0, true, ![4, 5, 6, 1, 2, 3], false⟩, ⟨67, 1, true, ![-3, 4, -5, -6, 1, -2], false⟩,
  ⟨67, 2, false, ![5, -4, 3, 2, 1, -6], false⟩, ⟨67, 3, false, ![-5, 4, 3, 2, 1, 6], true⟩,
  ⟨67, 4, false, ![-5, 6, 1, 2, 3, 4], false⟩, ⟨67, 5, false, ![5, -6, 1, 2, 3, -4], true⟩,
  ⟨67, 6, true, ![-3, -2, 1, -6, -5, 4], true⟩, ⟨35, 0, true, ![-4, -5, 6, 1, -2, 3], true⟩,
  ⟨35, 1, true, ![-4, 3, 2, 1, 6, -5], true⟩, ⟨35, 2, false, ![-2, 3, -4, 5, -6, 1], false⟩,
  ⟨35, 2, false, ![-5, 4, -3, 2, -1, 6], true⟩, ⟨35, 3, false, ![-1, -2, 3, 4, 5, -6], false⟩,
  ⟨35, 4, false, ![-1, -6, -5, 4, -3, 2], false⟩, ⟨35, 5, true, ![-1, 6, 5, -4, 3, 2], true⟩,
  ⟨35, 6, false, ![-3, 4, 5, -6, 1, -2], false⟩, ⟨99, 0, true, ![-3, -4, 5, -6, -1, -2], true⟩,
  ⟨99, 1, true, ![-3, 4, -5, 6, -1, -2], false⟩, ⟨99, 2, false, ![5, -4, 3, 2, -1, 6], false⟩,
  ⟨99, 3, false, ![-1, -2, -3, -4, -5, -6], true⟩, ⟨99, 3, false, ![-6, -5, -4, -3, -2, -1], false⟩,
  ⟨99, 4, false, ![6, -1, 2, 3, -4, 5], true⟩, ⟨99, 5, true, ![-2, -1, 6, -5, 4, -3], true⟩,
  ⟨99, 6, true, ![-2, -1, -6, 5, -4, -3], false⟩, ⟨19, 0, true, ![-2, 1, -6, -5, -4, 3], true⟩,
  ⟨19, 1, true, ![-2, 3, -4, -5, -6, 1], false⟩, ⟨19, 2, false, ![-2, -3, 4, 5, 6, 1], true⟩,
  ⟨19, 3, false, ![6, 5, 4, -3, 2, 1], true⟩, ⟨19, 4, true, ![-1, -6, 5, -4, -3, 2], true⟩,
  ⟨19, 4, true, ![-6, -1, 2, -3, -4, 5], false⟩, ⟨19, 5, false, ![5, 6, 1, 2, -3, 4], false⟩,
  ⟨19, 6, false, ![-3, -2, 1, 6, 5, 4], false⟩, ⟨83, 0, true, ![-3, 2, 1, 6, -5, -4], false⟩,
  ⟨83, 1, true, ![3, -4, 5, -6, 1, -2], true⟩, ⟨83, 1, true, ![4, -3, 2, -1, 6, -5], false⟩,
  ⟨83, 2, false, ![-2, -3, 4, 5, -6, -1], true⟩, ⟨83, 3, false, ![-6, 5, 4, -3, 2, -1], true⟩,
  ⟨83, 4, true, ![6, -5, -4, 3, 2, -1], false⟩, ⟨83, 5, false, ![4, -5, -6, 1, -2, -3], true⟩,
  ⟨83, 6, true, ![-4, 5, 6, 1, -2, 3], false⟩, ⟨51, 0, true, ![-4, -5, -6, -1, -2, 3], true⟩,
  ⟨51, 1, true, ![-4, 3, 2, -1, -6, -5], true⟩, ⟨51, 2, false, ![4, -3, 2, -1, 6, 5], false⟩,
  ⟨51, 3, false, ![6, -1, 2, -3, 4, 5], true⟩, ⟨51, 4, true, ![-6, -1, 2, 3, -4, -5], false⟩,
  ⟨51, 5, true, ![-2, -1, -6, -5, -4, 3], false⟩, ⟨51, 6, false, ![3, -2, 1, 6, -5, 4], false⟩,
  ⟨51, 6, false, ![4, -5, 6, 1, -2, 3], true⟩, ⟨115, 0, true, ![-4, -5, -6, -1, -2, -3], false⟩,
  ⟨115, 1, true, ![-4, 3, 2, -1, -6, 5], false⟩, ⟨115, 2, false, ![4, -3, 2, -1, 6, -5], true⟩,
  ⟨115, 3, false, ![6, -1, 2, -3, 4, -5], false⟩, ⟨115, 4, true, ![-6, -1, 2, 3, -4, 5], true⟩
]
/-- Consecutive explicit T7 placements 832 through 895. -/
def placements7_13 : List (Placement 6) := [
  ⟨115, 5, true, ![-2, -1, -6, -5, -4, -3], true⟩, ⟨115, 6, true, ![3, -2, 1, 6, -5, 4], true⟩,
  ⟨115, 6, true, ![4, -5, 6, 1, -2, 3], false⟩, ⟨11, 0, true, ![-4, -5, 6, 1, 2, 3], false⟩,
  ⟨11, 1, true, ![-4, 3, -2, 1, 6, -5], false⟩, ⟨11, 2, false, ![4, -3, -2, 1, -6, 5], true⟩,
  ⟨11, 3, true, ![6, -1, 2, 3, -4, 5], false⟩, ⟨11, 4, false, ![-6, -1, 2, -3, 4, -5], true⟩,
  ⟨11, 5, false, ![-2, -1, -6, 5, 4, 3], true⟩, ⟨11, 6, false, ![3, -2, 1, -6, 5, -4], true⟩,
  ⟨11, 6, false, ![4, -5, 6, -1, 2, -3], false⟩, ⟨75, 0, true, ![-4, -5, 6, 1, 2, -3], true⟩,
  ⟨75, 1, true, ![-4, 3, -2, 1, 6, 5], true⟩, ⟨75, 2, false, ![4, -3, -2, 1, -6, -5], false⟩,
  ⟨75, 3, true, ![6, -1, 2, 3, -4, -5], true⟩, ⟨75, 4, false, ![-6, -1, 2, -3, 4, 5], false⟩,
  ⟨75, 5, false, ![-2, -1, -6, 5, 4, -3], false⟩, ⟨75, 6, true, ![3, -2, 1, -6, 5, -4], false⟩,
  ⟨75, 6, true, ![4, -5, 6, -1, 2, -3], true⟩, ⟨43, 0, true, ![-2, 1, 6, 5, 4, 3], false⟩,
  ⟨43, 1, true, ![-2, 3, 4, 5, 6, 1], true⟩, ⟨43, 2, false, ![-2, -3, -4, -5, -6, 1], false⟩,
  ⟨43, 3, true, ![6, 5, 4, 3, -2, 1], false⟩, ⟨43, 4, false, ![-1, -6, 5, 4, 3, 2], false⟩,
  ⟨43, 4, false, ![-6, -1, 2, 3, 4, 5], true⟩, ⟨43, 5, true, ![5, 6, 1, -2, 3, 4], true⟩,
  ⟨43, 6, false, ![-3, -2, 1, -6, -5, -4], true⟩, ⟨107, 0, true, ![-3, -4, -5, -6, -1, -2], false⟩,
  ⟨107, 1, true, ![-3, 4, 5, 6, -1, -2], true⟩, ⟨107, 2, false, ![5, -4, -3, 2, -1, 6], true⟩,
  ⟨107, 3, true, ![-1, -2, -3, -4, -5, -6], false⟩, ⟨107, 3, true, ![-6, -5, -4, -3, -2, -1], true⟩,
  ⟨107, 4, false, ![6, -1, 2, -3, -4, 5], false⟩, ⟨107, 5, true, ![-2, -1, 6, 5, 4, -3], false⟩,
  ⟨107, 6, true, ![-2, -1, -6, -5, -4, -3], true⟩, ⟨27, 0, true, ![-4, -5, -6, -1, 2, 3], false⟩,
  ⟨27, 1, true, ![-4, 3, -2, -1, -6, -5], false⟩, ⟨27, 2, false, ![-2, 3, 4, -5, 6, 1], true⟩,
  ⟨27, 2, false, ![-5, 4, 3, -2, 1, 6], false⟩, ⟨27, 3, true, ![-1, -2, 3, -4, -5, -6], true⟩,
  ⟨27, 4, true, ![-1, -6, -5, -4, 3, 2], true⟩, ⟨27, 5, false, ![-1, 6, 5, 4, -3, 2], false⟩,
  ⟨27, 6, false, ![-3, 4, 5, 6, -1, 2], true⟩, ⟨91, 0, true, ![3, 2, -1, -6, 5, 4], true⟩,
  ⟨91, 0, true, ![4, 5, -6, -1, 2, 3], false⟩, ⟨91, 1, true, ![-3, 4, 5, 6, 1, -2], false⟩,
  ⟨91, 2, false, ![5, -4, -3, -2, 1, -6], false⟩, ⟨91, 3, true, ![-5, 4, 3, -2, 1, 6], true⟩,
  ⟨91, 4, true, ![-5, 6, 1, -2, 3, 4], false⟩, ⟨91, 5, false, ![5, -6, 1, -2, -3, -4], true⟩,
  ⟨91, 6, true, ![-3, -2, 1, 6, 5, 4], true⟩, ⟨59, 0, true, ![-2, 1, 6, -5, 4, 3], true⟩,
  ⟨59, 1, true, ![-2, 3, 4, -5, 6, 1], false⟩, ⟨59, 2, false, ![-2, -3, -4, 5, -6, 1], true⟩,
  ⟨59, 3, true, ![6, 5, 4, -3, -2, 1], true⟩, ⟨59, 4, true, ![-1, -6, 5, 4, 3, 2], true⟩,
  ⟨59, 4, true, ![-6, -1, 2, 3, 4, 5], false⟩, ⟨59, 5, true, ![5, 6, 1, -2, -3, 4], false⟩,
  ⟨59, 6, false, ![-3, -2, 1, -6, 5, -4], false⟩, ⟨123, 0, true, ![-4, -5, -6, -1, -2, -3], false⟩,
  ⟨123, 1, true, ![-4, 3, -2, -1, 6, 5], false⟩, ⟨123, 2, false, ![-2, 3, 4, -5, -6, -1], true⟩,
  ⟨123, 2, false, ![-5, 4, 3, -2, -1, -6], false⟩, ⟨123, 2, true, ![-5, 4, 3, 2, 1, 6], false⟩
]
/-- Consecutive explicit T7 placements 896 through 959. -/
def placements7_14 : List (Placement 6) := [
  ⟨123, 3, true, ![-1, -2, 3, -4, 5, 6], true⟩, ⟨123, 4, true, ![-1, -6, -5, -4, -3, -2], true⟩,
  ⟨123, 5, true, ![-1, 6, 5, 4, -3, -2], false⟩, ⟨123, 6, true, ![-3, 4, 5, 6, -1, -2], true⟩,
  ⟨7, 0, true, ![-3, -2, 1, -6, -5, 4], true⟩, ⟨7, 1, true, ![3, 4, 5, 6, 1, 2], false⟩,
  ⟨7, 1, true, ![4, 3, 2, 1, 6, 5], true⟩, ⟨7, 2, true, ![-2, -3, 4, -5, -6, 1], false⟩,
  ⟨7, 3, false, ![-6, 5, -4, 3, 2, 1], false⟩, ⟨7, 4, false, ![6, -5, 4, 3, 2, 1], true⟩,
  ⟨7, 5, false, ![4, -5, 6, 1, 2, 3], false⟩, ⟨7, 6, false, ![-4, 5, -6, 1, 2, 3], true⟩,
  ⟨71, 0, true, ![-2, -1, -6, 5, -4, -3], false⟩, ⟨71, 1, true, ![-2, -3, -4, 5, -6, -1], true⟩,
  ⟨71, 2, true, ![-2, -3, 4, -5, 6, -1], false⟩, ⟨71, 3, false, ![6, 5, -4, 3, 2, -1], false⟩,
  ⟨71, 4, false, ![-1, -6, -5, -4, -3, -2], false⟩, ⟨71, 4, false, ![-6, -1, -2, -3, -4, -5], true⟩,
  ⟨71, 5, false, ![5, 6, -1, 2, 3, -4], true⟩, ⟨71, 6, true, ![-3, -2, -1, 6, -5, 4], true⟩,
  ⟨39, 0, true, ![-4, 5, 6, 1, -2, 3], false⟩, ⟨39, 1, true, ![-4, -3, 2, 1, 6, -5], false⟩,
  ⟨39, 2, true, ![-2, 3, -4, 5, -6, 1], true⟩, ⟨39, 2, true, ![-5, 4, -3, 2, -1, 6], false⟩,
  ⟨39, 3, false, ![-1, -2, -3, 4, 5, -6], true⟩, ⟨39, 4, false, ![-1, -6, 5, 4, -3, 2], true⟩,
  ⟨39, 5, true, ![-1, 6, -5, -4, 3, 2], false⟩, ⟨39, 6, false, ![-3, 4, -5, -6, 1, -2], true⟩,
  ⟨103, 0, true, ![3, -2, 1, 6, -5, 4], true⟩, ⟨103, 0, true, ![4, -5, 6, 1, -2, 3], false⟩,
  ⟨103, 1, true, ![-3, -4, -5, -6, -1, -2], false⟩, ⟨103, 2, true, ![5, -4, 3, 2, -1, -6], false⟩,
  ⟨103, 3, false, ![-5, 4, -3, 2, -1, 6], true⟩, ⟨103, 4, false, ![-5, 6, -1, 2, -3, 4], false⟩,
  ⟨103, 5, true, ![5, -6, -1, 2, 3, -4], true⟩, ⟨103, 6, true, ![-3, -2, -1, -6, -5, -4], true⟩,
  ⟨23, 0, true, ![3, -2, 1, -6, 5, -4], false⟩, ⟨23, 0, true, ![4, -5, 6, -1, 2, -3], true⟩,
  ⟨23, 1, true, ![-3, -4, -5, 6, 1, 2], true⟩, ⟨23, 2, true, ![5, -4, 3, -2, 1, 6], true⟩,
  ⟨23, 3, false, ![-5, 4, -3, -2, 1, -6], false⟩, ⟨23, 4, true, ![-5, 6, -1, 2, 3, -4], true⟩,
  ⟨23, 5, false, ![5, -6, -1, 2, -3, 4], false⟩, ⟨23, 6, false, ![-3, -2, -1, -6, 5, 4], false⟩,
  ⟨87, 0, true, ![-2, -1, -6, -5, -4, -3], true⟩, ⟨87, 1, true, ![-2, -3, -4, -5, -6, -1], false⟩,
  ⟨87, 2, true, ![-2, -3, 4, 5, 6, -1], true⟩, ⟨87, 3, false, ![6, 5, -4, -3, 2, -1], true⟩,
  ⟨87, 4, true, ![-1, -6, -5, -4, -3, -2], true⟩, ⟨87, 4, true, ![-6, -1, -2, -3, -4, -5], false⟩,
  ⟨87, 5, false, ![5, 6, -1, 2, -3, -4], false⟩, ⟨87, 6, true, ![-3, -2, -1, 6, 5, 4], false⟩,
  ⟨55, 0, true, ![-3, -2, 1, 6, 5, 4], true⟩, ⟨55, 1, true, ![3, 4, 5, -6, -1, 2], false⟩,
  ⟨55, 1, true, ![4, 3, 2, -1, -6, 5], true⟩, ⟨55, 2, true, ![-2, -3, 4, 5, 6, 1], false⟩,
  ⟨55, 3, false, ![-6, 5, -4, -3, -2, 1], false⟩, ⟨55, 4, true, ![6, -5, 4, 3, -2, 1], true⟩,
  ⟨55, 5, true, ![4, -5, 6, 1, -2, 3], false⟩, ⟨55, 6, false, ![-4, 5, -6, 1, -2, -3], true⟩,
  ⟨119, 0, true, ![-3, 4, 5, 6, -1, -2], true⟩, ⟨119, 1, true, ![-3, -4, -5, -6, -1, -2], false⟩,
  ⟨119, 2, true, ![5, -4, 3, -2, -1, 6], false⟩, ⟨119, 3, false, ![-1, -2, 3, 4, -5, -6], true⟩
]
/-- Consecutive explicit T7 placements 960 through 1023. -/
def placements7_15 : List (Placement 6) := [
  ⟨119, 3, false, ![-6, -5, 4, 3, -2, -1], false⟩, ⟨119, 3, true, ![5, -4, 3, 2, 1, -6], true⟩,
  ⟨119, 4, true, ![6, -1, -2, 3, -4, 5], true⟩, ⟨119, 5, true, ![-2, -1, -6, -5, -4, -3], true⟩,
  ⟨119, 6, true, ![-2, -1, 6, 5, 4, -3], false⟩, ⟨15, 0, true, ![-3, -2, -1, 6, -5, 4], true⟩,
  ⟨15, 1, true, ![-3, -2, -1, -6, 5, -4], false⟩, ⟨15, 2, true, ![-1, -2, -3, -4, 5, -6], true⟩,
  ⟨15, 3, true, ![-1, -2, -3, 4, -5, 6], false⟩, ⟨15, 4, false, ![-1, 6, 5, -4, 3, 2], false⟩,
  ⟨15, 5, false, ![-2, -1, -6, -5, -4, -3], false⟩, ⟨15, 5, false, ![-5, -6, -1, -2, -3, -4], true⟩,
  ⟨15, 6, false, ![-4, 5, 6, -1, 2, 3], true⟩, ⟨79, 0, true, ![-3, -2, -1, -6, -5, -4], true⟩,
  ⟨79, 1, true, ![3, 4, -5, 6, 1, -2], false⟩, ⟨79, 1, true, ![4, 3, -2, 1, 6, -5], true⟩,
  ⟨79, 2, true, ![-2, -3, -4, -5, -6, -1], false⟩, ⟨79, 3, true, ![-6, 5, -4, 3, 2, -1], false⟩,
  ⟨79, 4, false, ![6, -5, 4, -3, 2, -1], true⟩, ⟨79, 5, false, ![4, -5, 6, -1, 2, -3], false⟩,
  ⟨79, 6, true, ![-4, 5, -6, -1, 2, 3], true⟩, ⟨47, 0, true, ![-3, -2, -1, 6, 5, 4], false⟩,
  ⟨47, 1, true, ![-3, -2, -1, -6, -5, -4], true⟩, ⟨47, 2, true, ![-1, -2, -3, -4, -5, -6], false⟩,
  ⟨47, 3, true, ![-1, -2, -3, 4, 5, 6], true⟩, ⟨47, 4, false, ![-1, 6, 5, -4, -3, 2], true⟩,
  ⟨47, 5, true, ![-2, -1, -6, -5, -4, -3], true⟩, ⟨47, 5, true, ![-5, -6, -1, -2, -3, -4], false⟩,
  ⟨47, 6, false, ![-4, 5, 6, -1, 2, -3], false⟩, ⟨111, 0, true, ![-2, -1, 6, 5, 4, -3], false⟩,
  ⟨111, 1, true, ![-2, -3, 4, 5, 6, -1], true⟩, ⟨111, 2, true, ![-2, -3, -4, -5, -6, -1], false⟩,
  ⟨111, 3, true, ![6, 5, -4, 3, -2, -1], false⟩, ⟨111, 4, false, ![-1, -6, -5, 4, 3, -2], false⟩,
  ⟨111, 4, false, ![-6, -1, -2, 3, 4, -5], true⟩, ⟨111, 4, true, ![5, -6, 1, 2, 3, -4], false⟩,
  ⟨111, 5, true, ![5, 6, -1, -2, 3, -4], true⟩, ⟨111, 6, true, ![-3, -2, -1, -6, -5, -4], true⟩,
  ⟨31, 0, true, ![-4, 5, -6, -1, 2, 3], true⟩, ⟨31, 1, true, ![-4, -3, -2, -1, -6, -5], true⟩,
  ⟨31, 2, true, ![-2, 3, 4, -5, 6, 1], false⟩, ⟨31, 2, true, ![-5, 4, 3, -2, 1, 6], true⟩,
  ⟨31, 3, true, ![-1, -2, -3, -4, -5, -6], false⟩, ⟨31, 4, true, ![-1, -6, 5, -4, 3, 2], false⟩,
  ⟨31, 5, false, ![-1, 6, -5, 4, -3, 2], true⟩, ⟨31, 6, false, ![-3, 4, -5, 6, -1, 2], false⟩,
  ⟨95, 0, true, ![-3, -2, -1, -6, -5, -4], true⟩, ⟨95, 1, true, ![-3, -2, -1, 6, 5, 4], false⟩,
  ⟨95, 2, true, ![-1, -2, -3, 4, 5, 6], true⟩, ⟨95, 3, true, ![-1, -2, -3, -4, -5, -6], false⟩,
  ⟨95, 4, true, ![-1, 6, 5, -4, 3, -2], false⟩, ⟨95, 5, false, ![-2, -1, -6, -5, 4, 3], false⟩,
  ⟨95, 5, false, ![-5, -6, -1, -2, 3, 4], true⟩, ⟨95, 5, true, ![-5, 6, 1, 2, 3, 4], true⟩,
  ⟨95, 6, true, ![-4, 5, 6, -1, -2, 3], true⟩, ⟨63, 0, true, ![-4, 5, 6, -1, -2, 3], true⟩,
  ⟨63, 1, true, ![-4, -3, -2, -1, -6, -5], true⟩, ⟨63, 2, true, ![4, -3, -2, -1, 6, 5], false⟩,
  ⟨63, 3, true, ![6, -1, -2, -3, 4, 5], true⟩, ⟨63, 4, true, ![-6, -1, -2, -3, -4, -5], false⟩,
  ⟨63, 5, true, ![-2, -1, 6, 5, -4, 3], false⟩, ⟨63, 6, false, ![3, -2, -1, -6, -5, 4], false⟩,
  ⟨63, 6, false, ![4, -5, -6, -1, -2, 3], true⟩, ⟨63, 6, true, ![3, 2, 1, -6, -5, 4], true⟩
]
/-- All 1024 exact T7 key placements, in pinned source order. -/
def placements7 : List (Placement 6) := placements7_0 ++ placements7_1 ++ placements7_2 ++ placements7_3 ++ placements7_4 ++ placements7_5 ++ placements7_6 ++ placements7_7 ++ placements7_8 ++ placements7_9 ++ placements7_10 ++ placements7_11 ++ placements7_12 ++ placements7_13 ++ placements7_14 ++ placements7_15

/-- Embed exact rational coordinates into Euclidean space. -/
noncomputable def rationalPoint {d : ℕ} (q : Fin d → ℚ) : Point d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (q i : ℝ))
/-- Closed base box; its normal half-width is zero. -/
def keyBase {d : ℕ} (k : Key d) : Set (Point d) :=
  {x | ∀ i, |x i - (k.centre i : ℝ)| ≤ (k.radius i : ℝ)}
/-- Closed convex pyramid, including its boundary. -/
def keySolid {d : ℕ} (k : Key d) : Set (Point d) :=
  convexHull ℝ (insert (rationalPoint k.apex) (keyBase k))
/-- Closed binary chair: all 2^d unit cubes except the upper all-one cube. -/
def carrier (d : ℕ) : Set (Point d) :=
  {x | ∃ c : Fin d → Bool, (∃ i, c i = false) ∧
    ∀ i, (if c i then (1 : ℝ) else 0) ≤ x i ∧ x i ≤ (if c i then (1 : ℝ) else 0) + 1}
/-- Union of the explicitly selected added or removed pyramids. -/
def keyUnion {d : ℕ} (ks : List (Key d)) (b : Bool) : Set (Point d) :=
  {x | ∃ k ∈ ks, k.bump = b ∧ x ∈ keySolid k}
/-- Add closed bumps, remove closed dents, then restore the boundary by closure. -/
def body {d : ℕ} (ks : List (Key d)) : Set (Point d) :=
  closure ((carrier d ∪ keyUnion ks true) \ keyUnion ks false)
/-- Exact proposed T5 body, at normal key height 1/240. -/
def T5 : Set (Point 5) := body (placements5.map (placedKey widths5 offsets5))
/-- Exact proposed T7 body, at normal key height 1/336. -/
def T7 : Set (Point 7) := body (placements7.map (placedKey widths7 offsets7))

/-- Physical tiling by arbitrary Euclidean isometric copies, reflections allowed.
Coverage is pointwise and distinct tile interiors must be disjoint. -/
def IsTiling {d : ℕ} (T : Set (Point d)) (tiles : Set (Set (Point d))) : Prop :=
  (∀ A ∈ tiles, ∃ g : Point d ≃ᵢ Point d, A = g '' T) ∧
  (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
  (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))
/-- Translation of one physical tile as a set. -/
def translate {d : ℕ} (v : Point d) (A : Set (Point d)) : Set (Point d) :=
  (fun x => x + v) '' A
/-- A period preserves the tile collection, not merely its union. -/
def IsPeriod {d : ℕ} (tiles : Set (Set (Point d))) (v : Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ translate v A ∈ tiles
/-- Compactness, at least one actual tiling, and no nonzero period in any tiling.
No registration, matching-law, hierarchy, or finite-certificate hypothesis occurs. -/
def IsAperiodicMonotile {d : ℕ} (T : Set (Point d)) : Prop :=
  IsCompact T ∧ (∃ tiles, IsTiling T tiles) ∧
  (∀ tiles, IsTiling T tiles → ∀ v, IsPeriod tiles v → v = 0)

/-- Intended main T5 theorem type. UNPROVED: this declaration asserts no theorem. -/
def T5Claim : Prop := IsAperiodicMonotile T5
/-- Intended main T7 theorem type. UNPROVED: this declaration asserts no theorem. -/
def T7Claim : Prop := IsAperiodicMonotile T7

end PalomarMonotiles
