module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.SetTheory.Cardinal.Finite
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Exact CLARK body and full Euclidean symmetry bound: separate extension draft

This independent statement retains the exact frozen T5 body definitions.
Its single theorem hole is confined to Challenge. This separate stronger
statement and Solution require fresh checks and a new full official preflight;
they do not change the existing running submission.

Only Lean core and Mathlib are imported. Each placement is an explicit tuple
(cell mask, normal axis, positive outward side, signed tangential labels, bump).
The cell mask is ordinary binary: coordinate i is its ith least significant bit.
Tangential coordinates are the remaining axes in increasing order. A signed
label ±j means the jth reference coordinate with the indicated sign, 1-based.
Thus these are geometric placement tables, not a hash or an opaque data blob.
All 256 records preserve the order in the exact pinned S54 T5 input.
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
  if hi : i.val < a.val then
    ⟨i.val, Nat.lt_of_lt_of_le hi (Nat.le_of_lt_succ a.isLt)⟩
  else
    ⟨i.val - 1,
      Nat.lt_of_lt_of_le
        (Nat.sub_lt
          (Nat.lt_of_le_of_lt (Nat.zero_le a.val)
            (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hi)
              (fun he => h (Fin.ext he.symm))))
          (Nat.zero_lt_succ 0))
        (Nat.le_of_lt_succ i.isLt)⟩

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

/-- Exact T5 target proposition; a definition alone asserts no proof. -/
def T5Claim : Prop := IsAperiodicMonotile T5
/-- All Euclidean isometries preserving the physical tile collection, with
no prescribed centre, orientation, lattice, or registered-frame restriction. -/
def IsEuclideanSymmetry {d : ℕ} (tiles : Set (Set (Point d)))
    (f : Point d ≃ᵢ Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ f '' A ∈ tiles

/-- The full symmetry type, including arbitrary rotations, reflections and translations. -/
def EuclideanSymmetries {d : ℕ} (tiles : Set (Set (Point d))) :=
  {f : Point d ≃ᵢ Point d // IsEuclideanSymmetry tiles f}

/-- Retain the original compactness/existence/no-period claim and add a uniform
finite bound for the full Euclidean symmetry group of every physical tiling.
The bound is 2^5 * 5! = 3840; trivial symmetry is not asserted. -/
def T5StrongClaim : Prop :=
  T5Claim ∧ ∀ tiles : Set (Set (Point 5)), IsTiling T5 tiles →
    Finite (EuclideanSymmetries tiles) ∧ Nat.card (EuclideanSymmetries tiles) ≤ 3840

/-- The deliberate Challenge-only theorem placeholder for the stronger entry. -/
theorem T5_strongAperiodicity : T5StrongClaim := by
  sorry

end PalomarMonotiles
