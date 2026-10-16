/- SOURCE-ONLY CONTRACT DRAFT, 2026-10-16. UNCOMPILED.
SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan.
Source attribution: see formalization.yaml and PROVENANCE.json.
Preserve all applicable upstream licenses and attribution notices.
AI assistance: OpenAI assistant; human responsibility remains with the named maintainer.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false
@[expose] public section

/-! A self-contained statement of one exact body and ordinary physical tiling.
Only Mathlib is imported by the Challenge. Theorem holes belong only to the
Challenge; the separate Solution is intended to discharge them through exact
body/model bridges and a freshly checked unconditional endpoint. The explicit
set formulas are fixed here, rather than supplied as existential proof outputs.
The recorded conclusion is only nonempty interior, compactness, tiling existence,
and absence of nonzero translation periods. -/
namespace PalomarCurved
noncomputable section
open Set
open scoped BigOperators InnerProductSpace
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Point := ℝ × ℝ
abbrev QuadraticPoint := (ℤ × ℤ) × (ℤ × ℤ)

/-- Twice the polygon vertices; (a,b) encodes a+b*sqrt(3). -/
def vertexData : List QuadraticPoint := [
  ((0,0),(0,0)), ((2,0),(0,0)), ((3,0),(0,-1)),
  ((3,1),(1,-1)), ((3,1),(3,-1)), ((5,1),(3,-1)),
  ((6,1),(3,0)), ((6,0),(4,0)), ((6,-1),(3,0)),
  ((5,-1),(3,1)), ((3,-1),(3,1)), ((1,-1),(3,1)),
  ((0,-1),(3,0)), ((0,0),(2,0))]
/-- Real realization of the exact doubled quadratic coordinates. -/
def realize (p : QuadraticPoint) : Point :=
  (((p.1.1 : ℝ)+(p.1.2 : ℝ)*Real.sqrt 3)/2,
   ((p.2.1 : ℝ)+(p.2.2 : ℝ)*Real.sqrt 3)/2)
/-- The fourteen actual polygon vertices, including the retained midpoint. -/
def vertex (i : Fin 14) : Point := realize (vertexData.getD i.val ((0,0),(0,0)))
/-- Cyclic successor in the fourteen-edge boundary. -/
def next (i : Fin 14) : Fin 14 := ⟨(i.val+1)%14, Nat.mod_lt _ (by decide)⟩
/-- Directed edge vector in real coordinates. -/
def edge (i : Fin 14) : Point :=
  ((vertex (next i)).1-(vertex i).1,(vertex (next i)).2-(vertex i).2)
/-- Coordinate homeomorphism into the standard Euclidean plane. -/
def toPlane : Point ≃ₜ Plane :=
  (Homeomorph.finTwoArrow (X := ℝ)).symm.trans
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm
/-- The fan's literal center. -/
def center : Point := (3/2,1)
/-- Counterclockwise quarter turn. -/
def leftNormal (p : Point) : Point := (-p.2,p.1)
/-- The homogeneous barycentric polynomial extending the edge displacement. -/
def fanHeight (a b : ℝ) : ℝ := (1/1024 : ℝ)/2*(b-a)*a^2*b^2
/-- Closed standard two-simplex in barycentric coordinates. -/
def simplex : Set Point := {w | 0 ≤ w.1 ∧ 0 ≤ w.2 ∧ w.1+w.2 ≤ 1}
/-- One literal polynomial fan patch; no geometric hypotheses are hidden here. -/
def fanPatch (i : Fin 14) (w : Point) : Point :=
  center + w.1 • (vertex i-center) + w.2 • (vertex (next i)-center) +
    fanHeight w.1 w.2 • leftNormal (edge i)
/-- The curved tile is a finite union of fourteen polynomial simplex images. -/
def curvedBody : Set Plane := toPlane '' (⋃ i : Fin 14, fanPatch i '' simplex)

/-- A tiling is a collection of physical sets, each an image under any Euclidean
isometry (reflections included), covering the whole space with disjoint interiors. -/
def IsTiling (T : Set Plane) (tiles : Set (Set Plane)) : Prop :=
  (∀ A ∈ tiles, ∃ g : Plane ≃ᵢ Plane, A = g '' T) ∧
  (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
  (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))
/-- Ordinary vector translation of a physical tile set. -/
def translate (v : Plane) (A : Set Plane) : Set Plane :=
  (fun x => x + v) '' A
/-- A period preserves membership of every physical tile in the collection.
Preserving the union alone would be vacuous for a covering of the whole space. -/
def IsPeriod (tiles : Set (Set Plane)) (v : Plane) : Prop :=
  ∀ A, A ∈ tiles ↔ translate v A ∈ tiles
/-- At least one covering and interior-packing collection of congruent tiles exists. -/
def HasTiling (T : Set Plane) : Prop := ∃ tiles, IsTiling T tiles
/-- Every physical tiling by this body has no nonzero translation period.
This quantifies over all isometric placements, without a handedness restriction. -/
def IsAperiodic (T : Set Plane) : Prop :=
  ∀ tiles, IsTiling T tiles → ∀ v, IsPeriod tiles v → v = 0

/-- The specified curved planar body has nonempty interior, is compact, admits a physical
tiling, and every physical tiling by it has only the zero translation period. -/
theorem curved_monotile :
    (interior curvedBody).Nonempty ∧ IsCompact curvedBody ∧
    HasTiling curvedBody ∧ IsAperiodic curvedBody := by
  sorry

end
end PalomarCurved
