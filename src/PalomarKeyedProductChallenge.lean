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
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
@[expose] public section

/-! A self-contained statement of one exact body and ordinary physical tiling.
Only Mathlib is imported by the Challenge. Theorem holes belong only to the
Challenge; the separate Solution is intended to discharge them through exact
body/model bridges and a freshly checked unconditional endpoint. The explicit
set formulas are fixed here, rather than supplied as existential proof outputs.
The recorded conclusion is only nonempty interior, compactness, tiling existence,
and absence of nonzero translation periods. -/
namespace PalomarKeyedProduct
noncomputable section
open Set
open scoped BigOperators InnerProductSpace
abbrev Four := EuclideanSpace ℝ (Fin 4)
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
/-- The undeformed polygon is the union of the fourteen exact radial triangles. -/
def polygon : Set Point := ⋃ i : Fin 14,
  convexHull ℝ {vertex i,vertex (next i),realize ((3,0),(2,0))}
/-- Pair-of-plane coordinates in the standard Euclidean four-space. -/
def toFour (p : Point × Point) : Four := WithLp.toLp 2 ![p.1.1,p.1.2,p.2.1,p.2.2]
/-- Undeformed product of the exact polygons. -/
def rawProduct : Set Four := toFour '' (polygon ×ˢ polygon)
/-- Key index: factor, edge, and polarity bit, giving exactly 56 sites. -/
abbrev KeySite := Fin 2 × Fin 14 × Bool
/-- False is positive and true is negative polarity. -/
def sign (s : KeySite) : ℝ := if s.2.2 then -1 else 1
/-- Signed integer label: polarity times the one-based active factor. -/
def label (s : KeySite) : ℤ := (if s.2.2 then -1 else 1)*(s.1.val+1)
/-- The exact collar/key width. -/
def eta : ℝ := 1/40000
/-- The exact collar half-height. -/
def rho : ℝ := 1/40000
/-- Negative/positive side primes for each of the three tangent coordinates. -/
def primePairs : Fin 3 → ℕ × ℕ := ![(3,5),(7,11),(13,17)]
/-- Selected side prime. -/
def prime (j : Fin 3) (b : Bool) : ℕ := if b then (primePairs j).2 else (primePairs j).1
/-- The active key center lies at edge parameter 1/4 or 3/4. -/
def activeCenter (s : KeySite) : Point := vertex s.2.1+(1/2-sign s/4) • edge s.2.1
/-- Full four-dimensional center, with passive coordinates (1/2,1/2). -/
def keyCenter (s : KeySite) : Four :=
  if s.1=0 then toFour (activeCenter s,(1/2,1/2)) else toFour ((1/2,1/2),activeCenter s)
/-- Embed a real plane vector in the first factor. -/
def leftEmbed (p : Point) : Four := toFour (p,(0,0))
/-- Embed a real plane vector in the second factor. -/
def rightEmbed (p : Point) : Four := toFour ((0,0),p)
/-- Tangents: signed active edge followed by the positive passive axes. -/
def tangent (s : KeySite) : Fin 3 → Four :=
  if s.1=0 then ![leftEmbed (sign s • edge s.2.1),rightEmbed (1,0),rightEmbed (0,1)]
  else ![rightEmbed (sign s • edge s.2.1),leftEmbed (1,0),leftEmbed (0,1)]
/-- Outward clockwise active-edge normal, independent of key polarity. -/
def normal (s : KeySite) : Four :=
  if s.1=0 then leftEmbed ((edge s.2.1).2,-(edge s.2.1).1)
  else rightEmbed ((edge s.2.1).2,-(edge s.2.1).1)
/-- Three tangents and the outward normal, in that order. -/
def frame (s : KeySite) : Fin 4 → Four := ![tangent s 0,tangent s 1,tangent s 2,normal s]
/-- Explicit affine frame map: the stated center plus the four frame components. -/
def keyMap (s : KeySite) (w : Four) : Four := keyCenter s+∑ j : Fin 4, w j • frame s j
/-- Exact closed rectangular reference collar. -/
def referenceCollar : Set Four := {w | (∀ j : Fin 3, |w j.castSucc| ≤ 2*eta) ∧ |w 3| ≤ rho}
/-- Placed closed collar. -/
def collar (s : KeySite) : Set Four := keyMap s '' referenceCollar
/-- Signed zero-extended max-min rational tent; denominator exactly 4357. -/
def keyHeight (s : KeySite) (v : Four) : ℝ :=
  (eta*(label s : ℝ)/4357)*max 0
    (Finset.univ.inf' Finset.univ_nonempty (fun j : Fin 3 =>
      min (1+(prime j false : ℝ)*inner ℝ (tangent s j) v/eta)
          (1-(prime j true : ℝ)*inner ℝ (tangent s j) v/eta)))
/-- Actual outward-coordinate hypograph. -/
def hypograph (s : KeySite) : Set Four :=
  {x | inner ℝ (normal s) (x-keyCenter s) ≤ keyHeight s (x-keyCenter s)}
/-- Literal tube replacement: remove open collars, insert their closed hypographs. -/
def keyedProduct : Set Four :=
  (rawProduct \ ⋃ s : KeySite, interior (collar s)) ∪
    ⋃ s : KeySite, collar s ∩ hypograph s


/-- A tiling is a collection of physical sets, each an image under any Euclidean
isometry (reflections included), covering the whole space with disjoint interiors. -/
def IsTiling (T : Set Four) (tiles : Set (Set Four)) : Prop :=
  (∀ A ∈ tiles, ∃ g : Four ≃ᵢ Four, A = g '' T) ∧
  (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
  (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))
/-- Ordinary vector translation of a physical tile set. -/
def translate (v : Four) (A : Set Four) : Set Four :=
  (fun x => x + v) '' A
/-- A period preserves membership of every physical tile in the collection.
Preserving the union alone would be vacuous for a covering of the whole space. -/
def IsPeriod (tiles : Set (Set Four)) (v : Four) : Prop :=
  ∀ A, A ∈ tiles ↔ translate v A ∈ tiles
/-- At least one covering and interior-packing collection of congruent tiles exists. -/
def HasTiling (T : Set Four) : Prop := ∃ tiles, IsTiling T tiles
/-- Every physical tiling by this body has no nonzero translation period.
This quantifies over all isometric placements, without a handedness restriction. -/
def IsAperiodic (T : Set Four) : Prop :=
  ∀ tiles, IsTiling T tiles → ∀ v, IsPeriod tiles v → v = 0

/-- The specified 56-key four-dimensional body has nonempty interior, is compact, admits a physical
tiling, and every physical tiling by it has only the zero translation period. -/
theorem keyed_product_monotile :
    (interior keyedProduct).Nonempty ∧ IsCompact keyedProduct ∧
    HasTiling keyedProduct ∧ IsAperiodic keyedProduct := by
  sorry

end
end PalomarKeyedProduct
