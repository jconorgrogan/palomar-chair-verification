module

public import LiteralPlanar.QuinticArc
public import SpectreGeometry.PolygonReal
public import SpectreGeometry.PolygonFanData

@[expose] public section


/-! Literal candidate definitions.

The proposed unrestricted planar tile is a curved semialgebraic body, not a
polygon. It is specified without a Jordan-curve or tiling premise as a finite
union of polynomial images of closed triangles. The assertion that its
boundary is the fourteen displayed arcs requires the small-deformation proof.
No simplicity, disk, tiling, registration, or aperiodicity theorem is asserted.
The rational amplitude satisfies the checked local fan Lipschitz bound;
the assembled-body geometric obligations remain separate.
-/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

abbrev Point := ℝ × ℝ

def center : Point := (3 / 2, 1)
def leftNormal (p : Point) : Point := (-p.2, p.1)

def edgeCurve (i : Fin 14) (t : ℝ) : Point :=
  realVertex i + (t + 1 / 2) • realEdge i +
    Quintic.height Quintic.amplitude t • leftNormal (realEdge i)

def parameterSimplex : Set Point :=
  {w | 0 ≤ w.1 ∧ 0 ≤ w.2 ∧ w.1 + w.2 ≤ 1}

/-- A polynomial map of an ordinary closed simplex. -/
def fanPatch (i : Fin 14) (w : Point) : Point :=
  center + w.1 • (realVertex i - center) +
    w.2 • (realVertex (next i) - center) +
    Quintic.fanHeight Quintic.amplitude w.1 w.2 • leftNormal (realEdge i)

/-- Literal proposed curved semialgebraic tile, with epsilon exactly1/1024. -/
def body : Set Point := ⋃ i : Fin 14, fanPatch i '' parameterSimplex

/-- The intended edge set; equality with the body's frontier is not assumed. -/
def candidateBoundary : Set Point :=
  ⋃ i : Fin 14, edgeCurve i '' Set.Icc (-1 / 2 : ℝ) (1 / 2)

end
end LiteralPlanar.Candidate
