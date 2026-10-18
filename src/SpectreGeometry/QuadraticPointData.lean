module

public import SpectreGeometry.DeformedVertexData
public import Init.Data.Rat

@[expose] public section


/-! Exact rational sqrt(3) coordinates and the direction-parity development
on them. This module contains finite algebraic identities only. -/
namespace SpectreGeometry

abbrev RationalQuadratic := Rat × Rat
abbrev RationalQuadraticPoint := RationalQuadratic × RationalQuadratic

def ratQuadAdd (x y : RationalQuadratic) : RationalQuadratic := (x.1+y.1,x.2+y.2)
def ratQuadSub (x y : RationalQuadratic) : RationalQuadratic := (x.1-y.1,x.2-y.2)
def ratQuadMul (x y : RationalQuadratic) : RationalQuadratic :=
  (x.1*y.1+3*x.2*y.2,x.1*y.2+x.2*y.1)
def ratQuadHalfInt (x : Quad3) : RationalQuadratic := ((x.1 : Rat)/2,(x.2 : Rat)/2)
def rationalVertex (i : Fin 14) : RationalQuadraticPoint :=
  (ratQuadHalfInt (vertex i).1,ratQuadHalfInt (vertex i).2)
def rationalDirection (d : Fin 12) : RationalQuadraticPoint :=
  (ratQuadHalfInt (direction d).1,ratQuadHalfInt (direction d).2)
def rationalRotate (k : Fin 12) (p : RationalQuadraticPoint) : RationalQuadraticPoint :=
  (ratQuadSub (ratQuadMul (rationalDirection k).1 p.1) (ratQuadMul (rationalDirection k).2 p.2),
    ratQuadAdd (ratQuadMul (rationalDirection k).1 p.2) (ratQuadMul (rationalDirection k).2 p.1))

def developPoint (p : RationalQuadraticPoint) : Rat × Rat :=
  (2*(p.1.1+p.1.2),p.2.1+3*p.2.2-(p.1.1+p.1.2))
def rationalKitePoint (p : KiteVertexPoint) : Rat × Rat := ((p.1 : Rat),(p.2 : Rat))

theorem developed_rotated_vertices : ∀ (k : Fin 12) (i : Fin 14),
    developPoint (rationalRotate k (rationalVertex i)) = rationalKitePoint (deformedVertex k i) := by decide +kernel

theorem developed_directions : ∀ d : Fin 12,
    developPoint (rationalDirection d) = rationalKitePoint (deformedDirection d) := by decide +kernel

end SpectreGeometry
