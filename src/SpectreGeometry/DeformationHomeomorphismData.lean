module

public import SpectreGeometry.DeformedVertexData

@[expose] public section


/-! Exact boundary-only triangulation and residual-matrix certificates for
all twelve actual C12 frames. The matrix inequality is the quantitative input
to global inversion; source/target realization and coverage are separate. -/
namespace SpectreGeometry.Deformation

abbrev TriangleIndices := Fin 14 × Fin 14 × Fin 14

def triangles : List TriangleIndices :=
  [(2,3,4),(1,2,4),(4,5,6),(6,7,8),(4,6,8),(1,4,8),
    (8,9,10),(10,11,12),(10,12,13),(8,10,13),(1,8,13),(0,1,13)]
def triangle (i : Fin 12) : TriangleIndices := triangles.getD i.val (0,0,0)
def sourceVertex4 (k : Fin 12) (i : Fin 14) : ExactPoint :=
  complexMulExact (direction k) (vertex i)
def targetVertex4 (k : Fin 12) (i : Fin 14) : ExactPoint :=
  let p := deformedVertex k i
  ((0,2*p.1),(2*p.1+4*p.2,0))
def sourceColumn (k i : Fin 12) (second : Bool) : ExactPoint :=
  let t := triangle i
  ExactPoint.sub (sourceVertex4 k (if second then t.2.2 else t.2.1)) (sourceVertex4 k t.1)
def targetColumn (k i : Fin 12) (second : Bool) : ExactPoint :=
  let t := triangle i
  ExactPoint.sub (targetVertex4 k (if second then t.2.2 else t.2.1)) (targetVertex4 k t.1)
def sourceDet (k i : Fin 12) : Quad3 :=
  ExactPoint.det (sourceColumn k i false) (sourceColumn k i true)

/-- Row-major two-by-two integer sqrt(3) matrix. -/
abbrev ExactMatrix := Quad3 × Quad3 × Quad3 × Quad3

def numeratorMatrix (k i : Fin 12) : ExactMatrix :=
  let u := sourceColumn k i false
  let v := sourceColumn k i true
  let a := targetColumn k i false
  let b := targetColumn k i true
  (Quad3.sub (Quad3.mul a.1 v.2) (Quad3.mul b.1 u.2),
    Quad3.sub (Quad3.mul b.1 u.1) (Quad3.mul a.1 v.1),
    Quad3.sub (Quad3.mul a.2 v.2) (Quad3.mul b.2 u.2),
    Quad3.sub (Quad3.mul b.2 u.1) (Quad3.mul a.2 v.1))
def residualMatrix (k i : Fin 12) : ExactMatrix :=
  let n := numeratorMatrix k i
  let d := Quad3.mul (8,0) (sourceDet k i)
  (Quad3.sub d n.1,Quad3.sub (0,0) n.2.1,
    Quad3.sub (0,0) n.2.2.1,Quad3.sub d n.2.2.2)
def residualGramGap (k i : Fin 12) : Quad3 × Quad3 × Quad3 :=
  let r := residualMatrix k i
  let d2 := Quad3.mul (225,0) (Quad3.mul (sourceDet k i) (sourceDet k i))
  (Quad3.sub d2 (Quad3.mul (4,0) (Quad3.add (Quad3.mul r.1 r.1) (Quad3.mul r.2.2.1 r.2.2.1))),
    Quad3.sub (0,0) (Quad3.mul (4,0) (Quad3.add (Quad3.mul r.1 r.2.1) (Quad3.mul r.2.2.1 r.2.2.2))),
    Quad3.sub d2 (Quad3.mul (4,0) (Quad3.add (Quad3.mul r.2.1 r.2.1) (Quad3.mul r.2.2.2 r.2.2.2))))

def MatrixCertificate (k i : Fin 12) : Prop :=
  let g := residualGramGap k i
  Quad3.positive (sourceDet k i) ∧ Quad3.positive g.1 ∧
    Quad3.positive (Quad3.sub (Quad3.mul g.1 g.2.2) (Quad3.mul g.2.1 g.2.1))
instance (k i : Fin 12) : Decidable (MatrixCertificate k i) := inferInstanceAs (Decidable (_ ∧ _))

theorem triangles_length : triangles.length = 12 := by decide

theorem residual_matrix_certificate : ∀ k i : Fin 12, MatrixCertificate k i := by decide

end SpectreGeometry.Deformation
