module

public import SpectreGeometry.PolygonData

@[expose] public section


/-! Exact radial triangulation data. The auxiliary center is (3/2,1) in
physical coordinates; it does not change the polygon or the key centers.
All fourteen boundary vertices, including the collinear midpoint, remain. -/
namespace SpectreGeometry

def fanCenter : ExactPoint := ((3,0),(2,0))
def triangleVertex (i : Fin 14) (v : Fin 3) : ExactPoint :=
  [fanCenter,vertex i,vertex (next i)].getD v.val ((0,0),(0,0))
def triangleNext (v : Fin 3) : Fin 3 := ⟨(v.val+1)%3,Nat.mod_lt _ (by decide)⟩
def triangleEdge (i : Fin 14) (v : Fin 3) : ExactPoint :=
  ExactPoint.sub (triangleVertex i (triangleNext v)) (triangleVertex i v)

def Quad3.nonpositive (x : Quad3) : Prop := x = (0,0) ∨ Quad3.positive (Quad3.sub (0,0) x)
instance (x : Quad3) : Decidable (Quad3.nonpositive x) := inferInstanceAs (Decidable (_ ∨ _))

def TriangleSideSeparates (i j : Fin 14) (e : Fin 3) : Prop :=
  ∀ v : Fin 3, Quad3.nonpositive
    (ExactPoint.det (triangleEdge i e) (ExactPoint.sub (triangleVertex j v) (triangleVertex i e)))
instance (i j : Fin 14) (e : Fin 3) : Decidable (TriangleSideSeparates i j e) :=
  inferInstanceAs (Decidable (∀ v : Fin 3, _))

def FanPairSeparated (i j : Fin 14) : Prop :=
  (∃ e : Fin 3, TriangleSideSeparates i j e) ∨
  (∃ e : Fin 3, TriangleSideSeparates j i e)
instance (i j : Fin 14) : Decidable (FanPairSeparated i j) := inferInstanceAs (Decidable (_ ∨ _))

theorem fan_center_strictly_left : ∀ i : Fin 14,
    Quad3.positive (ExactPoint.det (edge i) (ExactPoint.sub fanCenter (vertex i))) := by decide

theorem fan_triangles_positive : ∀ i : Fin 14,
    Quad3.positive (ExactPoint.det (triangleEdge i 0)
      (ExactPoint.sub (triangleVertex i 2) (triangleVertex i 0))) := by decide

theorem fan_pairs_separated : ∀ i j : Fin 14, i ≠ j → FanPairSeparated i j := by decide

end SpectreGeometry
