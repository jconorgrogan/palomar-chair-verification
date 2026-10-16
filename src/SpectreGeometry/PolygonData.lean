module

public import Init

@[expose] public section


/-! Exact integer-pair data for twice the fourteen polygon vertices in the
reviewed four-dimensional recipe. A pair (a,b) denotes a+b√3. The separate
real realization must prove that the integer certificates have their stated
geometric meaning; no physical tiling conclusion is asserted here. -/
namespace SpectreGeometry

abbrev Quad3 := Int × Int
namespace Quad3
def add (x y : Quad3) : Quad3 := (x.1+y.1,x.2+y.2)
def sub (x y : Quad3) : Quad3 := (x.1-y.1,x.2-y.2)
def mul (x y : Quad3) : Quad3 := (x.1*y.1+3*x.2*y.2,x.1*y.2+x.2*y.1)
def positive (x : Quad3) : Prop :=
  (0 < x.1 ∧ 0 ≤ x.2) ∨ (0 ≤ x.1 ∧ 0 < x.2) ∨
  (0 < x.1 ∧ x.2 < 0 ∧ 3*x.2*x.2 < x.1*x.1) ∨
  (x.1 < 0 ∧ 0 < x.2 ∧ x.1*x.1 < 3*x.2*x.2)
instance (x : Quad3) : Decidable (positive x) := inferInstanceAs (Decidable (_ ∨ _))
end Quad3

abbrev ExactPoint := Quad3 × Quad3
namespace ExactPoint
def add (x y : ExactPoint) : ExactPoint := (Quad3.add x.1 y.1,Quad3.add x.2 y.2)
def sub (x y : ExactPoint) : ExactPoint := (Quad3.sub x.1 y.1,Quad3.sub x.2 y.2)
def dot (x y : ExactPoint) : Quad3 := Quad3.add (Quad3.mul x.1 y.1) (Quad3.mul x.2 y.2)
def det (x y : ExactPoint) : Quad3 := Quad3.sub (Quad3.mul x.1 y.2) (Quad3.mul x.2 y.1)
end ExactPoint

def vertices : List ExactPoint := [
  ((0,0),(0,0)), ((2,0),(0,0)), ((3,0),(0,-1)),
  ((3,1),(1,-1)), ((3,1),(3,-1)), ((5,1),(3,-1)),
  ((6,1),(3,0)), ((6,0),(4,0)), ((6,-1),(3,0)),
  ((5,-1),(3,1)), ((3,-1),(3,1)), ((1,-1),(3,1)),
  ((0,-1),(3,0)), ((0,0),(2,0))]

def vertex (i : Fin 14) : ExactPoint := vertices.getD i.val ((0,0),(0,0))
def next (i : Fin 14) : Fin 14 := ⟨(i.val+1)%14, Nat.mod_lt _ (by decide)⟩
def edge (i : Fin 14) : ExactPoint := ExactPoint.sub (vertex (next i)) (vertex i)

/-- Twice the twelve directed unit vectors, in counterclockwise order. -/
def directions : List ExactPoint := [
  ((2,0),(0,0)), ((0,1),(1,0)), ((1,0),(0,1)),
  ((0,0),(2,0)), ((-1,0),(0,1)), ((0,-1),(1,0)),
  ((-2,0),(0,0)), ((0,-1),(-1,0)), ((-1,0),(0,-1)),
  ((0,0),(-2,0)), ((1,0),(0,-1)), ((0,1),(-1,0))]
def direction (d : Fin 12) : ExactPoint := directions.getD d.val ((0,0),(0,0))
def edgeTurns : List (Fin 12) := [0,10,1,3,0,2,5,7,4,6,6,8,11,9]
def edgeTurn (i : Fin 14) : Fin 12 := edgeTurns.getD i.val 0

def StrictSeparated (i j : Fin 14) : Prop :=
  Quad3.positive (Quad3.mul
    (ExactPoint.det (edge i) (ExactPoint.sub (vertex j) (vertex i)))
    (ExactPoint.det (edge i) (ExactPoint.sub (vertex (next j)) (vertex i)))) ∨
  Quad3.positive (Quad3.mul
    (ExactPoint.det (edge j) (ExactPoint.sub (vertex i) (vertex j)))
    (ExactPoint.det (edge j) (ExactPoint.sub (vertex (next i)) (vertex j))))
instance (i j : Fin 14) : Decidable (StrictSeparated i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

def doubledAreaSum : Quad3 :=
  ((List.finRange 14).map fun i => ExactPoint.det (vertex i) (vertex (next i))).foldl Quad3.add (0,0)

theorem vertices_length : vertices.length = 14 := by decide
theorem vertices_distinct : ∀ i j : Fin 14, vertex i = vertex j → i = j := by decide
theorem distinct_vertex_distance_positive : ∀ i j : Fin 14, i ≠ j →
    Quad3.positive (ExactPoint.dot (ExactPoint.sub (vertex i) (vertex j))
      (ExactPoint.sub (vertex i) (vertex j))) := by decide
theorem all_edges_squared : ∀ i : Fin 14, ExactPoint.dot (edge i) (edge i) = (4,0) := by decide
theorem all_directions_squared : ∀ d : Fin 12,
    ExactPoint.dot (direction d) (direction d) = (4,0) := by decide
theorem all_edge_directions : ∀ i : Fin 14, edge i = direction (edgeTurn i) := by decide
theorem adjacent_dot_values : ∀ i : Fin 14,
    ExactPoint.dot (edge i) (edge (next i)) = (0,0) ∨
    ExactPoint.dot (edge i) (edge (next i)) = (2,0) ∨
    ExactPoint.dot (edge i) (edge (next i)) = (4,0) := by decide
theorem nonadjacent_separated : ∀ i j : Fin 14,
    i ≠ j → next i ≠ j → next j ≠ i → StrictSeparated i j := by decide
theorem retained_midpoint : ExactPoint.add (vertex 10) (vertex 10) =
    ExactPoint.add (vertex 9) (vertex 11) := by decide
theorem only_straight_vertex : ∀ i : Fin 14,
    ExactPoint.det (edge i) (edge (next i)) = (0,0) ↔ i = 9 := by decide
theorem exact_area_sum : doubledAreaSum = (24,24) := by decide

end SpectreGeometry
