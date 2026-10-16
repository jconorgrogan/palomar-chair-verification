module

public import SpectreGeometry.QuadraticReal

@[expose] public section


/-! Actual real-coordinate consequences of the finite polygon certificates.
Squared length refers to the ordinary Euclidean sum of coordinate squares.
There is no assumption here about an arbitrary physical tiling. -/
namespace SpectreGeometry
noncomputable section

def realize (x : ExactPoint) : RealPoint := (Quad3.eval x.1/2,Quad3.eval x.2/2)
def realVertex (i : Fin 14) : RealPoint := realize (vertex i)
def realEdge (i : Fin 14) : RealPoint := RealPoint.sub (realVertex (next i)) (realVertex i)
def realDirection (d : Fin 12) : RealPoint := realize (direction d)

theorem realize_sub (x y : ExactPoint) :
    realize (ExactPoint.sub x y) = RealPoint.sub (realize x) (realize y) := by
  simp [realize,ExactPoint.sub,RealPoint.sub,Quad3.eval_sub,sub_div]

theorem realize_dot (x y : ExactPoint) :
    RealPoint.dot (realize x) (realize y) = Quad3.eval (ExactPoint.dot x y)/4 := by
  rw [ExactPoint.eval_dot]
  simp only [realize,ExactPoint.eval,RealPoint.dot]
  ring

theorem realize_det (x y : ExactPoint) :
    RealPoint.det (realize x) (realize y) = Quad3.eval (ExactPoint.det x y)/4 := by
  rw [ExactPoint.eval_det]
  simp only [realize,ExactPoint.eval,RealPoint.det]
  ring

theorem realize_edge (i : Fin 14) : realize (edge i) = realEdge i := realize_sub _ _

theorem real_edges_unit_squared (i : Fin 14) : RealPoint.dot (realEdge i) (realEdge i) = 1 := by
  rw [←realize_edge,realize_dot,all_edges_squared]
  norm_num [Quad3.eval]

theorem real_directions_unit_squared (d : Fin 12) :
    RealPoint.dot (realDirection d) (realDirection d) = 1 := by
  rw [realDirection,realize_dot,all_directions_squared]
  norm_num [Quad3.eval]

theorem real_edge_direction (i : Fin 14) : realEdge i = realDirection (edgeTurn i) := by
  rw [←realize_edge,all_edge_directions]
  rfl

theorem real_vertices_distinct (i j : Fin 14) (h : realVertex i = realVertex j) : i = j := by
  by_contra hne
  have hp := Quad3.positive_sound _ (distinct_vertex_distance_positive i j hne)
  have hd := realize_dot (ExactPoint.sub (vertex i) (vertex j))
    (ExactPoint.sub (vertex i) (vertex j))
  rw [realize_sub] at hd
  change RealPoint.dot (RealPoint.sub (realVertex i) (realVertex j))
    (RealPoint.sub (realVertex i) (realVertex j)) = _ at hd
  rw [h] at hd
  simp only [RealPoint.sub,RealPoint.dot,sub_self,mul_zero,zero_add] at hd
  linarith

theorem real_adjacent_dot_nonnegative (i : Fin 14) :
    0 ≤ RealPoint.dot (realEdge i) (realEdge (next i)) := by
  rw [←realize_edge,←realize_edge,realize_dot]
  rcases adjacent_dot_values i with h | h | h <;> rw [h] <;> norm_num [Quad3.eval]

def RealStrictSeparated (i j : Fin 14) : Prop :=
  0 < RealPoint.det (realEdge i) (RealPoint.sub (realVertex j) (realVertex i)) *
      RealPoint.det (realEdge i) (RealPoint.sub (realVertex (next j)) (realVertex i)) ∨
  0 < RealPoint.det (realEdge j) (RealPoint.sub (realVertex i) (realVertex j)) *
      RealPoint.det (realEdge j) (RealPoint.sub (realVertex (next i)) (realVertex j))

theorem real_separation_of_exact (i j : Fin 14) (h : StrictSeparated i j) :
    RealStrictSeparated i j := by
  have hd : ∀ a b c : Fin 14,
      RealPoint.det (realEdge a) (RealPoint.sub (realVertex b) (realVertex c)) =
        Quad3.eval (ExactPoint.det (edge a) (ExactPoint.sub (vertex b) (vertex c)))/4 := by
    intro a b c
    rw [←realize_edge]
    change RealPoint.det (realize (edge a))
      (RealPoint.sub (realize (vertex b)) (realize (vertex c))) = _
    rw [←realize_sub,realize_det]
  rcases h with h | h
  · apply Or.inl
    have hp := Quad3.positive_sound _ h
    rw [Quad3.eval_mul] at hp
    rw [hd,hd]
    nlinarith
  · apply Or.inr
    have hp := Quad3.positive_sound _ h
    rw [Quad3.eval_mul] at hp
    rw [hd,hd]
    nlinarith

theorem real_nonadjacent_separated (i j : Fin 14)
    (hij : i ≠ j) (hnext : next i ≠ j) (hprev : next j ≠ i) :
    RealStrictSeparated i j := real_separation_of_exact i j (nonadjacent_separated i j hij hnext hprev)

end
end SpectreGeometry
