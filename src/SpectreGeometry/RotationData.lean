module

public import SpectreGeometry.PolygonData

@[expose] public section


/-! Exact cyclic twelve-direction multiplication. The following are finite
algebraic certificates, later interpreted as real orientation-preserving
Euclidean rotations. They do not restrict arbitrary tiling poses by fiat. -/
namespace SpectreGeometry

def directionAdd (a b : Fin 12) : Fin 12 := ⟨(a.val+b.val)%12,Nat.mod_lt _ (by decide)⟩
def directionInverse (a : Fin 12) : Fin 12 := ⟨(12-a.val)%12,Nat.mod_lt _ (by decide)⟩
def complexMulExact (x y : ExactPoint) : ExactPoint :=
  (Quad3.sub (Quad3.mul x.1 y.1) (Quad3.mul x.2 y.2),
   Quad3.add (Quad3.mul x.1 y.2) (Quad3.mul x.2 y.1))

theorem direction_multiply : ∀ a b : Fin 12,
    complexMulExact (direction a) (direction b) =
      ExactPoint.add (direction (directionAdd a b)) (direction (directionAdd a b)) := by decide

theorem direction_inverse_left : ∀ a : Fin 12, directionAdd (directionInverse a) a = 0 := by decide
theorem direction_inverse_right : ∀ a : Fin 12, directionAdd a (directionInverse a) = 0 := by decide
theorem direction_add_assoc : ∀ a b c : Fin 12,
    directionAdd (directionAdd a b) c = directionAdd a (directionAdd b c) := by decide
theorem direction_distinct_distance : ∀ a b : Fin 12, a ≠ b →
    Quad3.positive (ExactPoint.dot (ExactPoint.sub (direction a) (direction b))
      (ExactPoint.sub (direction a) (direction b))) := by decide

end SpectreGeometry
