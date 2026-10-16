module

public import SpectreGeometry.PolygonFanData
public import SpectreGeometry.CornerSteps

@[expose] public section


/-! Exact finite data for local corner germs and the twelve intervening
open direction sectors. Physical germ correspondence is separate. -/
namespace SpectreGeometry

def sectorVector (d : Fin 12) : ExactPoint := ExactPoint.add (direction d) (direction (directionAdd d 1))
def radialVector (i : Fin 14) : ExactPoint := ExactPoint.sub (vertex i) fanCenter

def Quad3.nonnegative (x : Quad3) : Prop := x = (0,0) ∨ Quad3.positive x
instance (x : Quad3) : Decidable (Quad3.nonnegative x) := inferInstanceAs (Decidable (_ ∨ _))

def cornerSector (i : Fin 14) (d : Fin 12) : Prop :=
  (Quad3.nonnegative (ExactPoint.det (edge (previous i)) (sectorVector d)) ∧
    Quad3.nonpositive (ExactPoint.det (radialVector i) (sectorVector d))) ∨
  (Quad3.nonnegative (ExactPoint.det (radialVector i) (sectorVector d)) ∧
    Quad3.nonnegative (ExactPoint.det (edge i) (sectorVector d)))
instance (i : Fin 14) (d : Fin 12) : Decidable (cornerSector i d) := inferInstanceAs (Decidable (_ ∨ _))

def cornerSectorList (i : Fin 14) : List (Fin 12) := (List.finRange 12).filter (fun d => decide (cornerSector i d))

theorem next_previous : ∀ i : Fin 14, next (previous i) = i := by decide
theorem previous_next : ∀ i : Fin 14, previous (next i) = i := by decide
theorem previous_ne : ∀ i : Fin 14, previous i ≠ i := by decide

theorem nonincident_vertex_strict_separator : ∀ i j : Fin 14,
    j ≠ i → next j ≠ i → ∃ e : Fin 3,
    Quad3.positive (Quad3.sub (0,0) (ExactPoint.det (triangleEdge j e)
      (ExactPoint.sub (vertex i) (triangleVertex j e)))) := by decide

theorem sector_vector_off_edge : ∀ i : Fin 14, ∀ d : Fin 12,
    ExactPoint.det (edge i) (sectorVector d) ≠ (0,0) := by decide

theorem corner_sector_count : ∀ i : Fin 14, (cornerSectorList i).length = cornerSteps i := by decide

end SpectreGeometry
