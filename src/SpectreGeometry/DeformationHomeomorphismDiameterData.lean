module

public import SpectreGeometry.PolygonData

@[expose] public section


/-! Exact unique-diameter and upper-height certificates for the source polygon. -/
namespace SpectreGeometry.Deformation

def vertexSquaredDistance (i j : Fin 14) : Quad3 :=
  let v := ExactPoint.sub (vertex i) (vertex j)
  ExactPoint.dot v v

def DiameterPair (i j : Fin 14) : Prop := (i=6 ∧ j=12) ∨ (i=12 ∧ j=6)
instance (i j : Fin 14) : Decidable (DiameterPair i j) := inferInstanceAs (Decidable (_ ∨ _))

theorem diameter_pair_value : ∀ i j : Fin 14, DiameterPair i j →
    vertexSquaredDistance i j = (48,24) := by decide

theorem other_pair_strictly_shorter : ∀ i j : Fin 14, ¬ DiameterPair i j →
    Quad3.positive (Quad3.sub (48,24) (vertexSquaredDistance i j)) := by decide

theorem vertices_below_three : ∀ i : Fin 14,
    Quad3.positive (Quad3.sub (6,0) (vertex i).2) := by decide

end SpectreGeometry.Deformation
