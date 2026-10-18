module

public import SpectreGeometry.CornerGermData

@[expose] public section


namespace SpectreGeometry

def Quad3.signCertified (x : Quad3) : Prop :=
  x = (0,0) ∨ Quad3.positive x ∨ Quad3.positive (Quad3.sub (0,0) x)
instance (x : Quad3) : Decidable (Quad3.signCertified x) := inferInstanceAs (Decidable (_ ∨ _))

theorem sector_side_signs : ∀ i : Fin 14, ∀ d : Fin 12,
    Quad3.signCertified (ExactPoint.det (edge (previous i)) (sectorVector d)) ∧
    Quad3.signCertified (ExactPoint.det (radialVector i) (sectorVector d)) ∧
    Quad3.signCertified (ExactPoint.det (edge i) (sectorVector d)) := by decide

end SpectreGeometry
