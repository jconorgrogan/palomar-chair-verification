module

public import SpectreGeometry.ReverseFinitePLMarkedClusterCore
public import SpectreGeometry.ReverseFinitePLScaledInteriorCases

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL.MarkedMeshCertificate
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseExistence
variable {k : Fin 9} (C : MarkedMeshCertificate k)

/-- Concrete normalized marked charts need only vertex and open-edge target
neighborhoods; all triangle-interior points are handled by their affine charts. -/
theorem markedClusterHomeomorph_mem_interior_of_boundary
    (x : sourceHexCarrier (0,0)) (T : Set Plane)
    (hT : rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) ⊆ T)
    (hv : ∀ (i : Fin (meshTriangles k).length) (v : Fin 3),
      x.val = (1/(3*(sourceScale k:ℝ))) • integerPoint
        (sourceVertex k (codeIndex ((meshTriangles k).get i) v)) →
      (1/6:ℝ) • integerPoint (targetVertex k (codeIndex ((meshTriangles k).get i) v)) ∈ interior T)
    (he : ∀ (i : Fin (meshTriangles k).length) (v w : Fin 3), v ≠ w →
      ∀ t ∈ Ioo (0:ℝ) 1,
      x.val = AffineMap.lineMap
        ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k (codeIndex ((meshTriangles k).get i) v)))
        ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k (codeIndex ((meshTriangles k).get i) w))) t →
      AffineMap.lineMap
        ((1/6:ℝ) • integerPoint (targetVertex k (codeIndex ((meshTriangles k).get i) v)))
        ((1/6:ℝ) • integerPoint (targetVertex k (codeIndex ((meshTriangles k).get i) w))) t ∈ interior T) :
    (C.markedClusterHomeomorph x).val ∈ interior T := by
  exact C.markedIntegerMesh.scaledHomeomorph_mem_interior_of_boundary
    (1/(3*(sourceScale k:ℝ))) (1/6)
    (one_div_ne_zero (ne_of_gt (sourceScale_real_pos k))) (by norm_num)
    ((Homeomorph.setCongr (C.markedNormalizedSource).symm) x) T
    (by rw [C.markedNormalizedTarget]; exact hT) hv he

end
end SpectreGeometry.ReverseFinitePL.MarkedMeshCertificate
