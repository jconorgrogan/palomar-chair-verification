module

public import SparseMonotiles.CoarseContactCertificates5SymmetryData

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
open Contact CoarseContactCertificates5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem child_action3_checked : coarseAllB (fun i =>
    coarsePoseMatchB (conjugate 3 (child i)) (child (childAction 3 i))) = true := by decide +kernel
theorem registry_action3_checked : coarseAllB (fun i =>
    coarsePoseMatchB (conjugate 3 (registry i)) (registry (registryAction 3 i))) = true := by decide +kernel
theorem child_action3 (i : Fin 32) : conjugate 3 (child i) = child (childAction 3 i) :=
  coarsePoseMatchB_sound (coarseAllB_sound child_action3_checked i)
theorem registry_action3 (i : Fin 284) : conjugate 3 (registry i) = registry (registryAction 3 i) :=
  coarsePoseMatchB_sound (coarseAllB_sound registry_action3_checked i)
#print axioms child_action3
#print axioms registry_action3
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
