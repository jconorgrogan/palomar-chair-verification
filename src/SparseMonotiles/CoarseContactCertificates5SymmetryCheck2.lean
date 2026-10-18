module

public import SparseMonotiles.CoarseContactCertificates5SymmetryData

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
open Contact CoarseContactCertificates5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem child_action2_checked : coarseAllB (fun i =>
    coarsePoseMatchB (conjugate 2 (child i)) (child (childAction 2 i))) = true := by decide +kernel
theorem registry_action2_checked : coarseAllB (fun i =>
    coarsePoseMatchB (conjugate 2 (registry i)) (registry (registryAction 2 i))) = true := by decide +kernel
theorem child_action2 (i : Fin 32) : conjugate 2 (child i) = child (childAction 2 i) :=
  coarsePoseMatchB_sound (coarseAllB_sound child_action2_checked i)
theorem registry_action2 (i : Fin 284) : conjugate 2 (registry i) = registry (registryAction 2 i) :=
  coarsePoseMatchB_sound (coarseAllB_sound registry_action2_checked i)
#print axioms child_action2
#print axioms registry_action2
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
