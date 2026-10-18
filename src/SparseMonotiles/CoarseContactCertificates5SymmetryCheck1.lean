module

public import SparseMonotiles.CoarseContactCertificates5SymmetryData

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
open Contact CoarseContactCertificates5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem child_action1_checked : coarseAllB (fun i =>
    coarsePoseMatchB (conjugate 1 (child i)) (child (childAction 1 i))) = true := by decide +kernel
theorem registry_action1_checked : coarseAllB (fun i =>
    coarsePoseMatchB (conjugate 1 (registry i)) (registry (registryAction 1 i))) = true := by decide +kernel
theorem child_action1 (i : Fin 32) : conjugate 1 (child i) = child (childAction 1 i) :=
  coarsePoseMatchB_sound (coarseAllB_sound child_action1_checked i)
theorem registry_action1 (i : Fin 284) : conjugate 1 (registry i) = registry (registryAction 1 i) :=
  coarsePoseMatchB_sound (coarseAllB_sound registry_action1_checked i)
#print axioms child_action1
#print axioms registry_action1
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
