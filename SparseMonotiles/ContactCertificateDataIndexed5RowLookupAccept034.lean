module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept034

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept034PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm8 2 2829 else Pose.ofCodes perm12 2 2829) else (if i.val < 3 then Pose.ofCodes perm7 2 5630 else Pose.ofCodes perm11 2 5630))
theorem fullAccept034PoseLookup_binding : List.ofFn fullAccept034PoseLookup = fullAccept034.map IndexedRow.pose := by rfl
theorem fullAccept034PoseLookup_mem (i : Fin 4) : fullAccept034PoseLookup i ∈ fullAccept034.map IndexedRow.pose := by
  rw [← fullAccept034PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept034PoseLookup_binding
#print axioms fullAccept034PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
