module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept059

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept059PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm12 1 5606 else Pose.ofCodes perm13 1 5606) else (if i.val < 3 then Pose.ofCodes perm8 1 5606 else Pose.ofCodes perm11 1 5606))
theorem fullAccept059PoseLookup_binding : List.ofFn fullAccept059PoseLookup = fullAccept059.map IndexedRow.pose := by rfl
theorem fullAccept059PoseLookup_mem (i : Fin 4) : fullAccept059PoseLookup i ∈ fullAccept059.map IndexedRow.pose := by
  rw [← fullAccept059PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept059PoseLookup_binding
#print axioms fullAccept059PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
