module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept013

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept013PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm14 23 9832 else Pose.ofCodes perm0 23 9832) else (if i.val < 3 then Pose.ofCodes perm6 16 15206 else Pose.ofCodes perm8 16 15206))
theorem fullAccept013PoseLookup_binding : List.ofFn fullAccept013PoseLookup = fullAccept013.map IndexedRow.pose := by rfl
theorem fullAccept013PoseLookup_mem (i : Fin 4) : fullAccept013PoseLookup i ∈ fullAccept013.map IndexedRow.pose := by
  rw [← fullAccept013PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept013PoseLookup_binding
#print axioms fullAccept013PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
