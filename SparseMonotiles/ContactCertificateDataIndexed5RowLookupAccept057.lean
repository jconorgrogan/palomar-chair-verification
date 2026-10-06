module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept057

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept057PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm6 13 9189 else Pose.ofCodes perm7 13 9189) else (if i.val < 3 then Pose.ofCodes perm15 30 14003 else Pose.ofCodes perm14 30 14003))
theorem fullAccept057PoseLookup_binding : List.ofFn fullAccept057PoseLookup = fullAccept057.map IndexedRow.pose := by rfl
theorem fullAccept057PoseLookup_mem (i : Fin 4) : fullAccept057PoseLookup i ∈ fullAccept057.map IndexedRow.pose := by
  rw [← fullAccept057PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept057PoseLookup_binding
#print axioms fullAccept057PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
