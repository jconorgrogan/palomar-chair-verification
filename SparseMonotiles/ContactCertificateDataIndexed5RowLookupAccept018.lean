module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept018

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept018PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm14 15 11204 else Pose.ofCodes perm0 15 11204) else (if i.val < 3 then Pose.ofCodes perm7 8 4173 else Pose.ofCodes perm17 8 4173))
theorem fullAccept018PoseLookup_binding : List.ofFn fullAccept018PoseLookup = fullAccept018.map IndexedRow.pose := by rfl
theorem fullAccept018PoseLookup_mem (i : Fin 4) : fullAccept018PoseLookup i ∈ fullAccept018.map IndexedRow.pose := by
  rw [← fullAccept018PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept018PoseLookup_binding
#print axioms fullAccept018PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
