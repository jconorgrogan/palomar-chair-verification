module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept063

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept063PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm15 30 11204 else Pose.ofCodes perm14 30 11204) else (if i.val < 3 then Pose.ofCodes perm19 30 11204 else Pose.ofCodes perm16 30 11204))
theorem fullAccept063PoseLookup_binding : List.ofFn fullAccept063PoseLookup = fullAccept063.map IndexedRow.pose := by rfl
theorem fullAccept063PoseLookup_mem (i : Fin 4) : fullAccept063PoseLookup i ∈ fullAccept063.map IndexedRow.pose := by
  rw [← fullAccept063PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept063PoseLookup_binding
#print axioms fullAccept063PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
