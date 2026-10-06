module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept066

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept066PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm6 21 12605 else Pose.ofCodes perm18 21 12605) else (if i.val < 3 then Pose.ofCodes perm1 13 4373 else Pose.ofCodes perm2 13 4373))
theorem fullAccept066PoseLookup_binding : List.ofFn fullAccept066PoseLookup = fullAccept066.map IndexedRow.pose := by rfl
theorem fullAccept066PoseLookup_mem (i : Fin 4) : fullAccept066PoseLookup i ∈ fullAccept066.map IndexedRow.pose := by
  rw [← fullAccept066PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept066PoseLookup_binding
#print axioms fullAccept066PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
