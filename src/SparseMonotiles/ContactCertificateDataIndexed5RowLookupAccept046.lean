module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept046

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept046PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm0 12 9187 else Pose.ofCodes perm3 12 9187) else (if i.val < 3 then Pose.ofCodes perm12 13 9189 else Pose.ofCodes perm13 13 9189))
theorem fullAccept046PoseLookup_binding : List.ofFn fullAccept046PoseLookup = fullAccept046.map IndexedRow.pose := by rfl
theorem fullAccept046PoseLookup_mem (i : Fin 4) : fullAccept046PoseLookup i ∈ fullAccept046.map IndexedRow.pose := by
  rw [← fullAccept046PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept046PoseLookup_binding
#print axioms fullAccept046PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
