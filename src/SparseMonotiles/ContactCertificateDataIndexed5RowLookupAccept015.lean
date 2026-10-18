module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept015

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept015PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm18 16 15206 else Pose.ofCodes perm12 16 15206) else (if i.val < 3 then Pose.ofCodes perm19 15 11204 else Pose.ofCodes perm5 15 11204))
theorem fullAccept015PoseLookup_binding : List.ofFn fullAccept015PoseLookup = fullAccept015.map IndexedRow.pose := by rfl
theorem fullAccept015PoseLookup_mem (i : Fin 4) : fullAccept015PoseLookup i ∈ fullAccept015.map IndexedRow.pose := by
  rw [← fullAccept015PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept015PoseLookup_binding
#print axioms fullAccept015PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
