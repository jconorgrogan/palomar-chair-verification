module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept041

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept041PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm5 6 3025 else Pose.ofCodes perm19 6 3025) else (if i.val < 3 then Pose.ofCodes perm11 22 12629 else Pose.ofCodes perm13 22 12629))
theorem fullAccept041PoseLookup_binding : List.ofFn fullAccept041PoseLookup = fullAccept041.map IndexedRow.pose := by rfl
theorem fullAccept041PoseLookup_mem (i : Fin 4) : fullAccept041PoseLookup i ∈ fullAccept041.map IndexedRow.pose := by
  rw [← fullAccept041PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept041PoseLookup_binding
#print axioms fullAccept041PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
