module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance283Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm5, ![false, true, true, false, false, false, false], ![-1, 3, 3, -1, -1, -1, -1]⟩

theorem pose_eq_original_entry283 :
    pose = Catalog7.supplied.get ⟨283, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry283]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨336, 782, fun i => (if i.val < 448 then (if i.val < 224 then none else (if i.val < 336 then none else (if i.val < 392 then (if i.val < 364 then (if i.val < 350 then (if i.val < 343 then (if i.val < 339 then (if i.val < 337 then some 782 else (if i.val < 338 then some 840 else some 870)) else (if i.val < 341 then (if i.val < 340 then some 886 else some 895) else (if i.val < 342 then some 442 else some 668))) else none) else none) else none) else none))) else none)⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance283Pilot7
