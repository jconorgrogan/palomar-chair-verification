module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance215Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm1, ![true, false, false, false, false, false, false], ![3, -1, -1, -1, -1, -1, -1]⟩

theorem pose_eq_original_entry215 :
    pose = Catalog7.supplied.get ⟨215, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry215]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨449, 442, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then (if i.val < 504 then (if i.val < 476 then (if i.val < 462 then (if i.val < 455 then (if i.val < 451 then (if i.val < 449 then none else (if i.val < 450 then some 442 else some 895)) else (if i.val < 453 then (if i.val < 452 then some 886 else some 870) else (if i.val < 454 then some 840 else some 782))) else (if i.val < 458 then (if i.val < 456 then some 668 else none) else none)) else none) else none) else none) else none) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance215Pilot7
