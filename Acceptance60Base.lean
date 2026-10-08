module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance60Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm11, ![true, false, false, false, true, true, true], ![3, -1, -1, -1, 3, 3, 3]⟩

theorem pose_eq_original_entry60 :
    pose = Catalog7.supplied.get ⟨60, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry60]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨498, 886, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then (if i.val < 504 then (if i.val < 476 then none else (if i.val < 490 then none else (if i.val < 497 then none else (if i.val < 500 then (if i.val < 498 then none else (if i.val < 499 then some 886 else some 895)) else (if i.val < 502 then (if i.val < 501 then some 442 else some 668) else (if i.val < 503 then some 782 else some 840)))))) else (if i.val < 532 then (if i.val < 518 then (if i.val < 511 then (if i.val < 507 then (if i.val < 505 then some 870 else none) else none) else none) else none) else none)) else none) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance60Pilot7
