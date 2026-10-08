module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance178Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm2, ![true, false, false, false, true, false, true], ![3, -1, -1, -1, 3, -1, 3]⟩

theorem pose_eq_original_entry178 :
    pose = Catalog7.supplied.get ⟨178, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry178]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨484, 668, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then (if i.val < 504 then (if i.val < 476 then none else (if i.val < 490 then (if i.val < 483 then none else (if i.val < 486 then (if i.val < 484 then none else (if i.val < 485 then some 668 else some 442)) else (if i.val < 488 then (if i.val < 487 then some 895 else some 886) else (if i.val < 489 then some 870 else some 840)))) else (if i.val < 497 then (if i.val < 493 then (if i.val < 491 then some 782 else none) else none) else none))) else none) else none) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance178Pilot7
