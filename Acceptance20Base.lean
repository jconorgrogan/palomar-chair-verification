module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance20Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm12, ![true, false, true, true, false, false, true], ![3, -1, 3, 3, -1, -1, 3]⟩

theorem pose_eq_original_entry20 :
    pose = Catalog7.supplied.get ⟨20, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry20]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨624, 895, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then none else (if i.val < 616 then none else (if i.val < 644 then (if i.val < 630 then (if i.val < 623 then none else (if i.val < 626 then (if i.val < 624 then none else (if i.val < 625 then some 895 else some 442)) else (if i.val < 628 then (if i.val < 627 then some 668 else some 782) else (if i.val < 629 then some 840 else some 870)))) else (if i.val < 637 then (if i.val < 633 then (if i.val < 631 then some 886 else none) else none) else none)) else none))) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance20Pilot7
