module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance74Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm9, ![true, true, false, false, false, true, true], ![3, 3, -1, -1, -1, 3, 3]⟩

theorem pose_eq_original_entry74 :
    pose = Catalog7.supplied.get ⟨74, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry74]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨695, 870, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then (if i.val < 728 then (if i.val < 700 then (if i.val < 686 then none else (if i.val < 693 then none else (if i.val < 696 then (if i.val < 694 then none else (if i.val < 695 then none else some 870)) else (if i.val < 698 then (if i.val < 697 then some 886 else some 895) else (if i.val < 699 then some 442 else some 668))))) else (if i.val < 714 then (if i.val < 707 then (if i.val < 703 then (if i.val < 701 then some 782 else (if i.val < 702 then some 840 else none)) else none) else none) else none)) else none) else none)))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance74Pilot7
