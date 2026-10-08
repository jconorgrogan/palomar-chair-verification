module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance99Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm7, ![true, true, true, true, false, true, true], ![3, 3, 3, 3, -1, 3, 3]⟩

theorem pose_eq_original_entry99 :
    pose = Catalog7.supplied.get ⟨99, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry99]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨865, 840, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then none else (if i.val < 840 then none else (if i.val < 868 then (if i.val < 854 then none else (if i.val < 861 then none else (if i.val < 864 then none else (if i.val < 866 then (if i.val < 865 then none else some 840) else (if i.val < 867 then some 870 else some 886))))) else (if i.val < 882 then (if i.val < 875 then (if i.val < 871 then (if i.val < 869 then some 895 else (if i.val < 870 then some 442 else none)) else (if i.val < 873 then (if i.val < 872 then some 668 else some 782) else none)) else none) else none))))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance99Pilot7
