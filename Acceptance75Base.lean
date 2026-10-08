module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance75Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm8, ![true, true, true, false, true, false, true], ![3, 3, 3, -1, 3, -1, 3]⟩

theorem pose_eq_original_entry75 :
    pose = Catalog7.supplied.get ⟨75, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry75]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨822, 870, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then none else (if i.val < 840 then (if i.val < 812 then none else (if i.val < 826 then (if i.val < 819 then none else (if i.val < 822 then none else (if i.val < 824 then (if i.val < 823 then some 870 else some 840) else (if i.val < 825 then some 782 else some 668)))) else (if i.val < 833 then (if i.val < 829 then (if i.val < 827 then some 442 else (if i.val < 828 then some 895 else some 886)) else none) else none))) else none))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance75Pilot7
