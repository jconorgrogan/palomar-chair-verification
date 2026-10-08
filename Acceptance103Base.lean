module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance103Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm7, ![true, true, true, false, false, false, true], ![3, 3, 3, -1, -1, -1, 3]⟩

theorem pose_eq_original_entry103 :
    pose = Catalog7.supplied.get ⟨103, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry103]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨794, 840, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then none else (if i.val < 840 then (if i.val < 812 then (if i.val < 798 then (if i.val < 791 then none else (if i.val < 794 then none else (if i.val < 796 then (if i.val < 795 then some 840 else some 870) else (if i.val < 797 then some 886 else some 895)))) else (if i.val < 805 then (if i.val < 801 then (if i.val < 799 then some 442 else (if i.val < 800 then some 668 else some 782)) else none) else none)) else none) else none))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance103Pilot7
