module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance169Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm2, ![true, true, true, true, false, false, true], ![3, 3, 3, 3, -1, -1, 3]⟩

theorem pose_eq_original_entry169 :
    pose = Catalog7.supplied.get ⟨169, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry169]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨851, 668, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then none else (if i.val < 840 then none else (if i.val < 868 then (if i.val < 854 then (if i.val < 847 then none else (if i.val < 850 then none else (if i.val < 852 then (if i.val < 851 then none else some 668) else (if i.val < 853 then some 442 else some 895)))) else (if i.val < 861 then (if i.val < 857 then (if i.val < 855 then some 886 else (if i.val < 856 then some 870 else some 840)) else (if i.val < 859 then (if i.val < 858 then some 782 else none) else none)) else none)) else none)))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance169Pilot7
