module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance106Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm7, ![true, true, false, true, false, true, false], ![3, 3, -1, 3, -1, 3, -1]⟩

theorem pose_eq_original_entry106 :
    pose = Catalog7.supplied.get ⟨106, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry106]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨744, 840, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then (if i.val < 728 then none else (if i.val < 756 then (if i.val < 742 then none else (if i.val < 749 then (if i.val < 745 then (if i.val < 743 then none else (if i.val < 744 then none else some 840)) else (if i.val < 747 then (if i.val < 746 then some 870 else some 886) else (if i.val < 748 then some 895 else some 442))) else (if i.val < 752 then (if i.val < 750 then some 668 else (if i.val < 751 then some 782 else none)) else none))) else none)) else none)))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance106Pilot7
