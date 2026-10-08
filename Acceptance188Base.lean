module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance188Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm1, ![true, true, false, true, true, false, true], ![3, 3, -1, 3, 3, -1, 3]⟩

theorem pose_eq_original_entry188 :
    pose = Catalog7.supplied.get ⟨188, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry188]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨765, 442, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then (if i.val < 728 then none else (if i.val < 756 then none else (if i.val < 770 then (if i.val < 763 then none else (if i.val < 766 then (if i.val < 764 then none else (if i.val < 765 then none else some 442)) else (if i.val < 768 then (if i.val < 767 then some 895 else some 886) else (if i.val < 769 then some 870 else some 840)))) else (if i.val < 777 then (if i.val < 773 then (if i.val < 771 then some 782 else (if i.val < 772 then some 668 else none)) else none) else none)))) else none)))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance188Pilot7
