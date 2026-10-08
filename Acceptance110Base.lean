module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance110Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm6, ![true, true, false, true, false, true, true], ![3, 3, -1, 3, -1, 3, 3]⟩

theorem pose_eq_original_entry110 :
    pose = Catalog7.supplied.get ⟨110, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry110]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨751, 840, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then (if i.val < 728 then none else (if i.val < 756 then (if i.val < 742 then none else (if i.val < 749 then none else (if i.val < 752 then (if i.val < 750 then none else (if i.val < 751 then none else some 840)) else (if i.val < 754 then (if i.val < 753 then some 782 else some 668) else (if i.val < 755 then some 442 else some 895))))) else (if i.val < 770 then (if i.val < 763 then (if i.val < 759 then (if i.val < 757 then some 886 else (if i.val < 758 then some 870 else none)) else none) else none) else none))) else none)))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance110Pilot7
