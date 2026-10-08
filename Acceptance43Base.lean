module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance43Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm11, ![true, true, false, true, true, true, true], ![3, 3, -1, 3, 3, 3, 3]⟩

theorem pose_eq_original_entry43 :
    pose = Catalog7.supplied.get ⟨43, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry43]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨779, 886, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then (if i.val < 728 then none else (if i.val < 756 then none else (if i.val < 770 then none else (if i.val < 777 then none else (if i.val < 780 then (if i.val < 778 then none else (if i.val < 779 then none else some 886)) else (if i.val < 782 then (if i.val < 781 then some 895 else some 442) else (if i.val < 783 then none else some 668))))))) else (if i.val < 840 then (if i.val < 812 then (if i.val < 798 then (if i.val < 791 then (if i.val < 787 then (if i.val < 785 then some 782 else (if i.val < 786 then some 840 else some 870)) else none) else none) else none) else none) else none))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance43Pilot7
