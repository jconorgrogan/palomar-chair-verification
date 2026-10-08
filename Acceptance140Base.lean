module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance140Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm4, ![true, true, false, false, false, true, false], ![3, 3, -1, -1, -1, 3, -1]⟩

theorem pose_eq_original_entry140 :
    pose = Catalog7.supplied.get ⟨140, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry140]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨688, 782, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then (if i.val < 728 then (if i.val < 700 then (if i.val < 686 then none else (if i.val < 693 then (if i.val < 689 then (if i.val < 687 then none else (if i.val < 688 then none else some 782)) else (if i.val < 691 then (if i.val < 690 then some 668 else some 442) else (if i.val < 692 then some 895 else some 886))) else (if i.val < 696 then (if i.val < 694 then some 870 else (if i.val < 695 then some 840 else none)) else none))) else none) else none) else none)))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance140Pilot7
