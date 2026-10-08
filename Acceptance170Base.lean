module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance170Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm2, ![true, true, true, false, true, true, false], ![3, 3, 3, -1, 3, 3, -1]⟩

theorem pose_eq_original_entry170 :
    pose = Catalog7.supplied.get ⟨170, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry170]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨829, 668, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then none else (if i.val < 840 then (if i.val < 812 then none else (if i.val < 826 then none else (if i.val < 833 then (if i.val < 829 then none else (if i.val < 831 then (if i.val < 830 then some 668 else some 442) else (if i.val < 832 then some 895 else some 886))) else (if i.val < 836 then (if i.val < 834 then some 870 else (if i.val < 835 then some 840 else some 782)) else none)))) else none))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance170Pilot7
