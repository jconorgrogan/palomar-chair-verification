module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance128Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm5, ![true, true, true, true, true, false, true], ![3, 3, 3, 3, 3, -1, 3]⟩

theorem pose_eq_original_entry128 :
    pose = Catalog7.supplied.get ⟨128, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry128]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨880, 782, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then none else (if i.val < 840 then none else (if i.val < 868 then none else (if i.val < 882 then (if i.val < 875 then none else (if i.val < 878 then none else (if i.val < 880 then none else (if i.val < 881 then some 782 else some 840)))) else (if i.val < 889 then (if i.val < 885 then (if i.val < 883 then some 870 else (if i.val < 884 then some 886 else some 895)) else (if i.val < 887 then (if i.val < 886 then some 442 else none) else (if i.val < 888 then some 668 else none))) else none)))))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance128Pilot7
