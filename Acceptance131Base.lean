module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance131Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm5, ![true, true, true, true, false, false, false], ![3, 3, 3, 3, -1, -1, -1]⟩

theorem pose_eq_original_entry131 :
    pose = Catalog7.supplied.get ⟨131, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry131]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨844, 782, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then none else (if i.val < 840 then none else (if i.val < 868 then (if i.val < 854 then (if i.val < 847 then (if i.val < 843 then none else (if i.val < 845 then (if i.val < 844 then none else some 782) else (if i.val < 846 then some 840 else some 870))) else (if i.val < 850 then (if i.val < 848 then some 886 else (if i.val < 849 then some 895 else some 442)) else (if i.val < 852 then (if i.val < 851 then some 668 else none) else none))) else none) else none)))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance131Pilot7
