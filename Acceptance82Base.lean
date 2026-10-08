module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance82Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm8, ![true, false, true, true, false, false, false], ![3, -1, 3, 3, -1, -1, -1]⟩

theorem pose_eq_original_entry82 :
    pose = Catalog7.supplied.get ⟨82, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry82]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨617, 870, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then none else (if i.val < 616 then none else (if i.val < 644 then (if i.val < 630 then (if i.val < 623 then (if i.val < 619 then (if i.val < 617 then none else (if i.val < 618 then some 870 else some 840)) else (if i.val < 621 then (if i.val < 620 then some 782 else some 668) else (if i.val < 622 then some 442 else some 895))) else (if i.val < 626 then (if i.val < 624 then some 886 else none) else none)) else none) else none))) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance82Pilot7
