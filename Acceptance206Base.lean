module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance206Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm0, ![true, false, false, true, false, true, true], ![3, -1, -1, 3, -1, 3, 3]⟩

theorem pose_eq_original_entry206 :
    pose = Catalog7.supplied.get ⟨206, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry206]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨526, 442, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then (if i.val < 504 then none else (if i.val < 532 then (if i.val < 518 then none else (if i.val < 525 then none else (if i.val < 528 then (if i.val < 526 then none else (if i.val < 527 then some 442 else some 668)) else (if i.val < 530 then (if i.val < 529 then some 782 else some 840) else (if i.val < 531 then some 870 else some 886))))) else (if i.val < 546 then (if i.val < 539 then (if i.val < 535 then (if i.val < 533 then some 895 else none) else none) else none) else none))) else none) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance206Pilot7
