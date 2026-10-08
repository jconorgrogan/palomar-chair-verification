module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance89Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm9, ![true, false, true, false, true, false, true], ![3, -1, 3, -1, 3, -1, 3]⟩

theorem pose_eq_original_entry89 :
    pose = Catalog7.supplied.get ⟨89, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry89]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨596, 870, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then none else (if i.val < 616 then (if i.val < 588 then none else (if i.val < 602 then (if i.val < 595 then none else (if i.val < 598 then (if i.val < 596 then none else (if i.val < 597 then some 870 else some 886)) else (if i.val < 600 then (if i.val < 599 then some 895 else some 442) else (if i.val < 601 then some 668 else some 782)))) else (if i.val < 609 then (if i.val < 605 then (if i.val < 603 then some 840 else none) else none) else none))) else none)) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance89Pilot7
