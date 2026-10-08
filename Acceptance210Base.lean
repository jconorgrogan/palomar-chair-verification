module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance210Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm1, ![true, false, true, false, false, true, false], ![3, -1, 3, -1, -1, 3, -1]⟩

theorem pose_eq_original_entry210 :
    pose = Catalog7.supplied.get ⟨210, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry210]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨575, 442, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then none else (if i.val < 616 then (if i.val < 588 then (if i.val < 574 then none else (if i.val < 581 then (if i.val < 577 then (if i.val < 575 then none else (if i.val < 576 then some 442 else some 895)) else (if i.val < 579 then (if i.val < 578 then some 886 else some 870) else (if i.val < 580 then some 840 else some 782))) else (if i.val < 584 then (if i.val < 582 then some 668 else none) else none))) else none) else none)) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance210Pilot7
