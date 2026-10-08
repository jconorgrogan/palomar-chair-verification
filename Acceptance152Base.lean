module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance152Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm5, ![true, false, false, true, true, false, true], ![3, -1, -1, 3, 3, -1, 3]⟩

theorem pose_eq_original_entry152 :
    pose = Catalog7.supplied.get ⟨152, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry152]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨540, 782, fun i => (if i.val < 448 then none else (if i.val < 672 then (if i.val < 560 then (if i.val < 504 then none else (if i.val < 532 then none else (if i.val < 546 then (if i.val < 539 then none else (if i.val < 542 then (if i.val < 540 then none else (if i.val < 541 then some 782 else some 840)) else (if i.val < 544 then (if i.val < 543 then some 870 else some 886) else (if i.val < 545 then some 895 else some 442)))) else (if i.val < 553 then (if i.val < 549 then (if i.val < 547 then some 668 else none) else none) else none)))) else none) else none))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance152Pilot7
