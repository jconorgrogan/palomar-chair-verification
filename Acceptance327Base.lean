module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance327Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm7, ![false, false, true, false, false, false, true], ![-1, -1, 3, -1, -1, -1, 3]⟩

theorem pose_eq_original_entry327 :
    pose = Catalog7.supplied.get ⟨327, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry327]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨119, 840, fun i => (if i.val < 448 then (if i.val < 224 then (if i.val < 112 then none else (if i.val < 168 then (if i.val < 140 then (if i.val < 126 then (if i.val < 119 then none else (if i.val < 122 then (if i.val < 120 then some 840 else (if i.val < 121 then some 870 else some 886)) else (if i.val < 124 then (if i.val < 123 then some 895 else some 442) else (if i.val < 125 then some 668 else some 782)))) else none) else none) else none)) else none) else none)⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance327Pilot7
