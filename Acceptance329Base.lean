module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance329Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm7, ![false, false, false, true, false, true, false], ![-1, -1, -1, 3, -1, 3, -1]⟩

theorem pose_eq_original_entry329 :
    pose = Catalog7.supplied.get ⟨329, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry329]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨70, 840, fun i => (if i.val < 448 then (if i.val < 224 then (if i.val < 112 then (if i.val < 56 then none else (if i.val < 84 then (if i.val < 70 then none else (if i.val < 77 then (if i.val < 73 then (if i.val < 71 then some 840 else (if i.val < 72 then some 870 else some 886)) else (if i.val < 75 then (if i.val < 74 then some 895 else some 442) else (if i.val < 76 then some 668 else some 782))) else none)) else none)) else none) else none) else none)⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance329Pilot7
