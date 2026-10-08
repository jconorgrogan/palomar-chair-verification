module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance232Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm0, ![false, false, true, true, true, true, false], ![-1, -1, 3, 3, 3, 3, -1]⟩

theorem pose_eq_original_entry232 :
    pose = Catalog7.supplied.get ⟨232, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry232]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨210, 442, fun i => (if i.val < 448 then (if i.val < 224 then (if i.val < 112 then none else (if i.val < 168 then none else (if i.val < 196 then none else (if i.val < 210 then none else (if i.val < 217 then (if i.val < 213 then (if i.val < 211 then some 442 else (if i.val < 212 then some 668 else some 782)) else (if i.val < 215 then (if i.val < 214 then some 840 else some 870) else (if i.val < 216 then some 886 else some 895))) else none))))) else none) else none)⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance232Pilot7
