module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance340Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm8, ![false, true, false, false, false, true, true], ![-1, 3, -1, -1, -1, 3, 3]⟩

theorem pose_eq_original_entry340 :
    pose = Catalog7.supplied.get ⟨340, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry340]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨245, 870, fun i => (if i.val < 448 then (if i.val < 224 then none else (if i.val < 336 then (if i.val < 280 then (if i.val < 252 then (if i.val < 238 then none else (if i.val < 245 then none else (if i.val < 248 then (if i.val < 246 then some 870 else (if i.val < 247 then some 840 else some 782)) else (if i.val < 250 then (if i.val < 249 then some 668 else some 442) else (if i.val < 251 then some 895 else some 886))))) else none) else none) else none)) else none)⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance340Pilot7
