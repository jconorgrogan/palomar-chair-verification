module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance16Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm12, ![true, true, false, false, true, false, true], ![3, 3, -1, -1, 3, -1, 3]⟩

theorem pose_eq_original_entry16 :
    pose = Catalog7.supplied.get ⟨16, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry16]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨709, 895, fun i => (if i.val < 448 then none else (if i.val < 672 then none else (if i.val < 784 then (if i.val < 728 then (if i.val < 700 then none else (if i.val < 714 then (if i.val < 707 then none else (if i.val < 710 then (if i.val < 708 then none else (if i.val < 709 then none else some 895)) else (if i.val < 712 then (if i.val < 711 then some 442 else some 668) else (if i.val < 713 then some 782 else some 840)))) else (if i.val < 721 then (if i.val < 717 then (if i.val < 715 then some 870 else (if i.val < 716 then some 886 else none)) else none) else none))) else none) else none)))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance16Pilot7
