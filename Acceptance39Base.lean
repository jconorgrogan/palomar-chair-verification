module
public import SparseMonotiles.ContactCertificateDataIndexed7Base
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance39Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pose : Pose 7 := ⟨Catalog7.perm11, ![true, true, true, false, true, false, false], ![3, 3, 3, 1, 3, 1, 1]⟩

theorem pose_eq_original_entry39 :
    pose = Catalog7.supplied.get ⟨39, by decide⟩ := rfl

theorem pose_mem_originalM7 : pose ∈ M7 := by
  change pose ∈ Catalog7.supplied
  rw [pose_eq_original_entry39]
  exact List.get_mem _ _

def certificate : MateCertificate 896 := ⟨442, 587, fun i => (if i.val < 448 then (if i.val < 224 then none else (if i.val < 336 then none else (if i.val < 392 then none else (if i.val < 420 then none else (if i.val < 434 then none else (if i.val < 441 then none else (if i.val < 444 then (if i.val < 442 then none else (if i.val < 443 then some 587 else none)) else none))))))) else (if i.val < 672 then (if i.val < 560 then none else (if i.val < 616 then none else (if i.val < 644 then none else (if i.val < 658 then none else (if i.val < 665 then none else (if i.val < 668 then none else (if i.val < 670 then (if i.val < 669 then some 588 else none) else none))))))) else (if i.val < 784 then (if i.val < 728 then none else (if i.val < 756 then none else (if i.val < 770 then none else (if i.val < 777 then none else (if i.val < 780 then none else (if i.val < 782 then none else (if i.val < 783 then some 582 else none))))))) else (if i.val < 840 then none else (if i.val < 868 then (if i.val < 854 then (if i.val < 847 then (if i.val < 843 then (if i.val < 841 then some 583 else none) else none) else none) else none) else (if i.val < 882 then (if i.val < 875 then (if i.val < 871 then (if i.val < 869 then none else (if i.val < 870 then none else some 584)) else none) else none) else (if i.val < 889 then (if i.val < 885 then none else (if i.val < 887 then (if i.val < 886 then none else some 585) else none)) else (if i.val < 892 then none else (if i.val < 894 then none else (if i.val < 895 then none else some 586))))))))))⟩

def chunkIndex (b : Fin 3) (j : Fin 256) : Fin 896 :=
  ⟨b.val * 256 + j.val, by omega⟩

def tailIndex (j : Fin 128) : Fin 896 := ⟨768 + j.val, by omega⟩

def FacetChecked (i : Fin 896) : Prop := geometry.FastAcceptanceAt pose i (certificate.mates i)
instance (i : Fin 896) : Decidable (FacetChecked i) :=
  inferInstanceAs (Decidable (geometry.FastAcceptanceAt _ _ _))
end SparseMonotiles.Contact.Acceptance39Pilot7
