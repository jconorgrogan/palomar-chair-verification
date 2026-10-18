module

public import SparseMonotiles.CoarseContactCertificates5Coverage
public import SparseMonotiles.CoarseContactCertificatesLocal
public import SparseMonotiles.CarrierHierarchyPeriods

@[expose] public section

/-!
Concrete necessity and registered-world consequences of the fully checked T5
coarse table. This module must only be built after every finite row and complete
source-triple coverage chunk. It is not the arbitrary-isometry physical T5Goal.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Every disjoint touching aligned canonical parent pair whose cross-child
contacts belong to the exact supplied284-pose language halves into that language. -/
theorem t5_local_coarse_necessity (F : Pose 5) (heven : ∀ i, F.shift i % 2 = 0)
    (hdisjoint : ∀ x, ¬ (ParentOccupies (rootPose 5) x ∧ ParentOccupies F x))
    (hlegal : CanonicalCrossLegal CoarseContactCertificates5.C M5 F)
    {x y : Cell 5} (hx : ParentOccupies (rootPose 5) x) (hy : ParentOccupies F y)
    (hadj : AdjacentCells x y) : coarsePose (fun _ => 0) F ∈ M5 :=
  indexed_local_coarse_certificate CoarseContactCertificates5.C CoarseContactCertificates5.L
    CoarseContactCertificates5.child_table_covers CoarseContactCertificates5SymmetryCoverage.symmetricRows
    CoarseContactCertificates5SymmetryCoverage.symmetric_rows_valid CoarseContactCertificates5SymmetryCoverage.symmetric_candidate_complete
    F heven hdisjoint hlegal hx hy hadj

/-- No extra candidate table, hierarchy, or coarse-law premise remains. -/
theorem t5_registered_coarsen_legal (W : RegisteredWorld 5) (hl : W.Legal M5)
    (p₀ : Pose 5) (hp₀ : CompleteParent Catalog5.childPerm Catalog5.r W.tiles p₀) :
    (W.coarsen (by decide) Catalog5.r_involutive Catalog5.child_rule_equivariant
      Catalog5.local_catalog hl p₀ hp₀).Legal M5 :=
  W.coarsen_legal (by decide) Catalog5.r_involutive Catalog5.child_rule_equivariant
    CoarseContactCertificates5.C CoarseContactCertificates5.L
    CoarseContactCertificates5.canonical_table CoarseContactCertificates5.gauge_closed
    Catalog5.local_catalog hl CoarseContactCertificates5SymmetryCoverage.symmetricRows
    CoarseContactCertificates5SymmetryCoverage.symmetric_rows_valid CoarseContactCertificates5SymmetryCoverage.symmetric_candidate_complete p₀ hp₀

/-- A registered M5-legal world has no nonzero integer translation period.
Physical registration and physical-period representative transport remain separate. -/
theorem t5_registered_period_zero (W : RegisteredWorld 5) (hl : W.Legal M5)
    (v : Cell 5) (hv : W.IsPeriod v) : v = 0 :=
  registered_period_zero (by decide) Catalog5.r_involutive Catalog5.child_rule_equivariant
    CoarseContactCertificates5.C CoarseContactCertificates5.L
    CoarseContactCertificates5.canonical_table CoarseContactCertificates5.gauge_closed
    Catalog5.local_catalog CoarseContactCertificates5SymmetryCoverage.symmetricRows
    CoarseContactCertificates5SymmetryCoverage.symmetric_rows_valid CoarseContactCertificates5SymmetryCoverage.symmetric_candidate_complete W hl v hv

#print axioms t5_local_coarse_necessity
#print axioms t5_registered_coarsen_legal
#print axioms t5_registered_period_zero
end SparseMonotiles.CarrierHierarchy
