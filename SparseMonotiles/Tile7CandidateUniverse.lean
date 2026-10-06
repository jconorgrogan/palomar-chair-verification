module

public import SparseMonotiles.ProfileCertificates7

@[expose] public section

/-! The exact elementary profile conditions close the hypotheses of the
registered all-key-pair generator theorem. Equality between that generated
set and any exported certificate row table is a separate obligation. -/
namespace SparseMonotiles

open Contact

attribute [local irreducible] IndexedGeometry.generatedCandidates

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Every registered literal-profile contact of the exact indexed geometry
belongs to its executable all-key-pair candidate set. -/
theorem T7_registered_contact_in_generatedCandidates {p : Pose 7}
    (h : IndexedData7.geometry.LegalContact p) :
    p ∈ IndexedData7.geometry.generatedCandidates :=
  IndexedGeometry.legalContact_mem_generatedCandidates (g := IndexedData7.geometry) (by decide)
    (fun i => (profile7_checked i).1)
    (fun i b hb => ((profile7_checked i).2 b hb).1)
    (fun i b hb => ((profile7_checked i).2 b hb).2.1) h

/-- Each physical key uses the correct sign of its exact normal height. -/
theorem T7_indexed_keys_oriented (i : Fin 896) (b : BoxKey 7) (hb : b ∈ IndexedData7.geometry.profile i) :
    b.OrientedAt IndexedData7.geometry.denominator 560 (IndexedData7.geometry.facet i) :=
  ((profile7_checked i).2 b hb).2.2

#print axioms T7_registered_contact_in_generatedCandidates
#print axioms T7_indexed_keys_oriented

end SparseMonotiles
