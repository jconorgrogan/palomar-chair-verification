module

public import SparseMonotiles.ProfileCertificates5

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
theorem T5_registered_contact_in_generatedCandidates {p : Pose 5}
    (h : IndexedData5.geometry.LegalContact p) :
    p ∈ IndexedData5.geometry.generatedCandidates :=
  IndexedGeometry.legalContact_mem_generatedCandidates (g := IndexedData5.geometry) (by decide)
    (fun i => (profile5_checked i).1)
    (fun i b hb => ((profile5_checked i).2 b hb).1)
    (fun i b hb => ((profile5_checked i).2 b hb).2.1) h

/-- Each physical key uses the correct sign of its exact normal height. -/
theorem T5_indexed_keys_oriented (i : Fin 160) (b : BoxKey 5) (hb : b ∈ IndexedData5.geometry.profile i) :
    b.OrientedAt IndexedData5.geometry.denominator 80 (IndexedData5.geometry.facet i) :=
  ((profile5_checked i).2 b hb).2.2

#print axioms T5_registered_contact_in_generatedCandidates
#print axioms T5_indexed_keys_oriented

end SparseMonotiles
