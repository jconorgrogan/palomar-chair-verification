module

public import SparseMonotiles.CoarseContactCertificates5SymmetryRepresentativeCoverage
public import SparseMonotiles.CoarseContactCertificates5SymmetryTransport

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5SymmetryCoverage
open Contact CoarseContactCertificates5 CoarseContactCertificates5Symmetry
abbrev SymmetricAddress := RowAddress × Fin 4
def symmetricRows : SymmetricAddress → CoarseRow 5 := expandedRows rowLookup
theorem symmetric_rows_valid (a : SymmetricAddress) :
    (symmetricRows a).witness.Valid C L (symmetricRows a).pose :=
  expandedRows_valid rowLookup all_rows_valid a
theorem symmetric_candidate_complete (a : Pose 5) (ha : a ∈ C) (b : Pose 5) (hb : b ∈ C)
    (k : Pose 5) (hk : k ∈ L)
    (heven : ∀ i, (parentCandidate a b k).shift i % 2 = 0) :
    ∃ r, parentCandidate a b k = (symmetricRows r).pose :=
  expandedRows_complete rowLookup representative_complete a ha b hb k hk heven
#print axioms symmetric_rows_valid
#print axioms symmetric_candidate_complete
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5SymmetryCoverage
