module
public import T7DirectMatchedBlockCoverage
public import T7MatchedKeyReduction
@[expose] public section
namespace SparseMonotiles.T7DirectMatchedPhysicalAssembly
open Contact CarrierHierarchy T7DirectMatchedBlockCoverage

/-- Lightweight production indexing is definitionally the already checked
complete polarity indexing; this does not trust an external address map. -/
theorem bumpIndex_eq : T7ReducedIndexData.bumpIndex = T7PolarityIndexing.bumpIndex := rfl
theorem dentIndex_eq : T7ReducedIndexData.dentIndex = T7PolarityIndexing.dentIndex := rfl

theorem contact_mem_M7_of_all_match_pairs (pairs : ∀ a b : Fin 512, PairLaw a b)
    {p : Pose 7} (legal : IndexedData7.geometry.LegalContact p) : p ∈ M7 := by
  apply T7MatchedKeyReduction.contact_mem_M7_of_512_matched_key_classifications ?_ legal
  intro a b q matched hq
  exact pairs a b q
    (T7MatchedKeyReduction.indexed_key_asymmetric (T7PolarityIndexing.dentIndex b)) matched hq

theorem contact_mem_M7_of_2048_matched_blocks
    (blocks : ∀ (a : Fin 512) (c : Fin 4), BlockLaw128 a c)
    {p : Pose 7} (legal : IndexedData7.geometry.LegalContact p) : p ∈ M7 :=
  contact_mem_M7_of_all_match_pairs (all_pairs_of_2048_blocks blocks) legal

theorem contact_mem_M7_of_1024_matched_blocks
    (blocks : ∀ (a : Fin 512) (c : Fin 2), BlockLaw256 a c)
    {p : Pose 7} (legal : IndexedData7.geometry.LegalContact p) : p ∈ M7 :=
  contact_mem_M7_of_all_match_pairs (all_pairs_of_1024_blocks blocks) legal

#print axioms bumpIndex_eq
#print axioms dentIndex_eq
#print axioms contact_mem_M7_of_all_match_pairs
#print axioms contact_mem_M7_of_2048_matched_blocks
#print axioms contact_mem_M7_of_1024_matched_blocks
end SparseMonotiles.T7DirectMatchedPhysicalAssembly
