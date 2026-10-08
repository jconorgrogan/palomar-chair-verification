module
public import T7KeyIndexing
public import SparseMonotiles.Tile7CandidateUniverse
public import SparseMonotiles.ConditionalPhysicalAperiodicity7
public import CatalogInverseClosure
@[expose] public section

/-! Exact reduction of all legal compact T7 contacts to indexed pair laws.
No exhaustive pair-law or replay-table certificate is asserted here. -/
namespace SparseMonotiles
open Contact CarrierHierarchy
set_option maxRecDepth 100000
attribute [local irreducible] IndexedGeometry.generatedCandidates

/-- Every legal contact has an actual pairPose witness among all 1024² indexed
pairs, including all profile keys rather than a selected key per facet. -/
theorem T7_legalContact_exists_indexed_pair {p : Pose 7}
    (hlegal : IndexedData7.geometry.LegalContact p) :
    ∃ a b : Fin 1024, T7KeyIndexing.generatorIndexingT7.pair a b = some p :=
  (T7KeyIndexing.generated_iff_pair p).mp
    (T7_registered_contact_in_generatedCandidates hlegal)

/-- A law for every indexed pair suffices for full contact classification.
The universal pair-law hypothesis remains explicit and unproved. -/
theorem T7_contact_mem_M7_of_all_indexed_pair_classifications
    (hpairs : ∀ (a b : Fin 1024) (p : Pose 7),
      T7KeyIndexing.generatorIndexingT7.pair a b = some p →
      IndexedData7.geometry.LegalContact p → p ∈ M7)
    {p : Pose 7} (hlegal : IndexedData7.geometry.LegalContact p) : p ∈ M7 := by
  obtain ⟨a, b, hpair⟩ := T7_legalContact_exists_indexed_pair hlegal
  exact hpairs a b p hpair hlegal

/-- Conditional physical endpoint. This does not supply the all-pairs proof
or tiling existence. Four checked root blocks cannot discharge this premise. -/
theorem T7_isAperiodic_of_all_indexed_pair_classifications
    (hpairs : ∀ (a b : Fin 1024) (p : Pose 7),
      T7KeyIndexing.generatorIndexingT7.pair a b = some p →
      IndexedData7.geometry.LegalContact p → p ∈ M7) : IsAperiodic T7 :=
  T7_isAperiodic_of_indexed_contact_classification
    (fun _ hlegal => T7_contact_mem_M7_of_all_indexed_pair_classifications hpairs hlegal)

#print axioms T7_legalContact_exists_indexed_pair
#print axioms T7_contact_mem_M7_of_all_indexed_pair_classifications
#print axioms T7_isAperiodic_of_all_indexed_pair_classifications
end SparseMonotiles
