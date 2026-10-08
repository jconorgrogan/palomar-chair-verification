module
public import SparseMonotiles.GeneratorRowCoverage
@[expose] public section
namespace SparseMonotiles.Contact

/-- Every mathematical generator member has a pair of flat key indices.
This uses profile coverage, not any certificate or replay-row claim. -/
theorem KeyIndexing.exists_pair_of_mem_generatedCandidates
    {d n m : ℕ} {g : IndexedGeometry d n} (keys : KeyIndexing g m)
    {p : Pose d} (generated : p ∈ g.generatedCandidates) :
    ∃ a b : Fin m, keys.pair a b = some p := by
  rcases Finset.mem_biUnion.mp generated with ⟨i, _, hi⟩
  rcases Finset.mem_biUnion.mp hi with ⟨j, _, hj⟩
  rcases Finset.mem_biUnion.mp hj with ⟨root, hroot, hr⟩
  rcases Finset.mem_biUnion.mp hr with ⟨source, hsource, hp⟩
  obtain ⟨a, hai, har⟩ := keys.covers hroot
  obtain ⟨b, hbj, hbs⟩ := keys.covers hsource
  exact ⟨a, b, by simpa [KeyIndexing.pair, hai, hbj, har, hbs] using hp⟩

/-- The reverse direction needs membership of every flat index, because
`KeyIndexing` itself allows unused indices. -/
theorem KeyIndexing.mem_generatedCandidates_of_pair
    {d n m : ℕ} {g : IndexedGeometry d n} (keys : KeyIndexing g m)
    (source_mem : ∀ a, keys.key a ∈ g.profile (keys.facet a))
    {a b : Fin m} {p : Pose d} (generated : keys.pair a b = some p) :
    p ∈ g.generatedCandidates := by
  apply Finset.mem_biUnion.mpr
  refine ⟨keys.facet a, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨keys.facet b, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨keys.key a, source_mem a, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨keys.key b, source_mem b, ?_⟩
  simpa [KeyIndexing.pair] using generated

/-- A exact generator enumeration, conditional on no unused flat indices. -/
theorem KeyIndexing.mem_generatedCandidates_iff_exists_pair
    {d n m : ℕ} {g : IndexedGeometry d n} (keys : KeyIndexing g m)
    (source_mem : ∀ a, keys.key a ∈ g.profile (keys.facet a)) (p : Pose d) :
    p ∈ g.generatedCandidates ↔ ∃ a b : Fin m, keys.pair a b = some p := by
  constructor
  · exact keys.exists_pair_of_mem_generatedCandidates
  · rintro ⟨a, b, generated⟩
    exact keys.mem_generatedCandidates_of_pair source_mem generated

/-- A conditional reduction only: the law for all indexed pairs remains
an explicit premise. No replay table coverage or classification is inferred. -/
theorem KeyIndexing.classify_generated_of_pair_law
    {d n m : ℕ} {g : IndexedGeometry d n} (keys : KeyIndexing g m)
    {P : Pose d → Prop}
    (pair_law : ∀ a b p, keys.pair a b = some p → g.LegalContact p → P p)
    {p : Pose d} (generated : p ∈ g.generatedCandidates)
    (legal : g.LegalContact p) : P p := by
  obtain ⟨a, b, hp⟩ := keys.exists_pair_of_mem_generatedCandidates generated
  exact pair_law a b p hp legal

#print axioms KeyIndexing.exists_pair_of_mem_generatedCandidates
#print axioms KeyIndexing.mem_generatedCandidates_of_pair
#print axioms KeyIndexing.mem_generatedCandidates_iff_exists_pair
#print axioms KeyIndexing.classify_generated_of_pair_law
end SparseMonotiles.Contact
