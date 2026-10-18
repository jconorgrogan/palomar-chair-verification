module

public import SparseMonotiles.ContactChairChecker

@[expose] public section

namespace SparseMonotiles.Contact

@[simp] theorem indexedAcceptedPoses_append {d n : ℕ} (a b : List (IndexedRow d n)) :
    indexedAcceptedPoses (a ++ b) = indexedAcceptedPoses a ++ indexedAcceptedPoses b := by
  simp [indexedAcceptedPoses, List.filter_append, List.map_append]

/-- Exhaustiveness of the candidate generator is a separate explicit hypothesis. -/
theorem indexed_contact_language_exact_of_complete {d n : ℕ} {g : IndexedGeometry d n}
    (cells_eq : g.cells = chairCells d) (owned : ∀ j, (g.facet j).cell ∈ g.cells)
    (unique : Function.Injective g.facet) {rows : List (IndexedRow d n)}
    (valid : indexedValidate g rows = true)
    (complete : ∀ p, g.LegalContact p → ∃ row ∈ rows, row.pose = p) :
    ∀ p, g.LegalContact p ↔ p ∈ indexedAcceptedPoses rows := by
  intro p
  constructor
  · intro h
    rcases complete p h with ⟨r, hr, hp⟩
    exact (indexed_candidate_language_exact cells_eq owned unique valid p).mp
      ⟨List.mem_map.mpr ⟨r, hr, hp⟩, h⟩
  · intro h
    exact ((indexed_candidate_language_exact cells_eq owned unique valid p).mpr h).2

#print axioms indexed_contact_language_exact_of_complete
end SparseMonotiles.Contact
