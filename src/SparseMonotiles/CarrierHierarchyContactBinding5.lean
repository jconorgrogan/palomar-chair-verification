module

public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk0
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk1
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk2
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk3
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk4
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk5
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk6
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk7
public import SparseMonotiles.CarrierHierarchyContactBinding5Chunk8
public import SparseMonotiles.GeneratorRowCoverage5
public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.ContactBinding5
open Contact

theorem all_bindings (i : Fin 284) : hierarchyAt i = contactAt i := by
  have hall : ∀ b : Fin 9, ∀ j : Fin 32, hierarchyAt (bindingIndex b j) = contactAt (bindingIndex b j) := by
    intro b
    fin_cases b
    · exact chunk0
    · exact chunk1
    · exact chunk2
    · exact chunk3
    · exact chunk4
    · exact chunk5
    · exact chunk6
    · exact chunk7
    · exact chunk8
  let b : Fin 9 := ⟨i.val / 32, by omega⟩
  let j : Fin 32 := ⟨i.val % 32, by omega⟩
  have he : bindingIndex b j = i := by apply Fin.ext; simp only [bindingIndex, b, j]; omega
  simpa only [he] using hall b j

theorem catalog_mem_iff_frozen (p : Pose 5) : p ∈ M5 ↔ p ∈ IndexedData5.frozenPoseSet := by
  change p ∈ Catalog5.supplied ↔ p ∈ IndexedData5.RegistryIndices.registryList.toFinset
  rw [List.mem_toFinset, hierarchy_indexed, contact_indexed]
  simp only [all_bindings]

theorem catalog_eq_frozen : M5 = {p | p ∈ IndexedData5.frozenPoseSet} := by
  ext p
  exact catalog_mem_iff_frozen p

theorem catalog_finset_eq_frozen : Catalog5.supplied.toFinset = IndexedData5.frozenPoseSet := by
  ext p
  rw [List.mem_toFinset]
  exact catalog_mem_iff_frozen p

theorem catalog_card : Catalog5.supplied.toFinset.card = 284 := by
  rw [catalog_finset_eq_frozen]
  exact IndexedData5.registered_contact_exact_284.1

/-- Exact source binding: the checked registered contact law now uses the
same literal M5 language as the hierarchy and its finite coarse certificates. -/
theorem registered_contact_exact_catalog (p : Pose 5) :
    IndexedData5.geometry.LegalContact p ↔ p ∈ M5 :=
  (IndexedData5.registered_contact_exact_frozen p).trans (catalog_mem_iff_frozen p).symm

#print axioms all_bindings
#print axioms catalog_eq_frozen
#print axioms catalog_card
#print axioms registered_contact_exact_catalog
end SparseMonotiles.CarrierHierarchy.ContactBinding5
