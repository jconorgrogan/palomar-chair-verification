module

public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk0
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk1
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk2
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk3
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk4
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk5
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk6
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk7
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5Chunk8
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Sufficiency-only binding of the exact hierarchy catalog to checked full
facet-mate certificates. No necessity or candidate-exhaustiveness claim. -/
namespace SparseMonotiles.CarrierHierarchy.AcceptanceBinding5
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

theorem catalog_mem_iff_registry (p : Pose 5) :
    p ∈ Catalog5.supplied ↔ p ∈ IndexedData5.AcceptedSufficiency.frozenSet := by
  change p ∈ Catalog5.supplied ↔ p ∈ IndexedData5.AcceptedSufficiency.registryList.toFinset
  rw [List.mem_toFinset, hierarchy_indexed, contact_indexed]
  simp only [all_bindings]

theorem catalog_mateCertificate {p : Pose 5} (hp : p ∈ Catalog5.supplied) :
    ∃ cert : MateCertificate 160, IndexedData5.geometry.FastAcceptanceValid p cert :=
  IndexedData5.AcceptedSufficiency.mateCertificate_of_mem ((catalog_mem_iff_registry p).mp hp)

theorem catalog_key_mate {p : Pose 5} (hp : p ∈ Catalog5.supplied) {i : Fin 160}
    (occupied : (IndexedData5.geometry.facet i).neighbor ∈
      IndexedData5.geometry.cells.image p.cell)
    {root : BoxKey 5} (hr : root ∈ IndexedData5.geometry.profile i) :
    ∃ j, ∃ source ∈ IndexedData5.geometry.profile j,
      Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j) ∧
      root = p.boxKey IndexedData5.geometry.denominator source :=
  IndexedData5.AcceptedSufficiency.key_mate_of_mem ((catalog_mem_iff_registry p).mp hp)
    occupied hr

#print axioms catalog_mem_iff_registry
#print axioms catalog_mateCertificate
#print axioms catalog_key_mate
end SparseMonotiles.CarrierHierarchy.AcceptanceBinding5
