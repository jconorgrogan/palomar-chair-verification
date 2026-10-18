module

public import SparseMonotiles.CarrierHierarchyCatalog5
public import SparseMonotiles.ContactCertificateDataIndexed5RegistryIndices

@[expose] public section

/-! Indexed equality bridge between the hierarchy's literal JSON catalog and
the independently replayed contact registry. No JSON hash is used as proof. -/
namespace SparseMonotiles.CarrierHierarchy.ContactBinding5
open Contact
set_option maxRecDepth 100000

def hierarchyAt (i : Fin 284) : Pose 5 := Catalog5.supplied.get
  ⟨i.val, by simpa only [Catalog5.supplied_count] using i.isLt⟩

noncomputable def contactAt (i : Fin 284) : Pose 5 :=
  IndexedData5.RegistryIndices.acceptedAt (IndexedData5.RegistryIndices.registryOrder i)

def bindingIndex (b : Fin 9) (i : Fin 32) : Fin 284 :=
  ⟨min (32 * b.val + i.val) 283, by omega⟩

theorem hierarchy_indexed (p : Pose 5) : p ∈ Catalog5.supplied ↔ ∃ i, hierarchyAt i = p := by
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    exact ⟨⟨i.val, by simpa only [Catalog5.supplied_count] using i.isLt⟩, hi⟩
  · rintro ⟨i, rfl⟩
    exact List.get_mem _ _

theorem contact_indexed (p : Pose 5) :
    p ∈ IndexedData5.RegistryIndices.registryList ↔ ∃ i, contactAt i = p := by
  rw [← IndexedData5.RegistryIndices.registry_binding]
  exact List.mem_ofFn
end SparseMonotiles.CarrierHierarchy.ContactBinding5
