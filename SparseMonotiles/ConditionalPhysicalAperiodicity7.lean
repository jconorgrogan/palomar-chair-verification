module

public import SparseMonotiles.GlobalPhysicalRegistration
public import SparseMonotiles.PhysicalContactWorldLaw
public import SparseMonotiles.PrescribedContactProfiles7
public import CompactCatalogBinding7

@[expose] public section

/-! Exact compact T7 physical aperiodicity conditional on complete indexed
contact classification. The classification hypothesis is intentionally explicit;
this module does not prove it or assert tiling existence. -/
namespace SparseMonotiles
open Set Contact CarrierHierarchy

/-- Global registration, physical contact profiles, and exact real unmarked
period transport reduce the physical aperiodicity goal to one classification
implication for the exact indexed geometry. -/
theorem T7_isAperiodic_of_indexed_contact_classification
    (hclassify : ∀ p : Pose 7, IndexedData7.geometry.LegalContact p → p ∈ M7) :
    IsAperiodic T7 := by
  apply isAperiodic_of_registered_legal_frames T7 T7_isCompact T7_cellCentre_mem_iff
    (fun _ hc => T7_cellCentre_mem_interior hc) M7 ?_
    CompactCatalogBinding7.registered_compact7_period_zero
  intro tiles ht g hg
  obtain ⟨e, q, hreg⟩ := T7_global_registered_frames ht g hg
  refine ⟨e, q, hreg, ?_⟩
  apply registered_range_law_of_native_physical_law g e q hreg M7
  intro A B p hBA hp hcontact
  exact hclassify p (T7_native_contact_legal ht g hg A B p hBA hp hcontact)

#print axioms T7_isAperiodic_of_indexed_contact_classification
end SparseMonotiles
