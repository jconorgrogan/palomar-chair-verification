module
public import SampleAcceptanceGeneric
public import Acceptance155Chunk00
public import Acceptance155Chunk01
public import Acceptance155Chunk02
public import Acceptance155Chunk03
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance155Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open SampleAcceptanceGeneric7

/-- Exact partition of all896 slots into 256+256+256+128, with no padding. -/
theorem all_facets_checked (i : Fin 896) : FacetChecked i := by
  by_cases h : i.val < 768
  · have hall : ∀ b : Fin 3, ∀ j : Fin 256, FacetChecked (chunkIndex b j) := by
      intro b
      fin_cases b
      · exact chunk00
      · exact chunk01
      · exact chunk02
    let b : Fin 3 := ⟨i.val / 256, by omega⟩
    let j : Fin 256 := ⟨i.val % 256, by omega⟩
    have hi : chunkIndex b j = i := by
      apply Fin.ext
      simp only [chunkIndex, b, j]
      omega
    simpa only [hi] using hall b j
  · let j : Fin 128 := ⟨i.val - 768, by omega⟩
    have hi : tailIndex j = i := by
      apply Fin.ext
      simp only [tailIndex, j]
      omega
    simpa only [hi] using chunk03 j

/-- All127 carrier cells, rather than sampled carriers. -/
theorem carrier_count_checked : (chairCells 7).card = 127 := by decide

theorem disjoint_checked : ∀ c ∈ chairCells 7, ¬ IsChairCell (pose.inverseCell c) := by decide

theorem fast_acceptance : geometry.FastAcceptanceValid pose certificate :=
  ⟨disjoint_checked, by decide, all_facets_checked⟩

theorem acceptance : geometry.AcceptanceValid pose certificate.mates :=
  IndexedGeometry.fastAcceptance_valid cells_eq fast_acceptance

theorem legal_contact : geometry.LegalContact pose :=
  IndexedGeometry.acceptance_sound facet_owned facet_injective acceptance

theorem occupied_profile_mate {i : Fin 896}
    (occupied : (geometry.facet i).neighbor ∈ geometry.cells.image pose.cell) :
    ∃ j, Shared pose (geometry.facet i) (geometry.facet j) ∧
      geometry.profile i = (geometry.profile j).image (pose.boxKey geometry.denominator) :=
  mate_of_acceptance acceptance occupied

theorem occupied_key_mate {i : Fin 896}
    (occupied : (geometry.facet i).neighbor ∈ geometry.cells.image pose.cell)
    {root : BoxKey 7} (hr : root ∈ geometry.profile i) :
    ∃ j, ∃ source ∈ geometry.profile j,
      Shared pose (geometry.facet i) (geometry.facet j) ∧
      root = pose.boxKey geometry.denominator source :=
  key_mate_of_acceptance acceptance occupied hr

theorem shared_box_profiles {i j : Fin 896}
    (shared : Shared pose (geometry.facet i) (geometry.facet j)) :
    geometry.profile i = (geometry.profile j).image (pose.boxKey geometry.denominator) :=
  profiles_of_acceptance facet_owned facet_injective acceptance shared

theorem mate_count_checked :
    (Finset.univ.filter (fun i : Fin 896 => (certificate.mates i).isSome)).card = 63 := by decide

theorem original_entry155_fast_acceptance :
    geometry.FastAcceptanceValid (Catalog7.supplied.get ⟨155, by decide⟩) certificate := by
  rw [← pose_eq_original_entry155]
  exact fast_acceptance

theorem original_entry155_legal :
    geometry.LegalContact (Catalog7.supplied.get ⟨155, by decide⟩) := by
  rw [← pose_eq_original_entry155]
  exact legal_contact

#print axioms pose_eq_original_entry155
#print axioms pose_mem_originalM7
#print axioms all_facets_checked
#print axioms carrier_count_checked
#print axioms mate_count_checked
#print axioms disjoint_checked
#print axioms fast_acceptance
#print axioms acceptance
#print axioms legal_contact
#print axioms occupied_key_mate
#print axioms shared_box_profiles
#print axioms original_entry155_fast_acceptance
#print axioms original_entry155_legal
end SparseMonotiles.Contact.Acceptance155Pilot7
