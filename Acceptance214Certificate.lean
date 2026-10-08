module
public import Acceptance214Generic
public import Acceptance214Chunk00
public import Acceptance214Chunk01
public import Acceptance214Chunk02
public import Acceptance214Chunk03
public import Acceptance214Chunk04
public import Acceptance214Chunk05
public import Acceptance214Chunk06
public import Acceptance214Chunk07
public import Acceptance214Chunk08
public import Acceptance214Chunk09
public import Acceptance214Chunk10
public import Acceptance214Chunk11
public import Acceptance214Chunk12
public import Acceptance214Chunk13
public import Acceptance214Chunk14
public import Acceptance214Chunk15
public import Acceptance214Chunk16
public import Acceptance214Chunk17
public import Acceptance214Chunk18
public import Acceptance214Chunk19
public import Acceptance214Chunk20
public import Acceptance214Chunk21
public import Acceptance214Chunk22
public import Acceptance214Chunk23
public import Acceptance214Chunk24
public import Acceptance214Chunk25
public import Acceptance214Chunk26
public import Acceptance214Chunk27
@[expose] public section
namespace SparseMonotiles.Contact.Acceptance214Pilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_facets_checked (i : Fin 896) : FacetChecked i := by
  have hall : ∀ b : Fin 28, ∀ j : Fin 32, FacetChecked (chunkIndex b j) := by
    intro b
    fin_cases b
    · exact chunk00
    · exact chunk01
    · exact chunk02
    · exact chunk03
    · exact chunk04
    · exact chunk05
    · exact chunk06
    · exact chunk07
    · exact chunk08
    · exact chunk09
    · exact chunk10
    · exact chunk11
    · exact chunk12
    · exact chunk13
    · exact chunk14
    · exact chunk15
    · exact chunk16
    · exact chunk17
    · exact chunk18
    · exact chunk19
    · exact chunk20
    · exact chunk21
    · exact chunk22
    · exact chunk23
    · exact chunk24
    · exact chunk25
    · exact chunk26
    · exact chunk27
  let b : Fin 28 := ⟨i.val / 32, by omega⟩
  let j : Fin 32 := ⟨i.val % 32, by omega⟩
  have hi : chunkIndex b j = i := by
    apply Fin.ext
    simp only [chunkIndex, b, j]
    omega
  simpa only [hi] using hall b j

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

/-- A literal original-catalog entry is now certified legal on all896 indexed facets. -/
theorem original_entry214_legal :
    geometry.LegalContact (Catalog7.supplied.get ⟨214, by decide⟩) := by
  rw [← pose_eq_original_entry214]
  exact legal_contact

theorem originalM7_has_checked_legal_pose :
    ∃ p ∈ M7, ∃ cert : MateCertificate 896,
      geometry.FastAcceptanceValid p cert ∧ geometry.LegalContact p :=
  ⟨pose, pose_mem_originalM7, certificate, fast_acceptance, legal_contact⟩

#print axioms all_facets_checked
#print axioms disjoint_checked
#print axioms fast_acceptance
#print axioms acceptance
#print axioms legal_contact
#print axioms occupied_key_mate
#print axioms shared_box_profiles
#print axioms original_entry214_legal
#print axioms originalM7_has_checked_legal_pose
end SparseMonotiles.Contact.Acceptance214Pilot7
