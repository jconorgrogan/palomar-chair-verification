module
public import ReplayAllRoots
public import T7DirectMatchedPhysicalAssembly
@[expose] public section
namespace SparseMonotiles.FullContactReplay
open Contact CarrierHierarchy

/-- Unconditional classification of every legal exact indexed T7 contact. -/
theorem all_legal_contact_mem_M7 {p : Pose 7} (legal : IndexedData7.geometry.LegalContact p) : p ∈ M7 :=
  T7DirectMatchedPhysicalAssembly.contact_mem_M7_of_all_match_pairs AllRoots.classified legal

/-- Physical aperiodicity from complete contact classification. This theorem
is not a tiling-existence claim. -/
theorem T7_isAperiodic : IsAperiodic T7 :=
  T7_isAperiodic_of_indexed_contact_classification (fun _ h => all_legal_contact_mem_M7 h)
#print axioms all_legal_contact_mem_M7
#print axioms T7_isAperiodic
end SparseMonotiles.FullContactReplay
