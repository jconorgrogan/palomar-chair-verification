module

public import SpectreFinite.RadiusTwoThetaSteps

@[expose] public section


/-! The first checked larger-window consequence: every globally legal field
with Theta at turn zero has this one declared radius-two window. Coverage is
one-way and asserts neither global existence nor extendibility. -/
namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem table1_mem : table1 ∈ constraints := by
  rw [table1_eq]
  exact List.mem_map.mpr ⟨(-2, 1), by decide, rfl⟩
theorem table3_mem : table3 ∈ constraints := by
  rw [table3_eq]
  exact List.mem_map.mpr ⟨(-1, -1), by decide, rfl⟩
theorem table5_mem : table5 ∈ constraints := by
  rw [table5_eq]
  exact List.mem_map.mpr ⟨(-1, 1), by decide, rfl⟩
theorem table6_mem : table6 ∈ constraints := by
  rw [table6_eq]
  exact List.mem_map.mpr ⟨(-1, 2), by decide, rfl⟩
theorem table13_mem : table13 ∈ constraints := by
  rw [table13_eq]
  exact List.mem_map.mpr ⟨(1, -1), by decide, rfl⟩
theorem table15_mem : table15 ∈ constraints := by
  rw [table15_eq]
  exact List.mem_map.mpr ⟨(1, 1), by decide, rfl⟩
def thetaOutputs : List (List State) := [[(5,4),(0,0),(7,2),(4,3),(1,5),(6,1),(4,1),(1,4),(0,5),(2,0),(7,3),(5,2),(6,0),(3,1),(0,1),(6,2),(5,0),(4,5),(1,0)]]
def thetaFamily : List Patch := rowsToPatches positions thetaOutputs

theorem thetaOutputs_count : thetaOutputs.length = 1 := rfl
theorem thetaFamily_count : thetaFamily.length = 1 := rfl

theorem thetaLeaf_checked :
    checkCover 1 constraints thetaOutputs thetaDomains6 (.output 0) = true := by decide

theorem theta_table_cover : Covers (domains (2,0)) constraints thetaOutputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_mem
    thetaDomains0 thetaDomains1 f hf thetaStep1_checked
  have h2 := solution_checkReplacement constraints table5 table5_mem
    thetaDomains1 thetaDomains2 f h1 thetaStep2_checked
  have h3 := solution_checkReplacement constraints table3 table3_mem
    thetaDomains2 thetaDomains3 f h2 thetaStep3_checked
  have h4 := solution_checkReplacement constraints table15 table15_mem
    thetaDomains3 thetaDomains4 f h3 thetaStep4_checked
  have h5 := solution_checkReplacement constraints table1 table1_mem
    thetaDomains4 thetaDomains5 f h4 thetaStep5_checked
  have h6 := solution_checkReplacement constraints table6 table6_mem
    thetaDomains5 thetaDomains6 f h5 thetaStep6_checked
  exact checkCover_sound 1 constraints thetaOutputs thetaDomains6 (.output 0)
    thetaLeaf_checked f h6

theorem extract_mem_thetaFamily (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (2,0)) :
    extract f center (hexRegion 2) ∈ thetaFamily := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (2,0) (hexRegion 2) thetaOutputs
    theta_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, thetaFamily] using h

#print axioms theta_table_cover
#print axioms extract_mem_thetaFamily
end SpectreFinite.HexSearch.RadiusTwo
