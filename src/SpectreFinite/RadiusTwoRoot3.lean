module

public import SpectreFinite.RadiusTwoRoot3Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root3Node6_cover : Covers root3Node6Domains0 constraints root3Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root3Outputs root3Node6Domains0 (.output 3)
    root3Node6Leaf_checked f hf
theorem root3Node5_cover : Covers root3Node5Domains0 constraints root3Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root3Outputs root3Node5Domains0 (.output 2)
    root3Node5Leaf_checked f hf
theorem root3Node4_cover : Covers root3Node4Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root3Node4Domains0 root3Node4Domains1 f hf root3Node4Step1_checked
  have hb : Covers root3Node4Domains1 constraints root3Outputs := by
    apply covers_of_branches root3Node4Domains1 root3Outputs 7
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node5_cover
    · exact root3Node6_cover
  exact hb f h1
theorem root3Node3_cover : Covers root3Node3Domains0 constraints root3Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root3Outputs root3Node3Domains0 (.output 1)
    root3Node3Leaf_checked f hf
theorem root3Node2_cover : Covers root3Node2Domains0 constraints root3Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root3Outputs root3Node2Domains0 (.output 0)
    root3Node2Leaf_checked f hf
theorem root3Node1_cover : Covers root3Node1Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root3Node1Domains0 root3Node1Domains1 f hf root3Node1Step1_checked
  have hb : Covers root3Node1Domains1 constraints root3Outputs := by
    apply covers_of_branches root3Node1Domains1 root3Outputs 7
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node2_cover
    · exact root3Node3_cover
  exact hb f h1
theorem root3Node0_cover : Covers root3Node0Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root3Node0Domains0 root3Node0Domains1 f hf root3Node0Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root3Node0Domains1 root3Node0Domains2 f h1 root3Node0Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root3Node0Domains2 root3Node0Domains3 f h2 root3Node0Step3_checked
  have h4 := solution_checkReplacement constraints table15 table15_member
    root3Node0Domains3 root3Node0Domains4 f h3 root3Node0Step4_checked
  have h5 := solution_checkReplacement constraints table1 table1_member
    root3Node0Domains4 root3Node0Domains5 f h4 root3Node0Step5_checked
  have h6 := solution_checkReplacement constraints table6 table6_member
    root3Node0Domains5 root3Node0Domains6 f h5 root3Node0Step6_checked
  have hb : Covers root3Node0Domains6 constraints root3Outputs := by
    apply covers_of_branches root3Node0Domains6 root3Outputs 6
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node1_cover
    · exact root3Node4_cover
  exact hb f h6
theorem root3_table_cover : Covers (domains (3,0)) constraints root3Outputs :=
  root3Node0_cover

theorem root3Family_count : root3Family.length = 4 := rfl

theorem extract_mem_root3Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (3,0)) :
    extract f center (hexRegion 2) ∈ root3Family := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (3,0) (hexRegion 2) root3Outputs
    root3_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root3Family] using h
#print axioms extract_mem_root3Family
end SpectreFinite.HexSearch.RadiusTwo
