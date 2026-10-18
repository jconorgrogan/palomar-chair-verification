module

public import SpectreFinite.RadiusThreeRoot3Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root3Node2_cover : Covers root3Node2Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root3Node2Domains0 root3Node2Domains1 f hf root3Node2Step1_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node2Domains1 (.output 1)
    root3Node2Leaf_checked f h1
theorem root3Node1_cover : Covers root3Node1Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root3Node1Domains0 root3Node1Domains1 f hf root3Node1Step1_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node1Domains1 (.output 0)
    root3Node1Leaf_checked f h1
theorem root3Node0_cover : Covers root3Node0Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root3Node0Domains0 root3Node0Domains1 f hf root3Node0Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root3Node0Domains1 root3Node0Domains2 f h1 root3Node0Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root3Node0Domains2 root3Node0Domains3 f h2 root3Node0Step3_checked
  have h4 := solution_checkReplacement constraints table4 table4_member
    root3Node0Domains3 root3Node0Domains4 f h3 root3Node0Step4_checked
  have hb : Covers root3Node0Domains4 constraints root3Outputs := by
    apply covers_of_branches root3Node0Domains4 root3Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node1_cover
    · exact root3Node2_cover
  exact hb f h4
theorem root3_table_cover : Covers (domains (3,0)) constraints root3Outputs := root3Node0_cover
theorem root3Family_count : root3Family.length = 2 := rfl
#print axioms root3_table_cover
end SpectreFinite.HexSearch.RadiusThree
