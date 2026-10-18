module

public import SpectreFinite.RadiusFourRoot2Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root2Node14_cover : Covers root2Node14Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node14Domains0 root2Node14Domains1 f hf root2Node14Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node14Domains1 (.output 7)
    root2Node14Leaf_checked f h1
theorem root2Node13_cover : Covers root2Node13Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node13Domains0 root2Node13Domains1 f hf root2Node13Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node13Domains1 (.output 6)
    root2Node13Leaf_checked f h1
theorem root2Node12_cover : Covers root2Node12Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root2Node12Domains0 root2Node12Domains1 f hf root2Node12Step1_checked
  have hb : Covers root2Node12Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node12Domains1 root2Outputs 50
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node13_cover
    · exact root2Node14_cover
  exact hb f h1
theorem root2Node11_cover : Covers root2Node11Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node11Domains0 root2Node11Domains1 f hf root2Node11Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node11Domains1 (.output 5)
    root2Node11Leaf_checked f h1
theorem root2Node10_cover : Covers root2Node10Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node10Domains0 root2Node10Domains1 f hf root2Node10Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node10Domains1 (.output 4)
    root2Node10Leaf_checked f h1
theorem root2Node9_cover : Covers root2Node9Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root2Node9Domains0 root2Node9Domains1 f hf root2Node9Step1_checked
  have hb : Covers root2Node9Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node9Domains1 root2Outputs 50
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node10_cover
    · exact root2Node11_cover
  exact hb f h1
theorem root2Node8_cover : Covers root2Node8Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root2Node8Domains0 root2Node8Domains1 f hf root2Node8Step1_checked
  have hb : Covers root2Node8Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node8Domains1 root2Outputs 34
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node9_cover
    · exact root2Node12_cover
  exact hb f h1
theorem root2Node7_cover : Covers root2Node7Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node7Domains0 root2Node7Domains1 f hf root2Node7Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node7Domains1 (.output 3)
    root2Node7Leaf_checked f h1
theorem root2Node6_cover : Covers root2Node6Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node6Domains0 root2Node6Domains1 f hf root2Node6Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node6Domains1 (.output 2)
    root2Node6Leaf_checked f h1
theorem root2Node5_cover : Covers root2Node5Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root2Node5Domains0 root2Node5Domains1 f hf root2Node5Step1_checked
  have hb : Covers root2Node5Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node5Domains1 root2Outputs 50
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node6_cover
    · exact root2Node7_cover
  exact hb f h1
theorem root2Node4_cover : Covers root2Node4Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node4Domains0 root2Node4Domains1 f hf root2Node4Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node4Domains1 (.output 1)
    root2Node4Leaf_checked f h1
theorem root2Node3_cover : Covers root2Node3Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root2Node3Domains0 root2Node3Domains1 f hf root2Node3Step1_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node3Domains1 (.output 0)
    root2Node3Leaf_checked f h1
theorem root2Node2_cover : Covers root2Node2Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root2Node2Domains0 root2Node2Domains1 f hf root2Node2Step1_checked
  have hb : Covers root2Node2Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node2Domains1 root2Outputs 50
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node3_cover
    · exact root2Node4_cover
  exact hb f h1
theorem root2Node1_cover : Covers root2Node1Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root2Node1Domains0 root2Node1Domains1 f hf root2Node1Step1_checked
  have hb : Covers root2Node1Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node1Domains1 root2Outputs 34
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node2_cover
    · exact root2Node5_cover
  exact hb f h1
theorem root2Node0_cover : Covers root2Node0Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root2Node0Domains0 root2Node0Domains1 f hf root2Node0Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root2Node0Domains1 root2Node0Domains2 f h1 root2Node0Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root2Node0Domains2 root2Node0Domains3 f h2 root2Node0Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root2Node0Domains3 root2Node0Domains4 f h3 root2Node0Step4_checked
  have h5 := solution_checkReplacement constraints table16 table16_member
    root2Node0Domains4 root2Node0Domains5 f h4 root2Node0Step5_checked
  have hb : Covers root2Node0Domains5 constraints root2Outputs := by
    apply covers_of_branches root2Node0Domains5 root2Outputs 0
    intro s hs
    change s ∈ [(7,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node1_cover
    · exact root2Node8_cover
  exact hb f h5
theorem root2_table_cover : Covers (domains (2,0)) constraints root2Outputs := root2Node0_cover
theorem root2Family_count : root2Family.length = 8 := rfl
#print axioms root2_table_cover
end SpectreFinite.HexSearch.RadiusFour
