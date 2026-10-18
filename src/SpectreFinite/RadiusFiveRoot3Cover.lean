module

public import SpectreFinite.RadiusFiveRoot3Part5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root3Node12_cover : Covers root3Node12Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root3Node12Domains0 root3Node12Domains1 f hf root3Node12Step1_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node12Domains1 (.output 6)
    root3Node12Leaf_checked f h1
theorem root3Node11_cover : Covers root3Node11Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root3Node11Domains0 root3Node11Domains1 f hf root3Node11Step1_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node11Domains1 (.output 5)
    root3Node11Leaf_checked f h1
theorem root3Node10_cover : Covers root3Node10Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root3Node10Domains0 root3Node10Domains1 f hf root3Node10Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root3Node10Domains1 root3Node10Domains2 f h1 root3Node10Step2_checked
  have hb : Covers root3Node10Domains2 constraints root3Outputs := by
    apply covers_of_branches root3Node10Domains2 root3Outputs 78
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node11_cover
    · exact root3Node12_cover
  exact hb f h2
theorem root3Node9_cover : Covers root3Node9Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root3Node9Domains0 root3Node9Domains1 f hf root3Node9Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root3Node9Domains1 root3Node9Domains2 f h1 root3Node9Step2_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node9Domains2 (.output 4)
    root3Node9Leaf_checked f h2
theorem root3Node8_cover : Covers root3Node8Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root3Node8Domains0 root3Node8Domains1 f hf root3Node8Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root3Node8Domains1 root3Node8Domains2 f h1 root3Node8Step2_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node8Domains2 (.output 3)
    root3Node8Leaf_checked f h2
theorem root3Node7_cover : Covers root3Node7Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root3Node7Domains0 root3Node7Domains1 f hf root3Node7Step1_checked
  have hb : Covers root3Node7Domains1 constraints root3Outputs := by
    apply covers_of_branches root3Node7Domains1 root3Outputs 40
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node8_cover
    · exact root3Node9_cover
  exact hb f h1
theorem root3Node6_cover : Covers root3Node6Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root3Node6Domains0 root3Node6Domains1 f hf root3Node6Step1_checked
  have hb : Covers root3Node6Domains1 constraints root3Outputs := by
    apply covers_of_branches root3Node6Domains1 root3Outputs 13
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node7_cover
    · exact root3Node10_cover
  exact hb f h1
theorem root3Node5_cover : Covers root3Node5Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root3Node5Domains0 root3Node5Domains1 f hf root3Node5Step1_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node5Domains1 (.output 2)
    root3Node5Leaf_checked f h1
theorem root3Node4_cover : Covers root3Node4Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root3Node4Domains0 root3Node4Domains1 f hf root3Node4Step1_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node4Domains1 (.output 1)
    root3Node4Leaf_checked f h1
theorem root3Node3_cover : Covers root3Node3Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table9 table9_member
    root3Node3Domains0 root3Node3Domains1 f hf root3Node3Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root3Node3Domains1 root3Node3Domains2 f h1 root3Node3Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root3Node3Domains2 root3Node3Domains3 f h2 root3Node3Step3_checked
  have hb : Covers root3Node3Domains3 constraints root3Outputs := by
    apply covers_of_branches root3Node3Domains3 root3Outputs 78
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node4_cover
    · exact root3Node5_cover
  exact hb f h3
theorem root3Node2_cover : Covers root3Node2Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root3Node2Domains0 root3Node2Domains1 f hf root3Node2Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root3Node2Domains1 root3Node2Domains2 f h1 root3Node2Step2_checked
  have hb : Covers root3Node2Domains2 constraints root3Outputs := by
    apply covers_of_branches root3Node2Domains2 root3Outputs 5
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node3_cover
    · exact root3Node6_cover
  exact hb f h2
theorem root3Node1_cover : Covers root3Node1Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root3Node1Domains0 root3Node1Domains1 f hf root3Node1Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root3Node1Domains1 root3Node1Domains2 f h1 root3Node1Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root3Node1Domains2 root3Node1Domains3 f h2 root3Node1Step3_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node1Domains3 (.output 0)
    root3Node1Leaf_checked f h3
theorem root3Node0_cover : Covers root3Node0Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root3Node0Domains0 root3Node0Domains1 f hf root3Node0Step1_checked
  have h2 := solution_checkReplacement constraints table33 table33_member
    root3Node0Domains1 root3Node0Domains2 f h1 root3Node0Step2_checked
  have h3 := solution_checkReplacement constraints table65 table65_member
    root3Node0Domains2 root3Node0Domains3 f h2 root3Node0Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root3Node0Domains3 root3Node0Domains4 f h3 root3Node0Step4_checked
  have hb : Covers root3Node0Domains4 constraints root3Outputs := by
    apply covers_of_branches root3Node0Domains4 root3Outputs 0
    intro s hs
    change s ∈ [(2,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node1_cover
    · exact root3Node2_cover
  exact hb f h4
theorem root3_table_cover : Covers (domains (3,0)) constraints root3Outputs := root3Node0_cover
theorem root3Family_count : root3Family.length = 7 := rfl
#print axioms root3_table_cover
end SpectreFinite.HexSearch.RadiusFive
