module

public import SpectreFinite.RadiusFiveRoot2Part6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root2Node10_cover : Covers root2Node10Domains0 constraints root2Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root2Outputs root2Node10Domains0 (.output 5)
    root2Node10Leaf_checked f hf
theorem root2Node9_cover : Covers root2Node9Domains0 constraints root2Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root2Outputs root2Node9Domains0 (.output 4)
    root2Node9Leaf_checked f hf
theorem root2Node8_cover : Covers root2Node8Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root2Node8Domains0 root2Node8Domains1 f hf root2Node8Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root2Node8Domains1 root2Node8Domains2 f h1 root2Node8Step2_checked
  have h3 := solution_checkReplacement constraints table55 table55_member
    root2Node8Domains2 root2Node8Domains3 f h2 root2Node8Step3_checked
  have hb : Covers root2Node8Domains3 constraints root2Outputs := by
    apply covers_of_branches root2Node8Domains3 root2Outputs 5
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node9_cover
    · exact root2Node10_cover
  exact hb f h3
theorem root2Node7_cover : Covers root2Node7Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root2Node7Domains0 root2Node7Domains1 f hf root2Node7Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root2Node7Domains1 root2Node7Domains2 f h1 root2Node7Step2_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node7Domains2 (.output 3)
    root2Node7Leaf_checked f h2
theorem root2Node6_cover : Covers root2Node6Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root2Node6Domains0 root2Node6Domains1 f hf root2Node6Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root2Node6Domains1 root2Node6Domains2 f h1 root2Node6Step2_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node6Domains2 (.output 2)
    root2Node6Leaf_checked f h2
theorem root2Node5_cover : Covers root2Node5Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root2Node5Domains0 root2Node5Domains1 f hf root2Node5Step1_checked
  have hb : Covers root2Node5Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node5Domains1 root2Outputs 39
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node6_cover
    · exact root2Node7_cover
  exact hb f h1
theorem root2Node4_cover : Covers root2Node4Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root2Node4Domains0 root2Node4Domains1 f hf root2Node4Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root2Node4Domains1 root2Node4Domains2 f h1 root2Node4Step2_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node4Domains2 (.output 1)
    root2Node4Leaf_checked f h2
theorem root2Node3_cover : Covers root2Node3Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table41 table41_member
    root2Node3Domains0 root2Node3Domains1 f hf root2Node3Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root2Node3Domains1 root2Node3Domains2 f h1 root2Node3Step2_checked
  have hb : Covers root2Node3Domains2 constraints root2Outputs := by
    apply covers_of_branches root2Node3Domains2 root2Outputs 12
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node4_cover
    · exact root2Node5_cover
  exact hb f h2
theorem root2Node2_cover : Covers root2Node2Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table41 table41_member
    root2Node2Domains0 root2Node2Domains1 f hf root2Node2Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root2Node2Domains1 root2Node2Domains2 f h1 root2Node2Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root2Node2Domains2 root2Node2Domains3 f h2 root2Node2Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root2Node2Domains3 root2Node2Domains4 f h3 root2Node2Step4_checked
  have h5 := solution_checkReplacement constraints table5 table5_member
    root2Node2Domains4 root2Node2Domains5 f h4 root2Node2Step5_checked
  have h6 := solution_checkReplacement constraints table51 table51_member
    root2Node2Domains5 root2Node2Domains6 f h5 root2Node2Step6_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node2Domains6 (.output 0)
    root2Node2Leaf_checked f h6
theorem root2Node1_cover : Covers root2Node1Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root2Node1Domains0 root2Node1Domains1 f hf root2Node1Step1_checked
  have hb : Covers root2Node1Domains1 constraints root2Outputs := by
    apply covers_of_branches root2Node1Domains1 root2Outputs 6
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node2_cover
    · exact root2Node3_cover
  exact hb f h1
theorem root2Node0_cover : Covers root2Node0Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table45 table45_member
    root2Node0Domains0 root2Node0Domains1 f hf root2Node0Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root2Node0Domains1 root2Node0Domains2 f h1 root2Node0Step2_checked
  have h3 := solution_checkReplacement constraints table36 table36_member
    root2Node0Domains2 root2Node0Domains3 f h2 root2Node0Step3_checked
  have h4 := solution_checkReplacement constraints table56 table56_member
    root2Node0Domains3 root2Node0Domains4 f h3 root2Node0Step4_checked
  have h5 := solution_checkReplacement constraints table0 table0_member
    root2Node0Domains4 root2Node0Domains5 f h4 root2Node0Step5_checked
  have hb : Covers root2Node0Domains5 constraints root2Outputs := by
    apply covers_of_branches root2Node0Domains5 root2Outputs 0
    intro s hs
    change s ∈ [(5,1),(5,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root2Node1_cover
    · exact root2Node8_cover
  exact hb f h5
theorem root2_table_cover : Covers (domains (2,0)) constraints root2Outputs := root2Node0_cover
theorem root2Family_count : root2Family.length = 6 := rfl
#print axioms root2_table_cover
end SpectreFinite.HexSearch.RadiusFive
