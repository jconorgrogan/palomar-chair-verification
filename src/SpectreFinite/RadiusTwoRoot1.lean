module

public import SpectreFinite.RadiusTwoRoot1Part8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root1Node39_cover : Covers root1Node39Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node39Domains0 root1Node39Domains1 f hf root1Node39Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node39Domains1 root1Node39Domains2 f h1 root1Node39Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node39Domains2 (.output 20)
    root1Node39Leaf_checked f h2
theorem root1Node38_cover : Covers root1Node38Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node38Domains0 root1Node38Domains1 f hf root1Node38Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node38Domains1 root1Node38Domains2 f h1 root1Node38Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node38Domains2 (.output 19)
    root1Node38Leaf_checked f h2
theorem root1Node37_cover : Covers root1Node37Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node37Domains0 root1Node37Domains1 f hf root1Node37Step1_checked
  have hb : Covers root1Node37Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node37Domains1 root1Outputs 12
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node38_cover
    · exact root1Node39_cover
  exact hb f h1
theorem root1Node36_cover : Covers root1Node36Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node36Domains0 root1Node36Domains1 f hf root1Node36Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root1Node36Domains1 root1Node36Domains2 f h1 root1Node36Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node36Domains2 (.output 18)
    root1Node36Leaf_checked f h2
theorem root1Node35_cover : Covers root1Node35Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node35Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node35Domains0 root1Outputs 11
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node36_cover
    · exact root1Node37_cover
  exact hb f hf
theorem root1Node34_cover : Covers root1Node34Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node34Domains0 root1Node34Domains1 f hf root1Node34Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node34Domains1 root1Node34Domains2 f h1 root1Node34Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node34Domains2 (.output 17)
    root1Node34Leaf_checked f h2
theorem root1Node33_cover : Covers root1Node33Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node33Domains0 root1Node33Domains1 f hf root1Node33Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node33Domains1 root1Node33Domains2 f h1 root1Node33Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node33Domains2 (.output 16)
    root1Node33Leaf_checked f h2
theorem root1Node32_cover : Covers root1Node32Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node32Domains0 root1Node32Domains1 f hf root1Node32Step1_checked
  have hb : Covers root1Node32Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node32Domains1 root1Outputs 12
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node33_cover
    · exact root1Node34_cover
  exact hb f h1
theorem root1Node31_cover : Covers root1Node31Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node31Domains0 root1Node31Domains1 f hf root1Node31Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root1Node31Domains1 root1Node31Domains2 f h1 root1Node31Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node31Domains2 (.output 15)
    root1Node31Leaf_checked f h2
theorem root1Node30_cover : Covers root1Node30Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node30Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node30Domains0 root1Outputs 11
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node31_cover
    · exact root1Node32_cover
  exact hb f hf
theorem root1Node29_cover : Covers root1Node29Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node29Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node29Domains0 root1Outputs 7
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node30_cover
    · exact root1Node35_cover
  exact hb f hf
theorem root1Node28_cover : Covers root1Node28Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node28Domains0 root1Node28Domains1 f hf root1Node28Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node28Domains1 root1Node28Domains2 f h1 root1Node28Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node28Domains2 (.output 14)
    root1Node28Leaf_checked f h2
theorem root1Node27_cover : Covers root1Node27Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node27Domains0 root1Node27Domains1 f hf root1Node27Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node27Domains1 root1Node27Domains2 f h1 root1Node27Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node27Domains2 (.output 13)
    root1Node27Leaf_checked f h2
theorem root1Node26_cover : Covers root1Node26Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node26Domains0 root1Node26Domains1 f hf root1Node26Step1_checked
  have hb : Covers root1Node26Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node26Domains1 root1Outputs 12
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node27_cover
    · exact root1Node28_cover
  exact hb f h1
theorem root1Node25_cover : Covers root1Node25Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node25Domains0 root1Node25Domains1 f hf root1Node25Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root1Node25Domains1 root1Node25Domains2 f h1 root1Node25Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node25Domains2 (.output 12)
    root1Node25Leaf_checked f h2
theorem root1Node24_cover : Covers root1Node24Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node24Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node24Domains0 root1Outputs 11
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node25_cover
    · exact root1Node26_cover
  exact hb f hf
theorem root1Node23_cover : Covers root1Node23Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node23Domains0 root1Node23Domains1 f hf root1Node23Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node23Domains1 root1Node23Domains2 f h1 root1Node23Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node23Domains2 (.output 11)
    root1Node23Leaf_checked f h2
theorem root1Node22_cover : Covers root1Node22Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node22Domains0 root1Node22Domains1 f hf root1Node22Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node22Domains1 root1Node22Domains2 f h1 root1Node22Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node22Domains2 (.output 10)
    root1Node22Leaf_checked f h2
theorem root1Node21_cover : Covers root1Node21Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node21Domains0 root1Node21Domains1 f hf root1Node21Step1_checked
  have hb : Covers root1Node21Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node21Domains1 root1Outputs 12
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node22_cover
    · exact root1Node23_cover
  exact hb f h1
theorem root1Node20_cover : Covers root1Node20Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root1Node20Domains0 root1Node20Domains1 f hf root1Node20Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root1Node20Domains1 root1Node20Domains2 f h1 root1Node20Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node20Domains2 (.output 9)
    root1Node20Leaf_checked f h2
theorem root1Node19_cover : Covers root1Node19Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node19Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node19Domains0 root1Outputs 11
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node20_cover
    · exact root1Node21_cover
  exact hb f hf
theorem root1Node18_cover : Covers root1Node18Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node18Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node18Domains0 root1Outputs 7
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node19_cover
    · exact root1Node24_cover
  exact hb f hf
theorem root1Node17_cover : Covers root1Node17Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root1Node17Domains0 root1Node17Domains1 f hf root1Node17Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root1Node17Domains1 root1Node17Domains2 f h1 root1Node17Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root1Node17Domains2 root1Node17Domains3 f h2 root1Node17Step3_checked
  have h4 := solution_checkReplacement constraints table14 table14_member
    root1Node17Domains3 root1Node17Domains4 f h3 root1Node17Step4_checked
  have hb : Covers root1Node17Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node17Domains4 root1Outputs 2
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node18_cover
    · exact root1Node29_cover
  exact hb f h4
theorem root1Node16_cover : Covers root1Node16Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node16Domains0 root1Node16Domains1 f hf root1Node16Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root1Node16Domains1 root1Node16Domains2 f h1 root1Node16Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node16Domains2 (.output 8)
    root1Node16Leaf_checked f h2
theorem root1Node15_cover : Covers root1Node15Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node15Domains0 root1Node15Domains1 f hf root1Node15Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root1Node15Domains1 root1Node15Domains2 f h1 root1Node15Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node15Domains2 (.output 7)
    root1Node15Leaf_checked f h2
theorem root1Node14_cover : Covers root1Node14Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node14Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node14Domains0 root1Outputs 8
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node15_cover
    · exact root1Node16_cover
  exact hb f hf
theorem root1Node13_cover : Covers root1Node13Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node13Domains0 root1Node13Domains1 f hf root1Node13Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root1Node13Domains1 root1Node13Domains2 f h1 root1Node13Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node13Domains2 (.output 6)
    root1Node13Leaf_checked f h2
theorem root1Node12_cover : Covers root1Node12Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node12Domains0 root1Node12Domains1 f hf root1Node12Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root1Node12Domains1 root1Node12Domains2 f h1 root1Node12Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node12Domains2 (.output 5)
    root1Node12Leaf_checked f h2
theorem root1Node11_cover : Covers root1Node11Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node11Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node11Domains0 root1Outputs 8
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node12_cover
    · exact root1Node13_cover
  exact hb f hf
theorem root1Node10_cover : Covers root1Node10Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root1Node10Domains0 root1Node10Domains1 f hf root1Node10Step1_checked
  have h2 := solution_checkReplacement constraints table17 table17_member
    root1Node10Domains1 root1Node10Domains2 f h1 root1Node10Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root1Node10Domains2 root1Node10Domains3 f h2 root1Node10Step3_checked
  have h4 := solution_checkReplacement constraints table8 table8_member
    root1Node10Domains3 root1Node10Domains4 f h3 root1Node10Step4_checked
  have hb : Covers root1Node10Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node10Domains4 root1Outputs 7
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node11_cover
    · exact root1Node14_cover
  exact hb f h4
theorem root1Node9_cover : Covers root1Node9Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root1Node9Domains0 root1Node9Domains1 f hf root1Node9Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root1Node9Domains1 root1Node9Domains2 f h1 root1Node9Step2_checked
  have hb : Covers root1Node9Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node9Domains2 root1Outputs 6
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node10_cover
    · exact root1Node17_cover
  exact hb f h2
theorem root1Node8_cover : Covers root1Node8Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node8Domains0 (.output 4)
    root1Node8Leaf_checked f hf
theorem root1Node7_cover : Covers root1Node7Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node7Domains0 (.output 3)
    root1Node7Leaf_checked f hf
theorem root1Node6_cover : Covers root1Node6Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root1Node6Domains0 root1Node6Domains1 f hf root1Node6Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node6Domains1 root1Node6Domains2 f h1 root1Node6Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root1Node6Domains2 root1Node6Domains3 f h2 root1Node6Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root1Node6Domains3 root1Node6Domains4 f h3 root1Node6Step4_checked
  have h5 := solution_checkReplacement constraints table2 table2_member
    root1Node6Domains4 root1Node6Domains5 f h4 root1Node6Step5_checked
  have hb : Covers root1Node6Domains5 constraints root1Outputs := by
    apply covers_of_branches root1Node6Domains5 root1Outputs 2
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node7_cover
    · exact root1Node8_cover
  exact hb f h5
theorem root1Node5_cover : Covers root1Node5Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root1Node5Domains0 root1Node5Domains1 f hf root1Node5Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root1Node5Domains1 root1Node5Domains2 f h1 root1Node5Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root1Node5Domains2 root1Node5Domains3 f h2 root1Node5Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root1Node5Domains3 root1Node5Domains4 f h3 root1Node5Step4_checked
  have hb : Covers root1Node5Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node5Domains4 root1Outputs 3
    intro s hs
    change s ∈ [(3,1),(5,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node6_cover
    · exact root1Node9_cover
  exact hb f h4
theorem root1Node4_cover : Covers root1Node4Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root1Node4Domains0 root1Node4Domains1 f hf root1Node4Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node4Domains1 (.output 2)
    root1Node4Leaf_checked f h1
theorem root1Node3_cover : Covers root1Node3Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root1Node3Domains0 root1Node3Domains1 f hf root1Node3Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node3Domains1 (.output 1)
    root1Node3Leaf_checked f h1
theorem root1Node2_cover : Covers root1Node2Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root1Node2Domains0 root1Node2Domains1 f hf root1Node2Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root1Node2Domains1 root1Node2Domains2 f h1 root1Node2Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root1Node2Domains2 root1Node2Domains3 f h2 root1Node2Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root1Node2Domains3 root1Node2Domains4 f h3 root1Node2Step4_checked
  have h5 := solution_checkReplacement constraints table2 table2_member
    root1Node2Domains4 root1Node2Domains5 f h4 root1Node2Step5_checked
  have hb : Covers root1Node2Domains5 constraints root1Outputs := by
    apply covers_of_branches root1Node2Domains5 root1Outputs 3
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node3_cover
    · exact root1Node4_cover
  exact hb f h5
theorem root1Node1_cover : Covers root1Node1Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root1Node1Domains0 root1Node1Domains1 f hf root1Node1Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root1Node1Domains1 root1Node1Domains2 f h1 root1Node1Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root1Node1Domains2 root1Node1Domains3 f h2 root1Node1Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root1Node1Domains3 root1Node1Domains4 f h3 root1Node1Step4_checked
  have h5 := solution_checkReplacement constraints table1 table1_member
    root1Node1Domains4 root1Node1Domains5 f h4 root1Node1Step5_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node1Domains5 (.output 0)
    root1Node1Leaf_checked f h5
theorem root1Node0_cover : Covers root1Node0Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root1Node0Domains0 root1Node0Domains1 f hf root1Node0Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root1Node0Domains1 root1Node0Domains2 f h1 root1Node0Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root1Node0Domains2 root1Node0Domains3 f h2 root1Node0Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root1Node0Domains3 root1Node0Domains4 f h3 root1Node0Step4_checked
  have hb : Covers root1Node0Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node0Domains4 root1Outputs 0
    intro s hs
    change s ∈ [(2,0),(2,2),(4,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact root1Node1_cover
    · exact root1Node2_cover
    · exact root1Node5_cover
  exact hb f h4
theorem root1_table_cover : Covers (domains (1,0)) constraints root1Outputs :=
  root1Node0_cover

theorem root1Family_count : root1Family.length = 21 := rfl

theorem extract_mem_root1Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (1,0)) :
    extract f center (hexRegion 2) ∈ root1Family := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (1,0) (hexRegion 2) root1Outputs
    root1_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root1Family] using h
#print axioms extract_mem_root1Family
end SpectreFinite.HexSearch.RadiusTwo
