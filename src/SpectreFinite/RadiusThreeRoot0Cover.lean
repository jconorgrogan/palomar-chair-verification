module

public import SpectreFinite.RadiusThreeRoot0Part22

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root0Node42_cover : Covers root0Node42Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node42Domains0 (.output 21)
    root0Node42Leaf_checked f hf
theorem root0Node41_cover : Covers root0Node41Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node41Domains0 (.output 20)
    root0Node41Leaf_checked f hf
theorem root0Node40_cover : Covers root0Node40Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node40Domains0 root0Node40Domains1 f hf root0Node40Step1_checked
  have hb : Covers root0Node40Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node40Domains1 root0Outputs 36
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node41_cover
    · exact root0Node42_cover
  exact hb f h1
theorem root0Node39_cover : Covers root0Node39Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node39Domains0 root0Node39Domains1 f hf root0Node39Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node39Domains1 (.output 19)
    root0Node39Leaf_checked f h1
theorem root0Node38_cover : Covers root0Node38Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root0Node38Domains0 root0Node38Domains1 f hf root0Node38Step1_checked
  have hb : Covers root0Node38Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node38Domains1 root0Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node39_cover
    · exact root0Node40_cover
  exact hb f h1
theorem root0Node37_cover : Covers root0Node37Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node37Domains0 root0Node37Domains1 f hf root0Node37Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root0Node37Domains1 root0Node37Domains2 f h1 root0Node37Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node37Domains2 (.output 18)
    root0Node37Leaf_checked f h2
theorem root0Node36_cover : Covers root0Node36Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node36Domains0 root0Node36Domains1 f hf root0Node36Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root0Node36Domains1 root0Node36Domains2 f h1 root0Node36Step2_checked
  have hb : Covers root0Node36Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node36Domains2 root0Outputs 15
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node37_cover
    · exact root0Node38_cover
  exact hb f h2
theorem root0Node35_cover : Covers root0Node35Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node35Domains0 root0Node35Domains1 f hf root0Node35Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node35Domains1 (.output 17)
    root0Node35Leaf_checked f h1
theorem root0Node34_cover : Covers root0Node34Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node34Domains0 root0Node34Domains1 f hf root0Node34Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node34Domains1 (.output 16)
    root0Node34Leaf_checked f h1
theorem root0Node33_cover : Covers root0Node33Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root0Node33Domains0 root0Node33Domains1 f hf root0Node33Step1_checked
  have hb : Covers root0Node33Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node33Domains1 root0Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node34_cover
    · exact root0Node35_cover
  exact hb f h1
theorem root0Node32_cover : Covers root0Node32Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node32Domains0 root0Node32Domains1 f hf root0Node32Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root0Node32Domains1 root0Node32Domains2 f h1 root0Node32Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node32Domains2 (.output 15)
    root0Node32Leaf_checked f h2
theorem root0Node31_cover : Covers root0Node31Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root0Node31Domains0 root0Node31Domains1 f hf root0Node31Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root0Node31Domains1 root0Node31Domains2 f h1 root0Node31Step2_checked
  have hb : Covers root0Node31Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node31Domains2 root0Outputs 15
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node32_cover
    · exact root0Node33_cover
  exact hb f h2
theorem root0Node30_cover : Covers root0Node30Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root0Node30Domains0 root0Node30Domains1 f hf root0Node30Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root0Node30Domains1 root0Node30Domains2 f h1 root0Node30Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node30Domains2 (.output 14)
    root0Node30Leaf_checked f h2
theorem root0Node29_cover : Covers root0Node29Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node29Domains0 root0Node29Domains1 f hf root0Node29Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node29Domains1 (.output 13)
    root0Node29Leaf_checked f h1
theorem root0Node28_cover : Covers root0Node28Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node28Domains0 root0Node28Domains1 f hf root0Node28Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node28Domains1 (.output 12)
    root0Node28Leaf_checked f h1
theorem root0Node27_cover : Covers root0Node27Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root0Node27Domains0 root0Node27Domains1 f hf root0Node27Step1_checked
  have hb : Covers root0Node27Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node27Domains1 root0Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node28_cover
    · exact root0Node29_cover
  exact hb f h1
theorem root0Node26_cover : Covers root0Node26Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root0Node26Domains0 root0Node26Domains1 f hf root0Node26Step1_checked
  have hb : Covers root0Node26Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node26Domains1 root0Outputs 21
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node27_cover
    · exact root0Node30_cover
  exact hb f h1
theorem root0Node25_cover : Covers root0Node25Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node25Domains0 root0Node25Domains1 f hf root0Node25Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root0Node25Domains1 root0Node25Domains2 f h1 root0Node25Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root0Node25Domains2 root0Node25Domains3 f h2 root0Node25Step3_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node25Domains3 (.output 11)
    root0Node25Leaf_checked f h3
theorem root0Node24_cover : Covers root0Node24Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root0Node24Domains0 root0Node24Domains1 f hf root0Node24Step1_checked
  have hb : Covers root0Node24Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node24Domains1 root0Outputs 15
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node25_cover
    · exact root0Node26_cover
  exact hb f h1
theorem root0Node23_cover : Covers root0Node23Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root0Node23Domains0 root0Node23Domains1 f hf root0Node23Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root0Node23Domains1 root0Node23Domains2 f h1 root0Node23Step2_checked
  have hb : Covers root0Node23Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node23Domains2 root0Outputs 2
    intro s hs
    change s ∈ [(2,4),(4,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node24_cover
    · exact root0Node31_cover
  exact hb f h2
theorem root0Node22_cover : Covers root0Node22Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node22Domains0 (.output 10)
    root0Node22Leaf_checked f hf
theorem root0Node21_cover : Covers root0Node21Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node21Domains0 (.output 9)
    root0Node21Leaf_checked f hf
theorem root0Node20_cover : Covers root0Node20Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node20Domains0 root0Node20Domains1 f hf root0Node20Step1_checked
  have hb : Covers root0Node20Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node20Domains1 root0Outputs 36
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node21_cover
    · exact root0Node22_cover
  exact hb f h1
theorem root0Node19_cover : Covers root0Node19Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root0Node19Domains0 root0Node19Domains1 f hf root0Node19Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node19Domains1 (.output 8)
    root0Node19Leaf_checked f h1
theorem root0Node18_cover : Covers root0Node18Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root0Node18Domains0 root0Node18Domains1 f hf root0Node18Step1_checked
  have hb : Covers root0Node18Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node18Domains1 root0Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node19_cover
    · exact root0Node20_cover
  exact hb f h1
theorem root0Node17_cover : Covers root0Node17Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node17Domains0 root0Node17Domains1 f hf root0Node17Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root0Node17Domains1 root0Node17Domains2 f h1 root0Node17Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node17Domains2 (.output 7)
    root0Node17Leaf_checked f h2
theorem root0Node16_cover : Covers root0Node16Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root0Node16Domains0 root0Node16Domains1 f hf root0Node16Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root0Node16Domains1 root0Node16Domains2 f h1 root0Node16Step2_checked
  have hb : Covers root0Node16Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node16Domains2 root0Outputs 15
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node17_cover
    · exact root0Node18_cover
  exact hb f h2
theorem root0Node15_cover : Covers root0Node15Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root0Node15Domains0 root0Node15Domains1 f hf root0Node15Step1_checked
  have hb : Covers root0Node15Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node15Domains1 root0Outputs 6
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node16_cover
    · exact root0Node23_cover
  exact hb f h1
theorem root0Node14_cover : Covers root0Node14Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root0Node14Domains0 root0Node14Domains1 f hf root0Node14Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root0Node14Domains1 root0Node14Domains2 f h1 root0Node14Step2_checked
  have h3 := solution_checkReplacement constraints table30 table30_member
    root0Node14Domains2 root0Node14Domains3 f h2 root0Node14Step3_checked
  have hb : Covers root0Node14Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node14Domains3 root0Outputs 0
    intro s hs
    change s ∈ [(1,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node15_cover
    · exact root0Node36_cover
  exact hb f h3
theorem root0Node13_cover : Covers root0Node13Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node13Domains0 root0Node13Domains1 f hf root0Node13Step1_checked
  have h2 := solution_checkReplacement constraints table3 table3_member
    root0Node13Domains1 root0Node13Domains2 f h1 root0Node13Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node13Domains2 (.output 6)
    root0Node13Leaf_checked f h2
theorem root0Node12_cover : Covers root0Node12Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root0Node12Domains0 root0Node12Domains1 f hf root0Node12Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node12Domains1 (.output 5)
    root0Node12Leaf_checked f h1
theorem root0Node11_cover : Covers root0Node11Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root0Node11Domains0 root0Node11Domains1 f hf root0Node11Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node11Domains1 (.output 4)
    root0Node11Leaf_checked f h1
theorem root0Node10_cover : Covers root0Node10Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root0Node10Domains0 root0Node10Domains1 f hf root0Node10Step1_checked
  have hb : Covers root0Node10Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node10Domains1 root0Outputs 2
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node11_cover
    · exact root0Node12_cover
  exact hb f h1
theorem root0Node9_cover : Covers root0Node9Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node9Domains0 root0Node9Domains1 f hf root0Node9Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root0Node9Domains1 root0Node9Domains2 f h1 root0Node9Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root0Node9Domains2 root0Node9Domains3 f h2 root0Node9Step3_checked
  have hb : Covers root0Node9Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node9Domains3 root0Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node10_cover
    · exact root0Node13_cover
  exact hb f h3
theorem root0Node8_cover : Covers root0Node8Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node8Domains0 root0Node8Domains1 f hf root0Node8Step1_checked
  have h2 := solution_checkReplacement constraints table9 table9_member
    root0Node8Domains1 root0Node8Domains2 f h1 root0Node8Step2_checked
  have hb : Covers root0Node8Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node8Domains2 root0Outputs 9
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node9_cover
    · exact root0Node14_cover
  exact hb f h2
theorem root0Node7_cover : Covers root0Node7Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node7Domains0 (.output 3)
    root0Node7Leaf_checked f hf
theorem root0Node6_cover : Covers root0Node6Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node6Domains0 (.output 2)
    root0Node6Leaf_checked f hf
theorem root0Node5_cover : Covers root0Node5Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node5Domains0 root0Node5Domains1 f hf root0Node5Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root0Node5Domains1 root0Node5Domains2 f h1 root0Node5Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root0Node5Domains2 root0Node5Domains3 f h2 root0Node5Step3_checked
  have h4 := solution_checkReplacement constraints table4 table4_member
    root0Node5Domains3 root0Node5Domains4 f h3 root0Node5Step4_checked
  have hb : Covers root0Node5Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node5Domains4 root0Outputs 36
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node6_cover
    · exact root0Node7_cover
  exact hb f h4
theorem root0Node4_cover : Covers root0Node4Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node4Domains0 root0Node4Domains1 f hf root0Node4Step1_checked
  have h2 := solution_checkReplacement constraints table3 table3_member
    root0Node4Domains1 root0Node4Domains2 f h1 root0Node4Step2_checked
  have hb : Covers root0Node4Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node4Domains2 root0Outputs 11
    intro s hs
    change s ∈ [(3,0),(5,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node5_cover
    · exact root0Node8_cover
  exact hb f h2
theorem root0Node3_cover : Covers root0Node3Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node3Domains0 (.output 1)
    root0Node3Leaf_checked f hf
theorem root0Node2_cover : Covers root0Node2Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node2Domains0 (.output 0)
    root0Node2Leaf_checked f hf
theorem root0Node1_cover : Covers root0Node1Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node1Domains0 root0Node1Domains1 f hf root0Node1Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root0Node1Domains1 root0Node1Domains2 f h1 root0Node1Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root0Node1Domains2 root0Node1Domains3 f h2 root0Node1Step3_checked
  have h4 := solution_checkReplacement constraints table4 table4_member
    root0Node1Domains3 root0Node1Domains4 f h3 root0Node1Step4_checked
  have hb : Covers root0Node1Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node1Domains4 root0Outputs 36
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node2_cover
    · exact root0Node3_cover
  exact hb f h4
theorem root0Node0_cover : Covers root0Node0Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root0Node0Domains0 root0Node0Domains1 f hf root0Node0Step1_checked
  have h2 := solution_checkReplacement constraints table10 table10_member
    root0Node0Domains1 root0Node0Domains2 f h1 root0Node0Step2_checked
  have h3 := solution_checkReplacement constraints table8 table8_member
    root0Node0Domains2 root0Node0Domains3 f h2 root0Node0Step3_checked
  have h4 := solution_checkReplacement constraints table22 table22_member
    root0Node0Domains3 root0Node0Domains4 f h3 root0Node0Step4_checked
  have hb : Covers root0Node0Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node0Domains4 root0Outputs 19
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node1_cover
    · exact root0Node4_cover
  exact hb f h4
theorem root0_table_cover : Covers (domains (0,0)) constraints root0Outputs := root0Node0_cover
theorem root0Family_count : root0Family.length = 22 := rfl
#print axioms root0_table_cover
end SpectreFinite.HexSearch.RadiusThree
