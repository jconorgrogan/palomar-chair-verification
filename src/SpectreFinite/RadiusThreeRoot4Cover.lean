module

public import SpectreFinite.RadiusThreeRoot4Part24

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root4Node42_cover : Covers root4Node42Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root4Node42Domains0 root4Node42Domains1 f hf root4Node42Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node42Domains1 (.output 21)
    root4Node42Leaf_checked f h1
theorem root4Node41_cover : Covers root4Node41Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node41Domains0 (.output 20)
    root4Node41Leaf_checked f hf
theorem root4Node40_cover : Covers root4Node40Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node40Domains0 (.output 19)
    root4Node40Leaf_checked f hf
theorem root4Node39_cover : Covers root4Node39Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node39Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node39Domains0 root4Outputs 9
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node40_cover
    · exact root4Node41_cover
  exact hb f hf
theorem root4Node38_cover : Covers root4Node38Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table9 table9_member
    root4Node38Domains0 root4Node38Domains1 f hf root4Node38Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root4Node38Domains1 root4Node38Domains2 f h1 root4Node38Step2_checked
  have h3 := solution_checkReplacement constraints table8 table8_member
    root4Node38Domains2 root4Node38Domains3 f h2 root4Node38Step3_checked
  have h4 := solution_checkReplacement constraints table22 table22_member
    root4Node38Domains3 root4Node38Domains4 f h3 root4Node38Step4_checked
  have hb : Covers root4Node38Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node38Domains4 root4Outputs 2
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node39_cover
    · exact root4Node42_cover
  exact hb f h4
theorem root4Node37_cover : Covers root4Node37Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root4Node37Domains0 root4Node37Domains1 f hf root4Node37Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root4Node37Domains1 root4Node37Domains2 f h1 root4Node37Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node37Domains2 (.output 18)
    root4Node37Leaf_checked f h2
theorem root4Node36_cover : Covers root4Node36Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node36Domains0 root4Node36Domains1 f hf root4Node36Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node36Domains1 (.output 17)
    root4Node36Leaf_checked f h1
theorem root4Node35_cover : Covers root4Node35Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node35Domains0 root4Node35Domains1 f hf root4Node35Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node35Domains1 (.output 16)
    root4Node35Leaf_checked f h1
theorem root4Node34_cover : Covers root4Node34Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node34Domains0 root4Node34Domains1 f hf root4Node34Step1_checked
  have hb : Covers root4Node34Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node34Domains1 root4Outputs 34
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node35_cover
    · exact root4Node36_cover
  exact hb f h1
theorem root4Node33_cover : Covers root4Node33Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node33Domains0 root4Node33Domains1 f hf root4Node33Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root4Node33Domains1 root4Node33Domains2 f h1 root4Node33Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node33Domains2 (.output 15)
    root4Node33Leaf_checked f h2
theorem root4Node32_cover : Covers root4Node32Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root4Node32Domains0 root4Node32Domains1 f hf root4Node32Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root4Node32Domains1 root4Node32Domains2 f h1 root4Node32Step2_checked
  have hb : Covers root4Node32Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node32Domains2 root4Outputs 21
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node33_cover
    · exact root4Node34_cover
  exact hb f h2
theorem root4Node31_cover : Covers root4Node31Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table9 table9_member
    root4Node31Domains0 root4Node31Domains1 f hf root4Node31Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root4Node31Domains1 root4Node31Domains2 f h1 root4Node31Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root4Node31Domains2 root4Node31Domains3 f h2 root4Node31Step3_checked
  have hb : Covers root4Node31Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node31Domains3 root4Outputs 8
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node32_cover
    · exact root4Node37_cover
  exact hb f h3
theorem root4Node30_cover : Covers root4Node30Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root4Node30Domains0 root4Node30Domains1 f hf root4Node30Step1_checked
  have hb : Covers root4Node30Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node30Domains1 root4Outputs 0
    intro s hs
    change s ∈ [(2,0),(4,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node31_cover
    · exact root4Node38_cover
  exact hb f h1
theorem root4Node29_cover : Covers root4Node29Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root4Node29Domains0 root4Node29Domains1 f hf root4Node29Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root4Node29Domains1 root4Node29Domains2 f h1 root4Node29Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node29Domains2 (.output 14)
    root4Node29Leaf_checked f h2
theorem root4Node28_cover : Covers root4Node28Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node28Domains0 root4Node28Domains1 f hf root4Node28Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node28Domains1 (.output 13)
    root4Node28Leaf_checked f h1
theorem root4Node27_cover : Covers root4Node27Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node27Domains0 root4Node27Domains1 f hf root4Node27Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node27Domains1 (.output 12)
    root4Node27Leaf_checked f h1
theorem root4Node26_cover : Covers root4Node26Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node26Domains0 root4Node26Domains1 f hf root4Node26Step1_checked
  have hb : Covers root4Node26Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node26Domains1 root4Outputs 34
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node27_cover
    · exact root4Node28_cover
  exact hb f h1
theorem root4Node25_cover : Covers root4Node25Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node25Domains0 root4Node25Domains1 f hf root4Node25Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root4Node25Domains1 root4Node25Domains2 f h1 root4Node25Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node25Domains2 (.output 11)
    root4Node25Leaf_checked f h2
theorem root4Node24_cover : Covers root4Node24Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root4Node24Domains0 root4Node24Domains1 f hf root4Node24Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root4Node24Domains1 root4Node24Domains2 f h1 root4Node24Step2_checked
  have hb : Covers root4Node24Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node24Domains2 root4Outputs 21
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node25_cover
    · exact root4Node26_cover
  exact hb f h2
theorem root4Node23_cover : Covers root4Node23Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root4Node23Domains0 root4Node23Domains1 f hf root4Node23Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root4Node23Domains1 root4Node23Domains2 f h1 root4Node23Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root4Node23Domains2 root4Node23Domains3 f h2 root4Node23Step3_checked
  have hb : Covers root4Node23Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node23Domains3 root4Outputs 8
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node24_cover
    · exact root4Node29_cover
  exact hb f h3
theorem root4Node22_cover : Covers root4Node22Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root4Node22Domains0 root4Node22Domains1 f hf root4Node22Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root4Node22Domains1 root4Node22Domains2 f h1 root4Node22Step2_checked
  have h3 := solution_checkReplacement constraints table7 table7_member
    root4Node22Domains2 root4Node22Domains3 f h2 root4Node22Step3_checked
  have hb : Covers root4Node22Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node22Domains3 root4Outputs 1
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node23_cover
    · exact root4Node30_cover
  exact hb f h3
theorem root4Node21_cover : Covers root4Node21Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root4Node21Domains0 root4Node21Domains1 f hf root4Node21Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root4Node21Domains1 root4Node21Domains2 f h1 root4Node21Step2_checked
  have h3 := solution_checkReplacement constraints table8 table8_member
    root4Node21Domains2 root4Node21Domains3 f h2 root4Node21Step3_checked
  have h4 := solution_checkReplacement constraints table22 table22_member
    root4Node21Domains3 root4Node21Domains4 f h3 root4Node21Step4_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node21Domains4 (.output 10)
    root4Node21Leaf_checked f h4
theorem root4Node20_cover : Covers root4Node20Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node20Domains0 root4Node20Domains1 f hf root4Node20Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node20Domains1 (.output 9)
    root4Node20Leaf_checked f h1
theorem root4Node19_cover : Covers root4Node19Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node19Domains0 root4Node19Domains1 f hf root4Node19Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node19Domains1 (.output 8)
    root4Node19Leaf_checked f h1
theorem root4Node18_cover : Covers root4Node18Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node18Domains0 root4Node18Domains1 f hf root4Node18Step1_checked
  have hb : Covers root4Node18Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node18Domains1 root4Outputs 34
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node19_cover
    · exact root4Node20_cover
  exact hb f h1
theorem root4Node17_cover : Covers root4Node17Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node17Domains0 root4Node17Domains1 f hf root4Node17Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root4Node17Domains1 root4Node17Domains2 f h1 root4Node17Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node17Domains2 (.output 7)
    root4Node17Leaf_checked f h2
theorem root4Node16_cover : Covers root4Node16Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root4Node16Domains0 root4Node16Domains1 f hf root4Node16Step1_checked
  have hb : Covers root4Node16Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node16Domains1 root4Outputs 21
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node17_cover
    · exact root4Node18_cover
  exact hb f h1
theorem root4Node15_cover : Covers root4Node15Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node15Domains0 root4Node15Domains1 f hf root4Node15Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node15Domains1 (.output 6)
    root4Node15Leaf_checked f h1
theorem root4Node14_cover : Covers root4Node14Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node14Domains0 root4Node14Domains1 f hf root4Node14Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node14Domains1 (.output 5)
    root4Node14Leaf_checked f h1
theorem root4Node13_cover : Covers root4Node13Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node13Domains0 root4Node13Domains1 f hf root4Node13Step1_checked
  have hb : Covers root4Node13Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node13Domains1 root4Outputs 34
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node14_cover
    · exact root4Node15_cover
  exact hb f h1
theorem root4Node12_cover : Covers root4Node12Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node12Domains0 root4Node12Domains1 f hf root4Node12Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root4Node12Domains1 root4Node12Domains2 f h1 root4Node12Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node12Domains2 (.output 4)
    root4Node12Leaf_checked f h2
theorem root4Node11_cover : Covers root4Node11Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root4Node11Domains0 root4Node11Domains1 f hf root4Node11Step1_checked
  have hb : Covers root4Node11Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node11Domains1 root4Outputs 21
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node12_cover
    · exact root4Node13_cover
  exact hb f h1
theorem root4Node10_cover : Covers root4Node10Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root4Node10Domains0 root4Node10Domains1 f hf root4Node10Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node10Domains1 root4Node10Domains2 f h1 root4Node10Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root4Node10Domains2 root4Node10Domains3 f h2 root4Node10Step3_checked
  have hb : Covers root4Node10Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node10Domains3 root4Outputs 4
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node11_cover
    · exact root4Node16_cover
  exact hb f h3
theorem root4Node9_cover : Covers root4Node9Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root4Node9Domains0 root4Node9Domains1 f hf root4Node9Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root4Node9Domains1 root4Node9Domains2 f h1 root4Node9Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node9Domains2 (.output 3)
    root4Node9Leaf_checked f h2
theorem root4Node8_cover : Covers root4Node8Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node8Domains0 root4Node8Domains1 f hf root4Node8Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node8Domains1 (.output 2)
    root4Node8Leaf_checked f h1
theorem root4Node7_cover : Covers root4Node7Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node7Domains0 root4Node7Domains1 f hf root4Node7Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node7Domains1 (.output 1)
    root4Node7Leaf_checked f h1
theorem root4Node6_cover : Covers root4Node6Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node6Domains0 root4Node6Domains1 f hf root4Node6Step1_checked
  have hb : Covers root4Node6Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node6Domains1 root4Outputs 34
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node7_cover
    · exact root4Node8_cover
  exact hb f h1
theorem root4Node5_cover : Covers root4Node5Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root4Node5Domains0 root4Node5Domains1 f hf root4Node5Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root4Node5Domains1 root4Node5Domains2 f h1 root4Node5Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node5Domains2 (.output 0)
    root4Node5Leaf_checked f h2
theorem root4Node4_cover : Covers root4Node4Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root4Node4Domains0 root4Node4Domains1 f hf root4Node4Step1_checked
  have hb : Covers root4Node4Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node4Domains1 root4Outputs 21
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node5_cover
    · exact root4Node6_cover
  exact hb f h1
theorem root4Node3_cover : Covers root4Node3Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root4Node3Domains0 root4Node3Domains1 f hf root4Node3Step1_checked
  have h2 := solution_checkReplacement constraints table7 table7_member
    root4Node3Domains1 root4Node3Domains2 f h1 root4Node3Step2_checked
  have h3 := solution_checkReplacement constraints table16 table16_member
    root4Node3Domains2 root4Node3Domains3 f h2 root4Node3Step3_checked
  have hb : Covers root4Node3Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node3Domains3 root4Outputs 8
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node4_cover
    · exact root4Node9_cover
  exact hb f h3
theorem root4Node2_cover : Covers root4Node2Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root4Node2Domains0 root4Node2Domains1 f hf root4Node2Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root4Node2Domains1 root4Node2Domains2 f h1 root4Node2Step2_checked
  have h3 := solution_checkReplacement constraints table25 table25_member
    root4Node2Domains2 root4Node2Domains3 f h2 root4Node2Step3_checked
  have hb : Covers root4Node2Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node2Domains3 root4Outputs 2
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node3_cover
    · exact root4Node10_cover
  exact hb f h3
theorem root4Node1_cover : Covers root4Node1Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root4Node1Domains0 root4Node1Domains1 f hf root4Node1Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root4Node1Domains1 root4Node1Domains2 f h1 root4Node1Step2_checked
  have hb : Covers root4Node1Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node1Domains2 root4Outputs 0
    intro s hs
    change s ∈ [(4,2),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node2_cover
    · exact root4Node21_cover
  exact hb f h2
theorem root4Node0_cover : Covers root4Node0Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root4Node0Domains0 root4Node0Domains1 f hf root4Node0Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root4Node0Domains1 root4Node0Domains2 f h1 root4Node0Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root4Node0Domains2 root4Node0Domains3 f h2 root4Node0Step3_checked
  have h4 := solution_checkReplacement constraints table25 table25_member
    root4Node0Domains3 root4Node0Domains4 f h3 root4Node0Step4_checked
  have hb : Covers root4Node0Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node0Domains4 root4Outputs 3
    intro s hs
    change s ∈ [(7,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node1_cover
    · exact root4Node22_cover
  exact hb f h4
theorem root4_table_cover : Covers (domains (4,0)) constraints root4Outputs := root4Node0_cover
theorem root4Family_count : root4Family.length = 22 := rfl
#print axioms root4_table_cover
end SpectreFinite.HexSearch.RadiusThree
