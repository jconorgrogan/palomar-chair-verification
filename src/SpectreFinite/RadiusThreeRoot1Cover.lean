module

public import SpectreFinite.RadiusThreeRoot1Part29

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root1Node50_cover : Covers root1Node50Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node50Domains0 root1Node50Domains1 f hf root1Node50Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node50Domains1 (.output 25)
    root1Node50Leaf_checked f h1
theorem root1Node49_cover : Covers root1Node49Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node49Domains0 (.output 24)
    root1Node49Leaf_checked f hf
theorem root1Node48_cover : Covers root1Node48Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node48Domains0 (.output 23)
    root1Node48Leaf_checked f hf
theorem root1Node47_cover : Covers root1Node47Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node47Domains0 root1Node47Domains1 f hf root1Node47Step1_checked
  have hb : Covers root1Node47Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node47Domains1 root1Outputs 35
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node48_cover
    · exact root1Node49_cover
  exact hb f h1
theorem root1Node46_cover : Covers root1Node46Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node46Domains0 root1Node46Domains1 f hf root1Node46Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root1Node46Domains1 root1Node46Domains2 f h1 root1Node46Step2_checked
  have hb : Covers root1Node46Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node46Domains2 root1Outputs 23
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node47_cover
    · exact root1Node50_cover
  exact hb f h2
theorem root1Node45_cover : Covers root1Node45Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node45Domains0 root1Node45Domains1 f hf root1Node45Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node45Domains1 root1Node45Domains2 f h1 root1Node45Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node45Domains2 (.output 22)
    root1Node45Leaf_checked f h2
theorem root1Node44_cover : Covers root1Node44Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node44Domains0 root1Node44Domains1 f hf root1Node44Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node44Domains1 root1Node44Domains2 f h1 root1Node44Step2_checked
  have h3 := solution_checkReplacement constraints table9 table9_member
    root1Node44Domains2 root1Node44Domains3 f h2 root1Node44Step3_checked
  have hb : Covers root1Node44Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node44Domains3 root1Outputs 8
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node45_cover
    · exact root1Node46_cover
  exact hb f h3
theorem root1Node43_cover : Covers root1Node43Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root1Node43Domains0 root1Node43Domains1 f hf root1Node43Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root1Node43Domains1 root1Node43Domains2 f h1 root1Node43Step2_checked
  have h3 := solution_checkReplacement constraints table8 table8_member
    root1Node43Domains2 root1Node43Domains3 f h2 root1Node43Step3_checked
  have h4 := solution_checkReplacement constraints table22 table22_member
    root1Node43Domains3 root1Node43Domains4 f h3 root1Node43Step4_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node43Domains4 (.output 21)
    root1Node43Leaf_checked f h4
theorem root1Node42_cover : Covers root1Node42Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root1Node42Domains0 root1Node42Domains1 f hf root1Node42Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root1Node42Domains1 root1Node42Domains2 f h1 root1Node42Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node42Domains2 (.output 20)
    root1Node42Leaf_checked f h2
theorem root1Node41_cover : Covers root1Node41Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node41Domains0 root1Node41Domains1 f hf root1Node41Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node41Domains1 root1Node41Domains2 f h1 root1Node41Step2_checked
  have hb : Covers root1Node41Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node41Domains2 root1Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node42_cover
    · exact root1Node43_cover
  exact hb f h2
theorem root1Node40_cover : Covers root1Node40Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node40Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node40Domains0 root1Outputs 3
    intro s hs
    change s ∈ [(0,3),(6,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node41_cover
    · exact root1Node44_cover
  exact hb f hf
theorem root1Node39_cover : Covers root1Node39Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node39Domains0 root1Node39Domains1 f hf root1Node39Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node39Domains1 (.output 19)
    root1Node39Leaf_checked f h1
theorem root1Node38_cover : Covers root1Node38Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node38Domains0 (.output 18)
    root1Node38Leaf_checked f hf
theorem root1Node37_cover : Covers root1Node37Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node37Domains0 (.output 17)
    root1Node37Leaf_checked f hf
theorem root1Node36_cover : Covers root1Node36Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node36Domains0 root1Node36Domains1 f hf root1Node36Step1_checked
  have hb : Covers root1Node36Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node36Domains1 root1Outputs 35
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node37_cover
    · exact root1Node38_cover
  exact hb f h1
theorem root1Node35_cover : Covers root1Node35Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node35Domains0 root1Node35Domains1 f hf root1Node35Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root1Node35Domains1 root1Node35Domains2 f h1 root1Node35Step2_checked
  have hb : Covers root1Node35Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node35Domains2 root1Outputs 23
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node36_cover
    · exact root1Node39_cover
  exact hb f h2
theorem root1Node34_cover : Covers root1Node34Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node34Domains0 root1Node34Domains1 f hf root1Node34Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node34Domains1 root1Node34Domains2 f h1 root1Node34Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node34Domains2 (.output 16)
    root1Node34Leaf_checked f h2
theorem root1Node33_cover : Covers root1Node33Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node33Domains0 root1Node33Domains1 f hf root1Node33Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node33Domains1 root1Node33Domains2 f h1 root1Node33Step2_checked
  have h3 := solution_checkReplacement constraints table9 table9_member
    root1Node33Domains2 root1Node33Domains3 f h2 root1Node33Step3_checked
  have hb : Covers root1Node33Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node33Domains3 root1Outputs 8
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node34_cover
    · exact root1Node35_cover
  exact hb f h3
theorem root1Node32_cover : Covers root1Node32Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root1Node32Domains0 root1Node32Domains1 f hf root1Node32Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node32Domains1 (.output 15)
    root1Node32Leaf_checked f h1
theorem root1Node31_cover : Covers root1Node31Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root1Node31Domains0 root1Node31Domains1 f hf root1Node31Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node31Domains1 (.output 14)
    root1Node31Leaf_checked f h1
theorem root1Node30_cover : Covers root1Node30Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node30Domains0 root1Node30Domains1 f hf root1Node30Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node30Domains1 root1Node30Domains2 f h1 root1Node30Step2_checked
  have h3 := solution_checkReplacement constraints table11 table11_member
    root1Node30Domains2 root1Node30Domains3 f h2 root1Node30Step3_checked
  have h4 := solution_checkReplacement constraints table25 table25_member
    root1Node30Domains3 root1Node30Domains4 f h3 root1Node30Step4_checked
  have h5 := solution_checkReplacement constraints table22 table22_member
    root1Node30Domains4 root1Node30Domains5 f h4 root1Node30Step5_checked
  have h6 := solution_checkReplacement constraints table8 table8_member
    root1Node30Domains5 root1Node30Domains6 f h5 root1Node30Step6_checked
  have hb : Covers root1Node30Domains6 constraints root1Outputs := by
    apply covers_of_branches root1Node30Domains6 root1Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node31_cover
    · exact root1Node32_cover
  exact hb f h6
theorem root1Node29_cover : Covers root1Node29Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node29Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node29Domains0 root1Outputs 3
    intro s hs
    change s ∈ [(0,3),(6,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node30_cover
    · exact root1Node33_cover
  exact hb f hf
theorem root1Node28_cover : Covers root1Node28Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root1Node28Domains0 root1Node28Domains1 f hf root1Node28Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root1Node28Domains1 root1Node28Domains2 f h1 root1Node28Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root1Node28Domains2 root1Node28Domains3 f h2 root1Node28Step3_checked
  have h4 := solution_checkReplacement constraints table24 table24_member
    root1Node28Domains3 root1Node28Domains4 f h3 root1Node28Step4_checked
  have hb : Covers root1Node28Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node28Domains4 root1Outputs 0
    intro s hs
    change s ∈ [(1,0),(6,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node29_cover
    · exact root1Node40_cover
  exact hb f h4
theorem root1Node27_cover : Covers root1Node27Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node27Domains0 root1Node27Domains1 f hf root1Node27Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node27Domains1 (.output 13)
    root1Node27Leaf_checked f h1
theorem root1Node26_cover : Covers root1Node26Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node26Domains0 root1Node26Domains1 f hf root1Node26Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node26Domains1 (.output 12)
    root1Node26Leaf_checked f h1
theorem root1Node25_cover : Covers root1Node25Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root1Node25Domains0 root1Node25Domains1 f hf root1Node25Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node25Domains1 root1Node25Domains2 f h1 root1Node25Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root1Node25Domains2 root1Node25Domains3 f h2 root1Node25Step3_checked
  have hb : Covers root1Node25Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node25Domains3 root1Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node26_cover
    · exact root1Node27_cover
  exact hb f h3
theorem root1Node24_cover : Covers root1Node24Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node24Domains0 root1Node24Domains1 f hf root1Node24Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node24Domains1 (.output 11)
    root1Node24Leaf_checked f h1
theorem root1Node23_cover : Covers root1Node23Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node23Domains0 (.output 10)
    root1Node23Leaf_checked f hf
theorem root1Node22_cover : Covers root1Node22Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node22Domains0 (.output 9)
    root1Node22Leaf_checked f hf
theorem root1Node21_cover : Covers root1Node21Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node21Domains0 root1Node21Domains1 f hf root1Node21Step1_checked
  have hb : Covers root1Node21Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node21Domains1 root1Outputs 35
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node22_cover
    · exact root1Node23_cover
  exact hb f h1
theorem root1Node20_cover : Covers root1Node20Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node20Domains0 root1Node20Domains1 f hf root1Node20Step1_checked
  have hb : Covers root1Node20Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node20Domains1 root1Outputs 23
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node21_cover
    · exact root1Node24_cover
  exact hb f h1
theorem root1Node19_cover : Covers root1Node19Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node19Domains0 root1Node19Domains1 f hf root1Node19Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root1Node19Domains1 root1Node19Domains2 f h1 root1Node19Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node19Domains2 (.output 8)
    root1Node19Leaf_checked f h2
theorem root1Node18_cover : Covers root1Node18Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node18Domains0 root1Node18Domains1 f hf root1Node18Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root1Node18Domains1 root1Node18Domains2 f h1 root1Node18Step2_checked
  have hb : Covers root1Node18Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node18Domains2 root1Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node19_cover
    · exact root1Node20_cover
  exact hb f h2
theorem root1Node17_cover : Covers root1Node17Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node17Domains0 root1Node17Domains1 f hf root1Node17Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node17Domains1 root1Node17Domains2 f h1 root1Node17Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node17Domains2 (.output 7)
    root1Node17Leaf_checked f h2
theorem root1Node16_cover : Covers root1Node16Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root1Node16Domains0 root1Node16Domains1 f hf root1Node16Step1_checked
  have hb : Covers root1Node16Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node16Domains1 root1Outputs 8
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node17_cover
    · exact root1Node18_cover
  exact hb f h1
theorem root1Node15_cover : Covers root1Node15Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node15Domains0 root1Node15Domains1 f hf root1Node15Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node15Domains1 (.output 6)
    root1Node15Leaf_checked f h1
theorem root1Node14_cover : Covers root1Node14Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node14Domains0 (.output 5)
    root1Node14Leaf_checked f hf
theorem root1Node13_cover : Covers root1Node13Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node13Domains0 (.output 4)
    root1Node13Leaf_checked f hf
theorem root1Node12_cover : Covers root1Node12Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node12Domains0 root1Node12Domains1 f hf root1Node12Step1_checked
  have hb : Covers root1Node12Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node12Domains1 root1Outputs 35
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node13_cover
    · exact root1Node14_cover
  exact hb f h1
theorem root1Node11_cover : Covers root1Node11Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root1Node11Domains0 root1Node11Domains1 f hf root1Node11Step1_checked
  have hb : Covers root1Node11Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node11Domains1 root1Outputs 23
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node12_cover
    · exact root1Node15_cover
  exact hb f h1
theorem root1Node10_cover : Covers root1Node10Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node10Domains0 root1Node10Domains1 f hf root1Node10Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root1Node10Domains1 root1Node10Domains2 f h1 root1Node10Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node10Domains2 (.output 3)
    root1Node10Leaf_checked f h2
theorem root1Node9_cover : Covers root1Node9Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node9Domains0 root1Node9Domains1 f hf root1Node9Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root1Node9Domains1 root1Node9Domains2 f h1 root1Node9Step2_checked
  have hb : Covers root1Node9Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node9Domains2 root1Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node10_cover
    · exact root1Node11_cover
  exact hb f h2
theorem root1Node8_cover : Covers root1Node8Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node8Domains0 root1Node8Domains1 f hf root1Node8Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node8Domains1 root1Node8Domains2 f h1 root1Node8Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node8Domains2 (.output 2)
    root1Node8Leaf_checked f h2
theorem root1Node7_cover : Covers root1Node7Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root1Node7Domains0 root1Node7Domains1 f hf root1Node7Step1_checked
  have hb : Covers root1Node7Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node7Domains1 root1Outputs 8
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node8_cover
    · exact root1Node9_cover
  exact hb f h1
theorem root1Node6_cover : Covers root1Node6Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root1Node6Domains0 root1Node6Domains1 f hf root1Node6Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root1Node6Domains1 root1Node6Domains2 f h1 root1Node6Step2_checked
  have hb : Covers root1Node6Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node6Domains2 root1Outputs 4
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node7_cover
    · exact root1Node16_cover
  exact hb f h2
theorem root1Node5_cover : Covers root1Node5Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root1Node5Domains0 root1Node5Domains1 f hf root1Node5Step1_checked
  have hb : Covers root1Node5Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node5Domains1 root1Outputs 0
    intro s hs
    change s ∈ [(0,2),(1,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node6_cover
    · exact root1Node25_cover
  exact hb f h1
theorem root1Node4_cover : Covers root1Node4Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node4Domains0 root1Node4Domains1 f hf root1Node4Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node4Domains1 (.output 1)
    root1Node4Leaf_checked f h1
theorem root1Node3_cover : Covers root1Node3Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node3Domains0 root1Node3Domains1 f hf root1Node3Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node3Domains1 (.output 0)
    root1Node3Leaf_checked f h1
theorem root1Node2_cover : Covers root1Node2Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root1Node2Domains0 root1Node2Domains1 f hf root1Node2Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root1Node2Domains1 root1Node2Domains2 f h1 root1Node2Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root1Node2Domains2 root1Node2Domains3 f h2 root1Node2Step3_checked
  have h4 := solution_checkReplacement constraints table23 table23_member
    root1Node2Domains3 root1Node2Domains4 f h3 root1Node2Step4_checked
  have hb : Covers root1Node2Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node2Domains4 root1Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node3_cover
    · exact root1Node4_cover
  exact hb f h4
theorem root1Node1_cover : Covers root1Node1Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node1Domains0 root1Node1Domains1 f hf root1Node1Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root1Node1Domains1 root1Node1Domains2 f h1 root1Node1Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root1Node1Domains2 root1Node1Domains3 f h2 root1Node1Step3_checked
  have h4 := solution_checkReplacement constraints table13 table13_member
    root1Node1Domains3 root1Node1Domains4 f h3 root1Node1Step4_checked
  have hb : Covers root1Node1Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node1Domains4 root1Outputs 6
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node2_cover
    · exact root1Node5_cover
  exact hb f h4
theorem root1Node0_cover : Covers root1Node0Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node0Domains0 root1Node0Domains1 f hf root1Node0Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root1Node0Domains1 root1Node0Domains2 f h1 root1Node0Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root1Node0Domains2 root1Node0Domains3 f h2 root1Node0Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root1Node0Domains3 root1Node0Domains4 f h3 root1Node0Step4_checked
  have hb : Covers root1Node0Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node0Domains4 root1Outputs 2
    intro s hs
    change s ∈ [(4,1),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node1_cover
    · exact root1Node28_cover
  exact hb f h4
theorem root1_table_cover : Covers (domains (1,0)) constraints root1Outputs := root1Node0_cover
theorem root1Family_count : root1Family.length = 26 := rfl
#print axioms root1_table_cover
end SpectreFinite.HexSearch.RadiusThree
