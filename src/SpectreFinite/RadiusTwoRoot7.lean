module

public import SpectreFinite.RadiusTwoRoot7Part9

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node58_cover : Covers root7Node58Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node58Domains0 root7Node58Domains1 f hf root7Node58Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node58Domains1 (.output 29)
    root7Node58Leaf_checked f h1
theorem root7Node57_cover : Covers root7Node57Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node57Domains0 root7Node57Domains1 f hf root7Node57Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node57Domains1 (.output 28)
    root7Node57Leaf_checked f h1
theorem root7Node56_cover : Covers root7Node56Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node56Domains0 root7Node56Domains1 f hf root7Node56Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node56Domains1 root7Node56Domains2 f h1 root7Node56Step2_checked
  have hb : Covers root7Node56Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node56Domains2 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node57_cover
    · exact root7Node58_cover
  exact hb f h2
theorem root7Node55_cover : Covers root7Node55Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node55Domains0 (.output 27)
    root7Node55Leaf_checked f hf
theorem root7Node54_cover : Covers root7Node54Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node54Domains0 (.output 26)
    root7Node54Leaf_checked f hf
theorem root7Node53_cover : Covers root7Node53Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node53Domains0 root7Node53Domains1 f hf root7Node53Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node53Domains1 root7Node53Domains2 f h1 root7Node53Step2_checked
  have hb : Covers root7Node53Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node53Domains2 root7Outputs 11
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node54_cover
    · exact root7Node55_cover
  exact hb f h2
theorem root7Node52_cover : Covers root7Node52Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node52Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node52Domains0 root7Outputs 8
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node53_cover
    · exact root7Node56_cover
  exact hb f hf
theorem root7Node51_cover : Covers root7Node51Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node51Domains0 root7Node51Domains1 f hf root7Node51Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node51Domains1 (.output 25)
    root7Node51Leaf_checked f h1
theorem root7Node50_cover : Covers root7Node50Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node50Domains0 root7Node50Domains1 f hf root7Node50Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node50Domains1 (.output 24)
    root7Node50Leaf_checked f h1
theorem root7Node49_cover : Covers root7Node49Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node49Domains0 root7Node49Domains1 f hf root7Node49Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node49Domains1 root7Node49Domains2 f h1 root7Node49Step2_checked
  have hb : Covers root7Node49Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node49Domains2 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node50_cover
    · exact root7Node51_cover
  exact hb f h2
theorem root7Node48_cover : Covers root7Node48Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node48Domains0 (.output 23)
    root7Node48Leaf_checked f hf
theorem root7Node47_cover : Covers root7Node47Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node47Domains0 (.output 22)
    root7Node47Leaf_checked f hf
theorem root7Node46_cover : Covers root7Node46Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node46Domains0 root7Node46Domains1 f hf root7Node46Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node46Domains1 root7Node46Domains2 f h1 root7Node46Step2_checked
  have hb : Covers root7Node46Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node46Domains2 root7Outputs 11
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node47_cover
    · exact root7Node48_cover
  exact hb f h2
theorem root7Node45_cover : Covers root7Node45Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node45Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node45Domains0 root7Outputs 8
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node46_cover
    · exact root7Node49_cover
  exact hb f hf
theorem root7Node44_cover : Covers root7Node44Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root7Node44Domains0 root7Node44Domains1 f hf root7Node44Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root7Node44Domains1 root7Node44Domains2 f h1 root7Node44Step2_checked
  have hb : Covers root7Node44Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node44Domains2 root7Outputs 7
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node45_cover
    · exact root7Node52_cover
  exact hb f h2
theorem root7Node43_cover : Covers root7Node43Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node43Domains0 root7Node43Domains1 f hf root7Node43Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node43Domains1 (.output 21)
    root7Node43Leaf_checked f h1
theorem root7Node42_cover : Covers root7Node42Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node42Domains0 root7Node42Domains1 f hf root7Node42Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node42Domains1 (.output 20)
    root7Node42Leaf_checked f h1
theorem root7Node41_cover : Covers root7Node41Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root7Node41Domains0 root7Node41Domains1 f hf root7Node41Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root7Node41Domains1 root7Node41Domains2 f h1 root7Node41Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root7Node41Domains2 root7Node41Domains3 f h2 root7Node41Step3_checked
  have hb : Covers root7Node41Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node41Domains3 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node42_cover
    · exact root7Node43_cover
  exact hb f h3
theorem root7Node40_cover : Covers root7Node40Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root7Node40Domains0 root7Node40Domains1 f hf root7Node40Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node40Domains1 root7Node40Domains2 f h1 root7Node40Step2_checked
  have hb : Covers root7Node40Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node40Domains2 root7Outputs 3
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node41_cover
    · exact root7Node44_cover
  exact hb f h2
theorem root7Node39_cover : Covers root7Node39Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root7Node39Domains0 root7Node39Domains1 f hf root7Node39Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node39Domains1 (.output 19)
    root7Node39Leaf_checked f h1
theorem root7Node38_cover : Covers root7Node38Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root7Node38Domains0 root7Node38Domains1 f hf root7Node38Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node38Domains1 (.output 18)
    root7Node38Leaf_checked f h1
theorem root7Node37_cover : Covers root7Node37Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node37Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node37Domains0 root7Outputs 10
    intro s hs
    change s ∈ [(2,3),(4,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node38_cover
    · exact root7Node39_cover
  exact hb f hf
theorem root7Node36_cover : Covers root7Node36Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root7Node36Domains0 root7Node36Domains1 f hf root7Node36Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node36Domains1 (.output 17)
    root7Node36Leaf_checked f h1
theorem root7Node35_cover : Covers root7Node35Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root7Node35Domains0 root7Node35Domains1 f hf root7Node35Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node35Domains1 (.output 16)
    root7Node35Leaf_checked f h1
theorem root7Node34_cover : Covers root7Node34Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node34Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node34Domains0 root7Outputs 10
    intro s hs
    change s ∈ [(2,3),(4,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node35_cover
    · exact root7Node36_cover
  exact hb f hf
theorem root7Node33_cover : Covers root7Node33Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root7Node33Domains0 root7Node33Domains1 f hf root7Node33Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node33Domains1 root7Node33Domains2 f h1 root7Node33Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root7Node33Domains2 root7Node33Domains3 f h2 root7Node33Step3_checked
  have h4 := solution_checkReplacement constraints table3 table3_member
    root7Node33Domains3 root7Node33Domains4 f h3 root7Node33Step4_checked
  have hb : Covers root7Node33Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node33Domains4 root7Outputs 7
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node34_cover
    · exact root7Node37_cover
  exact hb f h4
theorem root7Node32_cover : Covers root7Node32Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node32Domains0 root7Node32Domains1 f hf root7Node32Step1_checked
  have hb : Covers root7Node32Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node32Domains1 root7Outputs 2
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node33_cover
    · exact root7Node40_cover
  exact hb f h1
theorem root7Node31_cover : Covers root7Node31Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node31Domains0 root7Node31Domains1 f hf root7Node31Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node31Domains1 (.output 15)
    root7Node31Leaf_checked f h1
theorem root7Node30_cover : Covers root7Node30Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node30Domains0 root7Node30Domains1 f hf root7Node30Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node30Domains1 (.output 14)
    root7Node30Leaf_checked f h1
theorem root7Node29_cover : Covers root7Node29Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root7Node29Domains0 root7Node29Domains1 f hf root7Node29Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root7Node29Domains1 root7Node29Domains2 f h1 root7Node29Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root7Node29Domains2 root7Node29Domains3 f h2 root7Node29Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root7Node29Domains3 root7Node29Domains4 f h3 root7Node29Step4_checked
  have h5 := solution_checkReplacement constraints table2 table2_member
    root7Node29Domains4 root7Node29Domains5 f h4 root7Node29Step5_checked
  have hb : Covers root7Node29Domains5 constraints root7Outputs := by
    apply covers_of_branches root7Node29Domains5 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node30_cover
    · exact root7Node31_cover
  exact hb f h5
theorem root7Node28_cover : Covers root7Node28Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root7Node28Domains0 root7Node28Domains1 f hf root7Node28Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root7Node28Domains1 root7Node28Domains2 f h1 root7Node28Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root7Node28Domains2 root7Node28Domains3 f h2 root7Node28Step3_checked
  have hb : Covers root7Node28Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node28Domains3 root7Outputs 0
    intro s hs
    change s ∈ [(2,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node29_cover
    · exact root7Node32_cover
  exact hb f h3
theorem root7Node27_cover : Covers root7Node27Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root7Node27Domains0 root7Node27Domains1 f hf root7Node27Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node27Domains1 root7Node27Domains2 f h1 root7Node27Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node27Domains2 (.output 13)
    root7Node27Leaf_checked f h2
theorem root7Node26_cover : Covers root7Node26Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node26Domains0 root7Node26Domains1 f hf root7Node26Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node26Domains1 (.output 12)
    root7Node26Leaf_checked f h1
theorem root7Node25_cover : Covers root7Node25Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node25Domains0 root7Node25Domains1 f hf root7Node25Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node25Domains1 (.output 11)
    root7Node25Leaf_checked f h1
theorem root7Node24_cover : Covers root7Node24Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node24Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node24Domains0 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node25_cover
    · exact root7Node26_cover
  exact hb f hf
theorem root7Node23_cover : Covers root7Node23Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node23Domains0 root7Node23Domains1 f hf root7Node23Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node23Domains1 root7Node23Domains2 f h1 root7Node23Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root7Node23Domains2 root7Node23Domains3 f h2 root7Node23Step3_checked
  have hb : Covers root7Node23Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node23Domains3 root7Outputs 6
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node24_cover
    · exact root7Node27_cover
  exact hb f h3
theorem root7Node22_cover : Covers root7Node22Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node22Domains0 (.output 10)
    root7Node22Leaf_checked f hf
theorem root7Node21_cover : Covers root7Node21Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node21Domains0 (.output 9)
    root7Node21Leaf_checked f hf
theorem root7Node20_cover : Covers root7Node20Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root7Node20Domains0 root7Node20Domains1 f hf root7Node20Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node20Domains1 root7Node20Domains2 f h1 root7Node20Step2_checked
  have hb : Covers root7Node20Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node20Domains2 root7Outputs 6
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node21_cover
    · exact root7Node22_cover
  exact hb f h2
theorem root7Node19_cover : Covers root7Node19Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root7Node19Domains0 root7Node19Domains1 f hf root7Node19Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node19Domains1 root7Node19Domains2 f h1 root7Node19Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node19Domains2 (.output 8)
    root7Node19Leaf_checked f h2
theorem root7Node18_cover : Covers root7Node18Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node18Domains0 root7Node18Domains1 f hf root7Node18Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node18Domains1 root7Node18Domains2 f h1 root7Node18Step2_checked
  have hb : Covers root7Node18Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node18Domains2 root7Outputs 10
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node19_cover
    · exact root7Node20_cover
  exact hb f h2
theorem root7Node17_cover : Covers root7Node17Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root7Node17Domains0 root7Node17Domains1 f hf root7Node17Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root7Node17Domains1 root7Node17Domains2 f h1 root7Node17Step2_checked
  have hb : Covers root7Node17Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node17Domains2 root7Outputs 8
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node18_cover
    · exact root7Node23_cover
  exact hb f h2
theorem root7Node16_cover : Covers root7Node16Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root7Node16Domains0 root7Node16Domains1 f hf root7Node16Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node16Domains1 root7Node16Domains2 f h1 root7Node16Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node16Domains2 (.output 7)
    root7Node16Leaf_checked f h2
theorem root7Node15_cover : Covers root7Node15Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node15Domains0 root7Node15Domains1 f hf root7Node15Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node15Domains1 (.output 6)
    root7Node15Leaf_checked f h1
theorem root7Node14_cover : Covers root7Node14Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node14Domains0 root7Node14Domains1 f hf root7Node14Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node14Domains1 (.output 5)
    root7Node14Leaf_checked f h1
theorem root7Node13_cover : Covers root7Node13Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node13Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node13Domains0 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node14_cover
    · exact root7Node15_cover
  exact hb f hf
theorem root7Node12_cover : Covers root7Node12Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root7Node12Domains0 root7Node12Domains1 f hf root7Node12Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node12Domains1 root7Node12Domains2 f h1 root7Node12Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root7Node12Domains2 root7Node12Domains3 f h2 root7Node12Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root7Node12Domains3 root7Node12Domains4 f h3 root7Node12Step4_checked
  have hb : Covers root7Node12Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node12Domains4 root7Outputs 6
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node13_cover
    · exact root7Node16_cover
  exact hb f h4
theorem root7Node11_cover : Covers root7Node11Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node11Domains0 root7Node11Domains1 f hf root7Node11Step1_checked
  have hb : Covers root7Node11Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node11Domains1 root7Outputs 3
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node12_cover
    · exact root7Node17_cover
  exact hb f h1
theorem root7Node10_cover : Covers root7Node10Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root7Node10Domains0 root7Node10Domains1 f hf root7Node10Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node10Domains1 root7Node10Domains2 f h1 root7Node10Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node10Domains2 (.output 4)
    root7Node10Leaf_checked f h2
theorem root7Node9_cover : Covers root7Node9Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node9Domains0 root7Node9Domains1 f hf root7Node9Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node9Domains1 (.output 3)
    root7Node9Leaf_checked f h1
theorem root7Node8_cover : Covers root7Node8Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node8Domains0 root7Node8Domains1 f hf root7Node8Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node8Domains1 (.output 2)
    root7Node8Leaf_checked f h1
theorem root7Node7_cover : Covers root7Node7Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node7Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node7Domains0 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node8_cover
    · exact root7Node9_cover
  exact hb f hf
theorem root7Node6_cover : Covers root7Node6Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node6Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node6Domains0 root7Outputs 6
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node7_cover
    · exact root7Node10_cover
  exact hb f hf
theorem root7Node5_cover : Covers root7Node5Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node5Domains0 root7Node5Domains1 f hf root7Node5Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node5Domains1 (.output 1)
    root7Node5Leaf_checked f h1
theorem root7Node4_cover : Covers root7Node4Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root7Node4Domains0 root7Node4Domains1 f hf root7Node4Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node4Domains1 (.output 0)
    root7Node4Leaf_checked f h1
theorem root7Node3_cover : Covers root7Node3Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root7Node3Domains0 root7Node3Domains1 f hf root7Node3Step1_checked
  have hb : Covers root7Node3Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node3Domains1 root7Outputs 15
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node4_cover
    · exact root7Node5_cover
  exact hb f h1
theorem root7Node2_cover : Covers root7Node2Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root7Node2Domains0 root7Node2Domains1 f hf root7Node2Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root7Node2Domains1 root7Node2Domains2 f h1 root7Node2Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root7Node2Domains2 root7Node2Domains3 f h2 root7Node2Step3_checked
  have h4 := solution_checkReplacement constraints table5 table5_member
    root7Node2Domains3 root7Node2Domains4 f h3 root7Node2Step4_checked
  have hb : Covers root7Node2Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node2Domains4 root7Outputs 2
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node3_cover
    · exact root7Node6_cover
  exact hb f h4
theorem root7Node1_cover : Covers root7Node1Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root7Node1Domains0 root7Node1Domains1 f hf root7Node1Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root7Node1Domains1 root7Node1Domains2 f h1 root7Node1Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root7Node1Domains2 root7Node1Domains3 f h2 root7Node1Step3_checked
  have hb : Covers root7Node1Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node1Domains3 root7Outputs 0
    intro s hs
    change s ∈ [(4,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node2_cover
    · exact root7Node11_cover
  exact hb f h3
theorem root7Node0_cover : Covers root7Node0Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root7Node0Domains0 root7Node0Domains1 f hf root7Node0Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root7Node0Domains1 root7Node0Domains2 f h1 root7Node0Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root7Node0Domains2 root7Node0Domains3 f h2 root7Node0Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root7Node0Domains3 root7Node0Domains4 f h3 root7Node0Step4_checked
  have h5 := solution_checkReplacement constraints table3 table3_member
    root7Node0Domains4 root7Node0Domains5 f h4 root7Node0Step5_checked
  have hb : Covers root7Node0Domains5 constraints root7Outputs := by
    apply covers_of_branches root7Node0Domains5 root7Outputs 1
    intro s hs
    change s ∈ [(0,0),(1,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node1_cover
    · exact root7Node28_cover
  exact hb f h5
theorem root7_table_cover : Covers (domains (7,0)) constraints root7Outputs :=
  root7Node0_cover

theorem root7Family_count : root7Family.length = 30 := rfl

theorem extract_mem_root7Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (7,0)) :
    extract f center (hexRegion 2) ∈ root7Family := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (7,0) (hexRegion 2) root7Outputs
    root7_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root7Family] using h
#print axioms extract_mem_root7Family
end SpectreFinite.HexSearch.RadiusTwo
