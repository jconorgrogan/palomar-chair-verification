module

public import SpectreFinite.RadiusFourRoot5Part18

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root5Node58_cover : Covers root5Node58Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node58Domains0 root5Node58Domains1 f hf root5Node58Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node58Domains1 (.output 29)
    root5Node58Leaf_checked f h1
theorem root5Node57_cover : Covers root5Node57Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node57Domains0 root5Node57Domains1 f hf root5Node57Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node57Domains1 (.output 28)
    root5Node57Leaf_checked f h1
theorem root5Node56_cover : Covers root5Node56Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root5Node56Domains0 root5Node56Domains1 f hf root5Node56Step1_checked
  have hb : Covers root5Node56Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node56Domains1 root5Outputs 52
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node57_cover
    · exact root5Node58_cover
  exact hb f h1
theorem root5Node55_cover : Covers root5Node55Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root5Node55Domains0 root5Node55Domains1 f hf root5Node55Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node55Domains1 root5Node55Domains2 f h1 root5Node55Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node55Domains2 (.output 27)
    root5Node55Leaf_checked f h2
theorem root5Node54_cover : Covers root5Node54Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node54Domains0 root5Node54Domains1 f hf root5Node54Step1_checked
  have hb : Covers root5Node54Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node54Domains1 root5Outputs 26
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node55_cover
    · exact root5Node56_cover
  exact hb f h1
theorem root5Node53_cover : Covers root5Node53Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node53Domains0 root5Node53Domains1 f hf root5Node53Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node53Domains1 (.output 26)
    root5Node53Leaf_checked f h1
theorem root5Node52_cover : Covers root5Node52Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node52Domains0 root5Node52Domains1 f hf root5Node52Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node52Domains1 (.output 25)
    root5Node52Leaf_checked f h1
theorem root5Node51_cover : Covers root5Node51Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root5Node51Domains0 root5Node51Domains1 f hf root5Node51Step1_checked
  have hb : Covers root5Node51Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node51Domains1 root5Outputs 52
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node52_cover
    · exact root5Node53_cover
  exact hb f h1
theorem root5Node50_cover : Covers root5Node50Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root5Node50Domains0 root5Node50Domains1 f hf root5Node50Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node50Domains1 root5Node50Domains2 f h1 root5Node50Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node50Domains2 (.output 24)
    root5Node50Leaf_checked f h2
theorem root5Node49_cover : Covers root5Node49Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node49Domains0 root5Node49Domains1 f hf root5Node49Step1_checked
  have hb : Covers root5Node49Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node49Domains1 root5Outputs 26
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node50_cover
    · exact root5Node51_cover
  exact hb f h1
theorem root5Node48_cover : Covers root5Node48Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root5Node48Domains0 root5Node48Domains1 f hf root5Node48Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root5Node48Domains1 root5Node48Domains2 f h1 root5Node48Step2_checked
  have h3 := solution_checkReplacement constraints table35 table35_member
    root5Node48Domains2 root5Node48Domains3 f h2 root5Node48Step3_checked
  have hb : Covers root5Node48Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node48Domains3 root5Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node49_cover
    · exact root5Node54_cover
  exact hb f h3
theorem root5Node47_cover : Covers root5Node47Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node47Domains0 (.output 23)
    root5Node47Leaf_checked f hf
theorem root5Node46_cover : Covers root5Node46Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node46Domains0 (.output 22)
    root5Node46Leaf_checked f hf
theorem root5Node45_cover : Covers root5Node45Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root5Node45Domains0 root5Node45Domains1 f hf root5Node45Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node45Domains1 root5Node45Domains2 f h1 root5Node45Step2_checked
  have hb : Covers root5Node45Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node45Domains2 root5Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node46_cover
    · exact root5Node47_cover
  exact hb f h2
theorem root5Node44_cover : Covers root5Node44Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node44Domains0 root5Node44Domains1 f hf root5Node44Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node44Domains1 (.output 21)
    root5Node44Leaf_checked f h1
theorem root5Node43_cover : Covers root5Node43Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node43Domains0 root5Node43Domains1 f hf root5Node43Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node43Domains1 (.output 20)
    root5Node43Leaf_checked f h1
theorem root5Node42_cover : Covers root5Node42Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root5Node42Domains0 root5Node42Domains1 f hf root5Node42Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root5Node42Domains1 root5Node42Domains2 f h1 root5Node42Step2_checked
  have hb : Covers root5Node42Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node42Domains2 root5Outputs 52
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node43_cover
    · exact root5Node44_cover
  exact hb f h2
theorem root5Node41_cover : Covers root5Node41Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root5Node41Domains0 root5Node41Domains1 f hf root5Node41Step1_checked
  have hb : Covers root5Node41Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node41Domains1 root5Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node42_cover
    · exact root5Node45_cover
  exact hb f h1
theorem root5Node40_cover : Covers root5Node40Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node40Domains0 (.output 19)
    root5Node40Leaf_checked f hf
theorem root5Node39_cover : Covers root5Node39Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node39Domains0 (.output 18)
    root5Node39Leaf_checked f hf
theorem root5Node38_cover : Covers root5Node38Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root5Node38Domains0 root5Node38Domains1 f hf root5Node38Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node38Domains1 root5Node38Domains2 f h1 root5Node38Step2_checked
  have hb : Covers root5Node38Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node38Domains2 root5Outputs 26
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node39_cover
    · exact root5Node40_cover
  exact hb f h2
theorem root5Node37_cover : Covers root5Node37Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root5Node37Domains0 root5Node37Domains1 f hf root5Node37Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root5Node37Domains1 root5Node37Domains2 f h1 root5Node37Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root5Node37Domains2 root5Node37Domains3 f h2 root5Node37Step3_checked
  have hb : Covers root5Node37Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node37Domains3 root5Outputs 27
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node38_cover
    · exact root5Node41_cover
  exact hb f h3
theorem root5Node36_cover : Covers root5Node36Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root5Node36Domains0 root5Node36Domains1 f hf root5Node36Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node36Domains1 root5Node36Domains2 f h1 root5Node36Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node36Domains2 (.output 17)
    root5Node36Leaf_checked f h2
theorem root5Node35_cover : Covers root5Node35Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node35Domains0 root5Node35Domains1 f hf root5Node35Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node35Domains1 (.output 16)
    root5Node35Leaf_checked f h1
theorem root5Node34_cover : Covers root5Node34Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node34Domains0 root5Node34Domains1 f hf root5Node34Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node34Domains1 (.output 15)
    root5Node34Leaf_checked f h1
theorem root5Node33_cover : Covers root5Node33Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root5Node33Domains0 root5Node33Domains1 f hf root5Node33Step1_checked
  have hb : Covers root5Node33Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node33Domains1 root5Outputs 52
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node34_cover
    · exact root5Node35_cover
  exact hb f h1
theorem root5Node32_cover : Covers root5Node32Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root5Node32Domains0 root5Node32Domains1 f hf root5Node32Step1_checked
  have hb : Covers root5Node32Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node32Domains1 root5Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node33_cover
    · exact root5Node36_cover
  exact hb f h1
theorem root5Node31_cover : Covers root5Node31Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root5Node31Domains0 root5Node31Domains1 f hf root5Node31Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node31Domains1 root5Node31Domains2 f h1 root5Node31Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node31Domains2 (.output 14)
    root5Node31Leaf_checked f h2
theorem root5Node30_cover : Covers root5Node30Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root5Node30Domains0 root5Node30Domains1 f hf root5Node30Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root5Node30Domains1 root5Node30Domains2 f h1 root5Node30Step2_checked
  have hb : Covers root5Node30Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node30Domains2 root5Outputs 26
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node31_cover
    · exact root5Node32_cover
  exact hb f h2
theorem root5Node29_cover : Covers root5Node29Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node29Domains0 root5Node29Domains1 f hf root5Node29Step1_checked
  have hb : Covers root5Node29Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node29Domains1 root5Outputs 5
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node30_cover
    · exact root5Node37_cover
  exact hb f h1
theorem root5Node28_cover : Covers root5Node28Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node28Domains0 (.output 13)
    root5Node28Leaf_checked f hf
theorem root5Node27_cover : Covers root5Node27Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node27Domains0 (.output 12)
    root5Node27Leaf_checked f hf
theorem root5Node26_cover : Covers root5Node26Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root5Node26Domains0 root5Node26Domains1 f hf root5Node26Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node26Domains1 root5Node26Domains2 f h1 root5Node26Step2_checked
  have hb : Covers root5Node26Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node26Domains2 root5Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node27_cover
    · exact root5Node28_cover
  exact hb f h2
theorem root5Node25_cover : Covers root5Node25Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node25Domains0 root5Node25Domains1 f hf root5Node25Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node25Domains1 (.output 11)
    root5Node25Leaf_checked f h1
theorem root5Node24_cover : Covers root5Node24Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root5Node24Domains0 root5Node24Domains1 f hf root5Node24Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node24Domains1 (.output 10)
    root5Node24Leaf_checked f h1
theorem root5Node23_cover : Covers root5Node23Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root5Node23Domains0 root5Node23Domains1 f hf root5Node23Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root5Node23Domains1 root5Node23Domains2 f h1 root5Node23Step2_checked
  have hb : Covers root5Node23Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node23Domains2 root5Outputs 52
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node24_cover
    · exact root5Node25_cover
  exact hb f h2
theorem root5Node22_cover : Covers root5Node22Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root5Node22Domains0 root5Node22Domains1 f hf root5Node22Step1_checked
  have hb : Covers root5Node22Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node22Domains1 root5Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node23_cover
    · exact root5Node26_cover
  exact hb f h1
theorem root5Node21_cover : Covers root5Node21Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root5Node21Domains0 root5Node21Domains1 f hf root5Node21Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root5Node21Domains1 root5Node21Domains2 f h1 root5Node21Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node21Domains2 (.output 9)
    root5Node21Leaf_checked f h2
theorem root5Node20_cover : Covers root5Node20Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root5Node20Domains0 root5Node20Domains1 f hf root5Node20Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root5Node20Domains1 root5Node20Domains2 f h1 root5Node20Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root5Node20Domains2 root5Node20Domains3 f h2 root5Node20Step3_checked
  have hb : Covers root5Node20Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node20Domains3 root5Outputs 26
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node21_cover
    · exact root5Node22_cover
  exact hb f h3
theorem root5Node19_cover : Covers root5Node19Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node19Domains0 root5Node19Domains1 f hf root5Node19Step1_checked
  have h2 := solution_checkReplacement constraints table10 table10_member
    root5Node19Domains1 root5Node19Domains2 f h1 root5Node19Step2_checked
  have hb : Covers root5Node19Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node19Domains2 root5Outputs 3
    intro s hs
    change s ∈ [(0,0),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node20_cover
    · exact root5Node29_cover
  exact hb f h2
theorem root5Node18_cover : Covers root5Node18Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node18Domains0 root5Node18Domains1 f hf root5Node18Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node18Domains1 (.output 8)
    root5Node18Leaf_checked f h1
theorem root5Node17_cover : Covers root5Node17Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node17Domains0 root5Node17Domains1 f hf root5Node17Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node17Domains1 (.output 7)
    root5Node17Leaf_checked f h1
theorem root5Node16_cover : Covers root5Node16Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root5Node16Domains0 root5Node16Domains1 f hf root5Node16Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root5Node16Domains1 root5Node16Domains2 f h1 root5Node16Step2_checked
  have h3 := solution_checkReplacement constraints table16 table16_member
    root5Node16Domains2 root5Node16Domains3 f h2 root5Node16Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root5Node16Domains3 root5Node16Domains4 f h3 root5Node16Step4_checked
  have hb : Covers root5Node16Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node16Domains4 root5Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node17_cover
    · exact root5Node18_cover
  exact hb f h4
theorem root5Node15_cover : Covers root5Node15Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root5Node15Domains0 root5Node15Domains1 f hf root5Node15Step1_checked
  have hb : Covers root5Node15Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node15Domains1 root5Outputs 0
    intro s hs
    change s ∈ [(1,5),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node16_cover
    · exact root5Node19_cover
  exact hb f h1
theorem root5Node14_cover : Covers root5Node14Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root5Node14Domains0 root5Node14Domains1 f hf root5Node14Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root5Node14Domains1 root5Node14Domains2 f h1 root5Node14Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root5Node14Domains2 root5Node14Domains3 f h2 root5Node14Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root5Node14Domains3 root5Node14Domains4 f h3 root5Node14Step4_checked
  have hb : Covers root5Node14Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node14Domains4 root5Outputs 6
    intro s hs
    change s ∈ [(7,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node15_cover
    · exact root5Node48_cover
  exact hb f h4
theorem root5Node13_cover : Covers root5Node13Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root5Node13Domains0 root5Node13Domains1 f hf root5Node13Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node13Domains1 (.output 6)
    root5Node13Leaf_checked f h1
theorem root5Node12_cover : Covers root5Node12Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root5Node12Domains0 root5Node12Domains1 f hf root5Node12Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node12Domains1 (.output 5)
    root5Node12Leaf_checked f h1
theorem root5Node11_cover : Covers root5Node11Domains0 constraints root5Outputs := by
  intro f hf
  have hb : Covers root5Node11Domains0 constraints root5Outputs := by
    apply covers_of_branches root5Node11Domains0 root5Outputs 4
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node12_cover
    · exact root5Node13_cover
  exact hb f hf
theorem root5Node10_cover : Covers root5Node10Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root5Node10Domains0 root5Node10Domains1 f hf root5Node10Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root5Node10Domains1 root5Node10Domains2 f h1 root5Node10Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node10Domains2 (.output 4)
    root5Node10Leaf_checked f h2
theorem root5Node9_cover : Covers root5Node9Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root5Node9Domains0 root5Node9Domains1 f hf root5Node9Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root5Node9Domains1 root5Node9Domains2 f h1 root5Node9Step2_checked
  have hb : Covers root5Node9Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node9Domains2 root5Outputs 0
    intro s hs
    change s ∈ [(1,0),(6,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node10_cover
    · exact root5Node11_cover
  exact hb f h2
theorem root5Node8_cover : Covers root5Node8Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node8Domains0 root5Node8Domains1 f hf root5Node8Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node8Domains1 (.output 3)
    root5Node8Leaf_checked f h1
theorem root5Node7_cover : Covers root5Node7Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node7Domains0 root5Node7Domains1 f hf root5Node7Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node7Domains1 (.output 2)
    root5Node7Leaf_checked f h1
theorem root5Node6_cover : Covers root5Node6Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root5Node6Domains0 root5Node6Domains1 f hf root5Node6Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root5Node6Domains1 root5Node6Domains2 f h1 root5Node6Step2_checked
  have hb : Covers root5Node6Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node6Domains2 root5Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node7_cover
    · exact root5Node8_cover
  exact hb f h2
theorem root5Node5_cover : Covers root5Node5Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root5Node5Domains0 root5Node5Domains1 f hf root5Node5Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node5Domains1 (.output 1)
    root5Node5Leaf_checked f h1
theorem root5Node4_cover : Covers root5Node4Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root5Node4Domains0 root5Node4Domains1 f hf root5Node4Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node4Domains1 (.output 0)
    root5Node4Leaf_checked f h1
theorem root5Node3_cover : Covers root5Node3Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root5Node3Domains0 root5Node3Domains1 f hf root5Node3Step1_checked
  have hb : Covers root5Node3Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node3Domains1 root5Outputs 5
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node4_cover
    · exact root5Node5_cover
  exact hb f h1
theorem root5Node2_cover : Covers root5Node2Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root5Node2Domains0 root5Node2Domains1 f hf root5Node2Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root5Node2Domains1 root5Node2Domains2 f h1 root5Node2Step2_checked
  have hb : Covers root5Node2Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node2Domains2 root5Outputs 6
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node3_cover
    · exact root5Node6_cover
  exact hb f h2
theorem root5Node1_cover : Covers root5Node1Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root5Node1Domains0 root5Node1Domains1 f hf root5Node1Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root5Node1Domains1 root5Node1Domains2 f h1 root5Node1Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root5Node1Domains2 root5Node1Domains3 f h2 root5Node1Step3_checked
  have h4 := solution_checkReplacement constraints table36 table36_member
    root5Node1Domains3 root5Node1Domains4 f h3 root5Node1Step4_checked
  have hb : Covers root5Node1Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node1Domains4 root5Outputs 1
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node2_cover
    · exact root5Node9_cover
  exact hb f h4
theorem root5Node0_cover : Covers root5Node0Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root5Node0Domains0 root5Node0Domains1 f hf root5Node0Step1_checked
  have h2 := solution_checkReplacement constraints table20 table20_member
    root5Node0Domains1 root5Node0Domains2 f h1 root5Node0Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root5Node0Domains2 root5Node0Domains3 f h2 root5Node0Step3_checked
  have h4 := solution_checkReplacement constraints table35 table35_member
    root5Node0Domains3 root5Node0Domains4 f h3 root5Node0Step4_checked
  have hb : Covers root5Node0Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node0Domains4 root5Outputs 28
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node1_cover
    · exact root5Node14_cover
  exact hb f h4
theorem root5_table_cover : Covers (domains (5,0)) constraints root5Outputs := root5Node0_cover
theorem root5Family_count : root5Family.length = 30 := rfl
#print axioms root5_table_cover
end SpectreFinite.HexSearch.RadiusFour
