module

public import SpectreFinite.RadiusFourRoot1Part23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root1Node64_cover : Covers root1Node64Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node64Domains0 root1Node64Domains1 f hf root1Node64Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node64Domains1 (.output 32)
    root1Node64Leaf_checked f h1
theorem root1Node63_cover : Covers root1Node63Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node63Domains0 root1Node63Domains1 f hf root1Node63Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node63Domains1 (.output 31)
    root1Node63Leaf_checked f h1
theorem root1Node62_cover : Covers root1Node62Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node62Domains0 root1Node62Domains1 f hf root1Node62Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node62Domains1 (.output 30)
    root1Node62Leaf_checked f h1
theorem root1Node61_cover : Covers root1Node61Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node61Domains0 root1Node61Domains1 f hf root1Node61Step1_checked
  have hb : Covers root1Node61Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node61Domains1 root1Outputs 50
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node62_cover
    · exact root1Node63_cover
  exact hb f h1
theorem root1Node60_cover : Covers root1Node60Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node60Domains0 root1Node60Domains1 f hf root1Node60Step1_checked
  have hb : Covers root1Node60Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node60Domains1 root1Outputs 37
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node61_cover
    · exact root1Node64_cover
  exact hb f h1
theorem root1Node59_cover : Covers root1Node59Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node59Domains0 root1Node59Domains1 f hf root1Node59Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root1Node59Domains1 root1Node59Domains2 f h1 root1Node59Step2_checked
  have h3 := solution_checkReplacement constraints table4 table4_member
    root1Node59Domains2 root1Node59Domains3 f h2 root1Node59Step3_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node59Domains3 (.output 29)
    root1Node59Leaf_checked f h3
theorem root1Node58_cover : Covers root1Node58Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root1Node58Domains0 root1Node58Domains1 f hf root1Node58Step1_checked
  have hb : Covers root1Node58Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node58Domains1 root1Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node59_cover
    · exact root1Node60_cover
  exact hb f h1
theorem root1Node57_cover : Covers root1Node57Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root1Node57Domains0 root1Node57Domains1 f hf root1Node57Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root1Node57Domains1 root1Node57Domains2 f h1 root1Node57Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node57Domains2 (.output 28)
    root1Node57Leaf_checked f h2
theorem root1Node56_cover : Covers root1Node56Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table20 table20_member
    root1Node56Domains0 root1Node56Domains1 f hf root1Node56Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root1Node56Domains1 root1Node56Domains2 f h1 root1Node56Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root1Node56Domains2 root1Node56Domains3 f h2 root1Node56Step3_checked
  have h4 := solution_checkReplacement constraints table35 table35_member
    root1Node56Domains3 root1Node56Domains4 f h3 root1Node56Step4_checked
  have hb : Covers root1Node56Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node56Domains4 root1Outputs 10
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node57_cover
    · exact root1Node58_cover
  exact hb f h4
theorem root1Node55_cover : Covers root1Node55Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root1Node55Domains0 root1Node55Domains1 f hf root1Node55Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root1Node55Domains1 root1Node55Domains2 f h1 root1Node55Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node55Domains2 (.output 27)
    root1Node55Leaf_checked f h2
theorem root1Node54_cover : Covers root1Node54Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root1Node54Domains0 root1Node54Domains1 f hf root1Node54Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root1Node54Domains1 root1Node54Domains2 f h1 root1Node54Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node54Domains2 (.output 26)
    root1Node54Leaf_checked f h2
theorem root1Node53_cover : Covers root1Node53Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root1Node53Domains0 root1Node53Domains1 f hf root1Node53Step1_checked
  have hb : Covers root1Node53Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node53Domains1 root1Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node54_cover
    · exact root1Node55_cover
  exact hb f h1
theorem root1Node52_cover : Covers root1Node52Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root1Node52Domains0 root1Node52Domains1 f hf root1Node52Step1_checked
  have h2 := solution_checkReplacement constraints table35 table35_member
    root1Node52Domains1 root1Node52Domains2 f h1 root1Node52Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root1Node52Domains2 root1Node52Domains3 f h2 root1Node52Step3_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node52Domains3 (.output 25)
    root1Node52Leaf_checked f h3
theorem root1Node51_cover : Covers root1Node51Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root1Node51Domains0 root1Node51Domains1 f hf root1Node51Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root1Node51Domains1 root1Node51Domains2 f h1 root1Node51Step2_checked
  have h3 := solution_checkReplacement constraints table11 table11_member
    root1Node51Domains2 root1Node51Domains3 f h2 root1Node51Step3_checked
  have h4 := solution_checkReplacement constraints table16 table16_member
    root1Node51Domains3 root1Node51Domains4 f h3 root1Node51Step4_checked
  have hb : Covers root1Node51Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node51Domains4 root1Outputs 5
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node52_cover
    · exact root1Node53_cover
  exact hb f h4
theorem root1Node50_cover : Covers root1Node50Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node50Domains0 root1Node50Domains1 f hf root1Node50Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node50Domains1 (.output 24)
    root1Node50Leaf_checked f h1
theorem root1Node49_cover : Covers root1Node49Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node49Domains0 root1Node49Domains1 f hf root1Node49Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node49Domains1 (.output 23)
    root1Node49Leaf_checked f h1
theorem root1Node48_cover : Covers root1Node48Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node48Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node48Domains0 root1Outputs 37
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node49_cover
    · exact root1Node50_cover
  exact hb f hf
theorem root1Node47_cover : Covers root1Node47Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root1Node47Domains0 root1Node47Domains1 f hf root1Node47Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root1Node47Domains1 root1Node47Domains2 f h1 root1Node47Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node47Domains2 (.output 22)
    root1Node47Leaf_checked f h2
theorem root1Node46_cover : Covers root1Node46Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node46Domains0 root1Node46Domains1 f hf root1Node46Step1_checked
  have hb : Covers root1Node46Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node46Domains1 root1Outputs 26
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node47_cover
    · exact root1Node48_cover
  exact hb f h1
theorem root1Node45_cover : Covers root1Node45Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node45Domains0 root1Node45Domains1 f hf root1Node45Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root1Node45Domains1 root1Node45Domains2 f h1 root1Node45Step2_checked
  have h3 := solution_checkReplacement constraints table4 table4_member
    root1Node45Domains2 root1Node45Domains3 f h2 root1Node45Step3_checked
  have h4 := solution_checkReplacement constraints table35 table35_member
    root1Node45Domains3 root1Node45Domains4 f h3 root1Node45Step4_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node45Domains4 (.output 21)
    root1Node45Leaf_checked f h4
theorem root1Node44_cover : Covers root1Node44Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root1Node44Domains0 root1Node44Domains1 f hf root1Node44Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root1Node44Domains1 root1Node44Domains2 f h1 root1Node44Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root1Node44Domains2 root1Node44Domains3 f h2 root1Node44Step3_checked
  have h4 := solution_checkReplacement constraints table5 table5_member
    root1Node44Domains3 root1Node44Domains4 f h3 root1Node44Step4_checked
  have h5 := solution_checkReplacement constraints table39 table39_member
    root1Node44Domains4 root1Node44Domains5 f h4 root1Node44Step5_checked
  have hb : Covers root1Node44Domains5 constraints root1Outputs := by
    apply covers_of_branches root1Node44Domains5 root1Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node45_cover
    · exact root1Node46_cover
  exact hb f h5
theorem root1Node43_cover : Covers root1Node43Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root1Node43Domains0 root1Node43Domains1 f hf root1Node43Step1_checked
  have h2 := solution_checkReplacement constraints table29 table29_member
    root1Node43Domains1 root1Node43Domains2 f h1 root1Node43Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root1Node43Domains2 root1Node43Domains3 f h2 root1Node43Step3_checked
  have h4 := solution_checkReplacement constraints table10 table10_member
    root1Node43Domains3 root1Node43Domains4 f h3 root1Node43Step4_checked
  have hb : Covers root1Node43Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node43Domains4 root1Outputs 3
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node44_cover
    · exact root1Node51_cover
  exact hb f h4
theorem root1Node42_cover : Covers root1Node42Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table20 table20_member
    root1Node42Domains0 root1Node42Domains1 f hf root1Node42Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root1Node42Domains1 root1Node42Domains2 f h1 root1Node42Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root1Node42Domains2 root1Node42Domains3 f h2 root1Node42Step3_checked
  have h4 := solution_checkReplacement constraints table26 table26_member
    root1Node42Domains3 root1Node42Domains4 f h3 root1Node42Step4_checked
  have hb : Covers root1Node42Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node42Domains4 root1Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node43_cover
    · exact root1Node56_cover
  exact hb f h4
theorem root1Node41_cover : Covers root1Node41Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node41Domains0 root1Node41Domains1 f hf root1Node41Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root1Node41Domains1 root1Node41Domains2 f h1 root1Node41Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node41Domains2 (.output 20)
    root1Node41Leaf_checked f h2
theorem root1Node40_cover : Covers root1Node40Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node40Domains0 root1Node40Domains1 f hf root1Node40Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node40Domains1 (.output 19)
    root1Node40Leaf_checked f h1
theorem root1Node39_cover : Covers root1Node39Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node39Domains0 root1Node39Domains1 f hf root1Node39Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node39Domains1 (.output 18)
    root1Node39Leaf_checked f h1
theorem root1Node38_cover : Covers root1Node38Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node38Domains0 root1Node38Domains1 f hf root1Node38Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node38Domains1 (.output 17)
    root1Node38Leaf_checked f h1
theorem root1Node37_cover : Covers root1Node37Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node37Domains0 root1Node37Domains1 f hf root1Node37Step1_checked
  have hb : Covers root1Node37Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node37Domains1 root1Outputs 50
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node38_cover
    · exact root1Node39_cover
  exact hb f h1
theorem root1Node36_cover : Covers root1Node36Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node36Domains0 root1Node36Domains1 f hf root1Node36Step1_checked
  have hb : Covers root1Node36Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node36Domains1 root1Outputs 37
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node37_cover
    · exact root1Node40_cover
  exact hb f h1
theorem root1Node35_cover : Covers root1Node35Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node35Domains0 root1Node35Domains1 f hf root1Node35Step1_checked
  have hb : Covers root1Node35Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node35Domains1 root1Outputs 17
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node36_cover
    · exact root1Node41_cover
  exact hb f h1
theorem root1Node34_cover : Covers root1Node34Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node34Domains0 root1Node34Domains1 f hf root1Node34Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root1Node34Domains1 root1Node34Domains2 f h1 root1Node34Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node34Domains2 (.output 16)
    root1Node34Leaf_checked f h2
theorem root1Node33_cover : Covers root1Node33Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root1Node33Domains0 root1Node33Domains1 f hf root1Node33Step1_checked
  have h2 := solution_checkReplacement constraints table35 table35_member
    root1Node33Domains1 root1Node33Domains2 f h1 root1Node33Step2_checked
  have hb : Covers root1Node33Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node33Domains2 root1Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node34_cover
    · exact root1Node35_cover
  exact hb f h2
theorem root1Node32_cover : Covers root1Node32Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node32Domains0 root1Node32Domains1 f hf root1Node32Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root1Node32Domains1 root1Node32Domains2 f h1 root1Node32Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node32Domains2 (.output 15)
    root1Node32Leaf_checked f h2
theorem root1Node31_cover : Covers root1Node31Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node31Domains0 (.output 14)
    root1Node31Leaf_checked f hf
theorem root1Node30_cover : Covers root1Node30Domains0 constraints root1Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root1Outputs root1Node30Domains0 (.output 13)
    root1Node30Leaf_checked f hf
theorem root1Node29_cover : Covers root1Node29Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node29Domains0 root1Node29Domains1 f hf root1Node29Step1_checked
  have hb : Covers root1Node29Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node29Domains1 root1Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node30_cover
    · exact root1Node31_cover
  exact hb f h1
theorem root1Node28_cover : Covers root1Node28Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node28Domains0 root1Node28Domains1 f hf root1Node28Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node28Domains1 (.output 12)
    root1Node28Leaf_checked f h1
theorem root1Node27_cover : Covers root1Node27Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node27Domains0 root1Node27Domains1 f hf root1Node27Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node27Domains1 (.output 11)
    root1Node27Leaf_checked f h1
theorem root1Node26_cover : Covers root1Node26Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root1Node26Domains0 root1Node26Domains1 f hf root1Node26Step1_checked
  have hb : Covers root1Node26Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node26Domains1 root1Outputs 50
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node27_cover
    · exact root1Node28_cover
  exact hb f h1
theorem root1Node25_cover : Covers root1Node25Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node25Domains0 root1Node25Domains1 f hf root1Node25Step1_checked
  have hb : Covers root1Node25Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node25Domains1 root1Outputs 37
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node26_cover
    · exact root1Node29_cover
  exact hb f h1
theorem root1Node24_cover : Covers root1Node24Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node24Domains0 root1Node24Domains1 f hf root1Node24Step1_checked
  have hb : Covers root1Node24Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node24Domains1 root1Outputs 17
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node25_cover
    · exact root1Node32_cover
  exact hb f h1
theorem root1Node23_cover : Covers root1Node23Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node23Domains0 root1Node23Domains1 f hf root1Node23Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root1Node23Domains1 root1Node23Domains2 f h1 root1Node23Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node23Domains2 (.output 10)
    root1Node23Leaf_checked f h2
theorem root1Node22_cover : Covers root1Node22Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root1Node22Domains0 root1Node22Domains1 f hf root1Node22Step1_checked
  have hb : Covers root1Node22Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node22Domains1 root1Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node23_cover
    · exact root1Node24_cover
  exact hb f h1
theorem root1Node21_cover : Covers root1Node21Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root1Node21Domains0 root1Node21Domains1 f hf root1Node21Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root1Node21Domains1 root1Node21Domains2 f h1 root1Node21Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root1Node21Domains2 root1Node21Domains3 f h2 root1Node21Step3_checked
  have hb : Covers root1Node21Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node21Domains3 root1Outputs 0
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node22_cover
    · exact root1Node33_cover
  exact hb f h3
theorem root1Node20_cover : Covers root1Node20Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root1Node20Domains0 root1Node20Domains1 f hf root1Node20Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root1Node20Domains1 root1Node20Domains2 f h1 root1Node20Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node20Domains2 (.output 9)
    root1Node20Leaf_checked f h2
theorem root1Node19_cover : Covers root1Node19Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node19Domains0 root1Node19Domains1 f hf root1Node19Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node19Domains1 (.output 8)
    root1Node19Leaf_checked f h1
theorem root1Node18_cover : Covers root1Node18Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node18Domains0 root1Node18Domains1 f hf root1Node18Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node18Domains1 (.output 7)
    root1Node18Leaf_checked f h1
theorem root1Node17_cover : Covers root1Node17Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node17Domains0 root1Node17Domains1 f hf root1Node17Step1_checked
  have hb : Covers root1Node17Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node17Domains1 root1Outputs 58
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node18_cover
    · exact root1Node19_cover
  exact hb f h1
theorem root1Node16_cover : Covers root1Node16Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node16Domains0 root1Node16Domains1 f hf root1Node16Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node16Domains1 (.output 6)
    root1Node16Leaf_checked f h1
theorem root1Node15_cover : Covers root1Node15Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node15Domains0 root1Node15Domains1 f hf root1Node15Step1_checked
  have hb : Covers root1Node15Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node15Domains1 root1Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node16_cover
    · exact root1Node17_cover
  exact hb f h1
theorem root1Node14_cover : Covers root1Node14Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node14Domains0 root1Node14Domains1 f hf root1Node14Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root1Node14Domains1 root1Node14Domains2 f h1 root1Node14Step2_checked
  have hb : Covers root1Node14Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node14Domains2 root1Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node15_cover
    · exact root1Node20_cover
  exact hb f h2
theorem root1Node13_cover : Covers root1Node13Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node13Domains0 root1Node13Domains1 f hf root1Node13Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root1Node13Domains1 root1Node13Domains2 f h1 root1Node13Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node13Domains2 (.output 5)
    root1Node13Leaf_checked f h2
theorem root1Node12_cover : Covers root1Node12Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root1Node12Domains0 root1Node12Domains1 f hf root1Node12Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root1Node12Domains1 root1Node12Domains2 f h1 root1Node12Step2_checked
  have h3 := solution_checkReplacement constraints table35 table35_member
    root1Node12Domains2 root1Node12Domains3 f h2 root1Node12Step3_checked
  have hb : Covers root1Node12Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node12Domains3 root1Outputs 17
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node13_cover
    · exact root1Node14_cover
  exact hb f h3
theorem root1Node11_cover : Covers root1Node11Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root1Node11Domains0 root1Node11Domains1 f hf root1Node11Step1_checked
  have hb : Covers root1Node11Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node11Domains1 root1Outputs 1
    intro s hs
    change s ∈ [(0,0),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node12_cover
    · exact root1Node21_cover
  exact hb f h1
theorem root1Node10_cover : Covers root1Node10Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root1Node10Domains0 root1Node10Domains1 f hf root1Node10Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root1Node10Domains1 root1Node10Domains2 f h1 root1Node10Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node10Domains2 (.output 4)
    root1Node10Leaf_checked f h2
theorem root1Node9_cover : Covers root1Node9Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node9Domains0 root1Node9Domains1 f hf root1Node9Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node9Domains1 (.output 3)
    root1Node9Leaf_checked f h1
theorem root1Node8_cover : Covers root1Node8Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node8Domains0 root1Node8Domains1 f hf root1Node8Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node8Domains1 (.output 2)
    root1Node8Leaf_checked f h1
theorem root1Node7_cover : Covers root1Node7Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node7Domains0 root1Node7Domains1 f hf root1Node7Step1_checked
  have hb : Covers root1Node7Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node7Domains1 root1Outputs 58
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node8_cover
    · exact root1Node9_cover
  exact hb f h1
theorem root1Node6_cover : Covers root1Node6Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root1Node6Domains0 root1Node6Domains1 f hf root1Node6Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node6Domains1 (.output 1)
    root1Node6Leaf_checked f h1
theorem root1Node5_cover : Covers root1Node5Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root1Node5Domains0 root1Node5Domains1 f hf root1Node5Step1_checked
  have hb : Covers root1Node5Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node5Domains1 root1Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node6_cover
    · exact root1Node7_cover
  exact hb f h1
theorem root1Node4_cover : Covers root1Node4Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node4Domains0 root1Node4Domains1 f hf root1Node4Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root1Node4Domains1 root1Node4Domains2 f h1 root1Node4Step2_checked
  have hb : Covers root1Node4Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node4Domains2 root1Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node5_cover
    · exact root1Node10_cover
  exact hb f h2
theorem root1Node3_cover : Covers root1Node3Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root1Node3Domains0 root1Node3Domains1 f hf root1Node3Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root1Node3Domains1 root1Node3Domains2 f h1 root1Node3Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node3Domains2 (.output 0)
    root1Node3Leaf_checked f h2
theorem root1Node2_cover : Covers root1Node2Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root1Node2Domains0 root1Node2Domains1 f hf root1Node2Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root1Node2Domains1 root1Node2Domains2 f h1 root1Node2Step2_checked
  have h3 := solution_checkReplacement constraints table35 table35_member
    root1Node2Domains2 root1Node2Domains3 f h2 root1Node2Step3_checked
  have hb : Covers root1Node2Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node2Domains3 root1Outputs 17
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node3_cover
    · exact root1Node4_cover
  exact hb f h3
theorem root1Node1_cover : Covers root1Node1Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root1Node1Domains0 root1Node1Domains1 f hf root1Node1Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root1Node1Domains1 root1Node1Domains2 f h1 root1Node1Step2_checked
  have h3 := solution_checkReplacement constraints table37 table37_member
    root1Node1Domains2 root1Node1Domains3 f h2 root1Node1Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root1Node1Domains3 root1Node1Domains4 f h3 root1Node1Step4_checked
  have h5 := solution_checkReplacement constraints table39 table39_member
    root1Node1Domains4 root1Node1Domains5 f h4 root1Node1Step5_checked
  have hb : Covers root1Node1Domains5 constraints root1Outputs := by
    apply covers_of_branches root1Node1Domains5 root1Outputs 2
    intro s hs
    change s ∈ [(1,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node2_cover
    · exact root1Node11_cover
  exact hb f h5
theorem root1Node0_cover : Covers root1Node0Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root1Node0Domains0 root1Node0Domains1 f hf root1Node0Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root1Node0Domains1 root1Node0Domains2 f h1 root1Node0Step2_checked
  have h3 := solution_checkReplacement constraints table40 table40_member
    root1Node0Domains2 root1Node0Domains3 f h2 root1Node0Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root1Node0Domains3 root1Node0Domains4 f h3 root1Node0Step4_checked
  have hb : Covers root1Node0Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node0Domains4 root1Outputs 8
    intro s hs
    change s ∈ [(4,1),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node1_cover
    · exact root1Node42_cover
  exact hb f h4
theorem root1_table_cover : Covers (domains (1,0)) constraints root1Outputs := root1Node0_cover
theorem root1Family_count : root1Family.length = 33 := rfl
#print axioms root1_table_cover
end SpectreFinite.HexSearch.RadiusFour
