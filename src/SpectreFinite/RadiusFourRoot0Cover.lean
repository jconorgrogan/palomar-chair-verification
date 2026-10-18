module

public import SpectreFinite.RadiusFourRoot0Part23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root0Node70_cover : Covers root0Node70Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root0Node70Domains0 root0Node70Domains1 f hf root0Node70Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node70Domains1 (.output 35)
    root0Node70Leaf_checked f h1
theorem root0Node69_cover : Covers root0Node69Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root0Node69Domains0 root0Node69Domains1 f hf root0Node69Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node69Domains1 (.output 34)
    root0Node69Leaf_checked f h1
theorem root0Node68_cover : Covers root0Node68Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node68Domains0 root0Node68Domains1 f hf root0Node68Step1_checked
  have hb : Covers root0Node68Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node68Domains1 root0Outputs 45
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node69_cover
    · exact root0Node70_cover
  exact hb f h1
theorem root0Node67_cover : Covers root0Node67Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node67Domains0 root0Node67Domains1 f hf root0Node67Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node67Domains1 root0Node67Domains2 f h1 root0Node67Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node67Domains2 (.output 33)
    root0Node67Leaf_checked f h2
theorem root0Node66_cover : Covers root0Node66Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node66Domains0 root0Node66Domains1 f hf root0Node66Step1_checked
  have hb : Covers root0Node66Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node66Domains1 root0Outputs 18
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node67_cover
    · exact root0Node68_cover
  exact hb f h1
theorem root0Node65_cover : Covers root0Node65Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root0Node65Domains0 root0Node65Domains1 f hf root0Node65Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node65Domains1 (.output 32)
    root0Node65Leaf_checked f h1
theorem root0Node64_cover : Covers root0Node64Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root0Node64Domains0 root0Node64Domains1 f hf root0Node64Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node64Domains1 (.output 31)
    root0Node64Leaf_checked f h1
theorem root0Node63_cover : Covers root0Node63Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node63Domains0 root0Node63Domains1 f hf root0Node63Step1_checked
  have hb : Covers root0Node63Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node63Domains1 root0Outputs 45
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node64_cover
    · exact root0Node65_cover
  exact hb f h1
theorem root0Node62_cover : Covers root0Node62Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node62Domains0 root0Node62Domains1 f hf root0Node62Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node62Domains1 root0Node62Domains2 f h1 root0Node62Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node62Domains2 (.output 30)
    root0Node62Leaf_checked f h2
theorem root0Node61_cover : Covers root0Node61Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node61Domains0 root0Node61Domains1 f hf root0Node61Step1_checked
  have hb : Covers root0Node61Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node61Domains1 root0Outputs 18
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node62_cover
    · exact root0Node63_cover
  exact hb f h1
theorem root0Node60_cover : Covers root0Node60Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root0Node60Domains0 root0Node60Domains1 f hf root0Node60Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root0Node60Domains1 root0Node60Domains2 f h1 root0Node60Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root0Node60Domains2 root0Node60Domains3 f h2 root0Node60Step3_checked
  have hb : Covers root0Node60Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node60Domains3 root0Outputs 3
    intro s hs
    change s ∈ [(1,0),(3,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node61_cover
    · exact root0Node66_cover
  exact hb f h3
theorem root0Node59_cover : Covers root0Node59Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node59Domains0 root0Node59Domains1 f hf root0Node59Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node59Domains1 (.output 29)
    root0Node59Leaf_checked f h1
theorem root0Node58_cover : Covers root0Node58Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node58Domains0 root0Node58Domains1 f hf root0Node58Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node58Domains1 (.output 28)
    root0Node58Leaf_checked f h1
theorem root0Node57_cover : Covers root0Node57Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root0Node57Domains0 root0Node57Domains1 f hf root0Node57Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node57Domains1 root0Node57Domains2 f h1 root0Node57Step2_checked
  have h3 := solution_checkReplacement constraints table16 table16_member
    root0Node57Domains2 root0Node57Domains3 f h2 root0Node57Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root0Node57Domains3 root0Node57Domains4 f h3 root0Node57Step4_checked
  have hb : Covers root0Node57Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node57Domains4 root0Outputs 3
    intro s hs
    change s ∈ [(1,0),(3,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node58_cover
    · exact root0Node59_cover
  exact hb f h4
theorem root0Node56_cover : Covers root0Node56Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root0Node56Domains0 root0Node56Domains1 f hf root0Node56Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node56Domains1 (.output 27)
    root0Node56Leaf_checked f h1
theorem root0Node55_cover : Covers root0Node55Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root0Node55Domains0 root0Node55Domains1 f hf root0Node55Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node55Domains1 (.output 26)
    root0Node55Leaf_checked f h1
theorem root0Node54_cover : Covers root0Node54Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node54Domains0 root0Node54Domains1 f hf root0Node54Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root0Node54Domains1 root0Node54Domains2 f h1 root0Node54Step2_checked
  have hb : Covers root0Node54Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node54Domains2 root0Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node55_cover
    · exact root0Node56_cover
  exact hb f h2
theorem root0Node53_cover : Covers root0Node53Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root0Node53Domains0 root0Node53Domains1 f hf root0Node53Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root0Node53Domains1 root0Node53Domains2 f h1 root0Node53Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node53Domains2 (.output 25)
    root0Node53Leaf_checked f h2
theorem root0Node52_cover : Covers root0Node52Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root0Node52Domains0 root0Node52Domains1 f hf root0Node52Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root0Node52Domains1 root0Node52Domains2 f h1 root0Node52Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node52Domains2 (.output 24)
    root0Node52Leaf_checked f h2
theorem root0Node51_cover : Covers root0Node51Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node51Domains0 root0Node51Domains1 f hf root0Node51Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node51Domains1 root0Node51Domains2 f h1 root0Node51Step2_checked
  have hb : Covers root0Node51Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node51Domains2 root0Outputs 34
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node52_cover
    · exact root0Node53_cover
  exact hb f h2
theorem root0Node50_cover : Covers root0Node50Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node50Domains0 root0Node50Domains1 f hf root0Node50Step1_checked
  have hb : Covers root0Node50Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node50Domains1 root0Outputs 26
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node51_cover
    · exact root0Node54_cover
  exact hb f h1
theorem root0Node49_cover : Covers root0Node49Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node49Domains0 root0Node49Domains1 f hf root0Node49Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root0Node49Domains1 root0Node49Domains2 f h1 root0Node49Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node49Domains2 (.output 23)
    root0Node49Leaf_checked f h2
theorem root0Node48_cover : Covers root0Node48Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node48Domains0 root0Node48Domains1 f hf root0Node48Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root0Node48Domains1 root0Node48Domains2 f h1 root0Node48Step2_checked
  have hb : Covers root0Node48Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node48Domains2 root0Outputs 18
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node49_cover
    · exact root0Node50_cover
  exact hb f h2
theorem root0Node47_cover : Covers root0Node47Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root0Node47Domains0 root0Node47Domains1 f hf root0Node47Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node47Domains1 (.output 22)
    root0Node47Leaf_checked f h1
theorem root0Node46_cover : Covers root0Node46Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root0Node46Domains0 root0Node46Domains1 f hf root0Node46Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node46Domains1 (.output 21)
    root0Node46Leaf_checked f h1
theorem root0Node45_cover : Covers root0Node45Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node45Domains0 root0Node45Domains1 f hf root0Node45Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root0Node45Domains1 root0Node45Domains2 f h1 root0Node45Step2_checked
  have hb : Covers root0Node45Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node45Domains2 root0Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node46_cover
    · exact root0Node47_cover
  exact hb f h2
theorem root0Node44_cover : Covers root0Node44Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root0Node44Domains0 root0Node44Domains1 f hf root0Node44Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root0Node44Domains1 root0Node44Domains2 f h1 root0Node44Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node44Domains2 (.output 20)
    root0Node44Leaf_checked f h2
theorem root0Node43_cover : Covers root0Node43Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root0Node43Domains0 root0Node43Domains1 f hf root0Node43Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root0Node43Domains1 root0Node43Domains2 f h1 root0Node43Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node43Domains2 (.output 19)
    root0Node43Leaf_checked f h2
theorem root0Node42_cover : Covers root0Node42Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node42Domains0 root0Node42Domains1 f hf root0Node42Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node42Domains1 root0Node42Domains2 f h1 root0Node42Step2_checked
  have hb : Covers root0Node42Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node42Domains2 root0Outputs 34
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node43_cover
    · exact root0Node44_cover
  exact hb f h2
theorem root0Node41_cover : Covers root0Node41Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node41Domains0 root0Node41Domains1 f hf root0Node41Step1_checked
  have hb : Covers root0Node41Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node41Domains1 root0Outputs 26
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node42_cover
    · exact root0Node45_cover
  exact hb f h1
theorem root0Node40_cover : Covers root0Node40Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node40Domains0 root0Node40Domains1 f hf root0Node40Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root0Node40Domains1 root0Node40Domains2 f h1 root0Node40Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node40Domains2 (.output 18)
    root0Node40Leaf_checked f h2
theorem root0Node39_cover : Covers root0Node39Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node39Domains0 root0Node39Domains1 f hf root0Node39Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root0Node39Domains1 root0Node39Domains2 f h1 root0Node39Step2_checked
  have hb : Covers root0Node39Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node39Domains2 root0Outputs 18
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node40_cover
    · exact root0Node41_cover
  exact hb f h2
theorem root0Node38_cover : Covers root0Node38Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node38Domains0 root0Node38Domains1 f hf root0Node38Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root0Node38Domains1 root0Node38Domains2 f h1 root0Node38Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node38Domains2 (.output 17)
    root0Node38Leaf_checked f h2
theorem root0Node37_cover : Covers root0Node37Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root0Node37Domains0 root0Node37Domains1 f hf root0Node37Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node37Domains1 (.output 16)
    root0Node37Leaf_checked f h1
theorem root0Node36_cover : Covers root0Node36Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root0Node36Domains0 root0Node36Domains1 f hf root0Node36Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node36Domains1 (.output 15)
    root0Node36Leaf_checked f h1
theorem root0Node35_cover : Covers root0Node35Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root0Node35Domains0 root0Node35Domains1 f hf root0Node35Step1_checked
  have hb : Covers root0Node35Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node35Domains1 root0Outputs 45
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node36_cover
    · exact root0Node37_cover
  exact hb f h1
theorem root0Node34_cover : Covers root0Node34Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node34Domains0 (.output 14)
    root0Node34Leaf_checked f hf
theorem root0Node33_cover : Covers root0Node33Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node33Domains0 (.output 13)
    root0Node33Leaf_checked f hf
theorem root0Node32_cover : Covers root0Node32Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root0Node32Domains0 root0Node32Domains1 f hf root0Node32Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root0Node32Domains1 root0Node32Domains2 f h1 root0Node32Step2_checked
  have hb : Covers root0Node32Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node32Domains2 root0Outputs 49
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node33_cover
    · exact root0Node34_cover
  exact hb f h2
theorem root0Node31_cover : Covers root0Node31Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root0Node31Domains0 root0Node31Domains1 f hf root0Node31Step1_checked
  have hb : Covers root0Node31Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node31Domains1 root0Outputs 34
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node32_cover
    · exact root0Node35_cover
  exact hb f h1
theorem root0Node30_cover : Covers root0Node30Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node30Domains0 root0Node30Domains1 f hf root0Node30Step1_checked
  have hb : Covers root0Node30Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node30Domains1 root0Outputs 26
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node31_cover
    · exact root0Node38_cover
  exact hb f h1
theorem root0Node29_cover : Covers root0Node29Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node29Domains0 root0Node29Domains1 f hf root0Node29Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root0Node29Domains1 root0Node29Domains2 f h1 root0Node29Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node29Domains2 (.output 12)
    root0Node29Leaf_checked f h2
theorem root0Node28_cover : Covers root0Node28Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root0Node28Domains0 root0Node28Domains1 f hf root0Node28Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node28Domains1 root0Node28Domains2 f h1 root0Node28Step2_checked
  have hb : Covers root0Node28Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node28Domains2 root0Outputs 18
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node29_cover
    · exact root0Node30_cover
  exact hb f h2
theorem root0Node27_cover : Covers root0Node27Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root0Node27Domains0 root0Node27Domains1 f hf root0Node27Step1_checked
  have hb : Covers root0Node27Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node27Domains1 root0Outputs 2
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node28_cover
    · exact root0Node39_cover
  exact hb f h1
theorem root0Node26_cover : Covers root0Node26Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root0Node26Domains0 root0Node26Domains1 f hf root0Node26Step1_checked
  have hb : Covers root0Node26Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node26Domains1 root0Outputs 3
    intro s hs
    change s ∈ [(0,3),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node27_cover
    · exact root0Node48_cover
  exact hb f h1
theorem root0Node25_cover : Covers root0Node25Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root0Node25Domains0 root0Node25Domains1 f hf root0Node25Step1_checked
  have hb : Covers root0Node25Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node25Domains1 root0Outputs 1
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node26_cover
    · exact root0Node57_cover
  exact hb f h1
theorem root0Node24_cover : Covers root0Node24Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root0Node24Domains0 root0Node24Domains1 f hf root0Node24Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root0Node24Domains1 root0Node24Domains2 f h1 root0Node24Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root0Node24Domains2 root0Node24Domains3 f h2 root0Node24Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root0Node24Domains3 root0Node24Domains4 f h3 root0Node24Step4_checked
  have hb : Covers root0Node24Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node24Domains4 root0Outputs 0
    intro s hs
    change s ∈ [(7,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node25_cover
    · exact root0Node60_cover
  exact hb f h4
theorem root0Node23_cover : Covers root0Node23Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node23Domains0 root0Node23Domains1 f hf root0Node23Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node23Domains1 (.output 11)
    root0Node23Leaf_checked f h1
theorem root0Node22_cover : Covers root0Node22Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node22Domains0 root0Node22Domains1 f hf root0Node22Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node22Domains1 (.output 10)
    root0Node22Leaf_checked f h1
theorem root0Node21_cover : Covers root0Node21Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root0Node21Domains0 root0Node21Domains1 f hf root0Node21Step1_checked
  have hb : Covers root0Node21Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node21Domains1 root0Outputs 3
    intro s hs
    change s ∈ [(1,0),(3,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node22_cover
    · exact root0Node23_cover
  exact hb f h1
theorem root0Node20_cover : Covers root0Node20Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node20Domains0 (.output 9)
    root0Node20Leaf_checked f hf
theorem root0Node19_cover : Covers root0Node19Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node19Domains0 (.output 8)
    root0Node19Leaf_checked f hf
theorem root0Node18_cover : Covers root0Node18Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root0Node18Domains0 root0Node18Domains1 f hf root0Node18Step1_checked
  have hb : Covers root0Node18Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node18Domains1 root0Outputs 17
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node19_cover
    · exact root0Node20_cover
  exact hb f h1
theorem root0Node17_cover : Covers root0Node17Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node17Domains0 (.output 7)
    root0Node17Leaf_checked f hf
theorem root0Node16_cover : Covers root0Node16Domains0 constraints root0Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root0Outputs root0Node16Domains0 (.output 6)
    root0Node16Leaf_checked f hf
theorem root0Node15_cover : Covers root0Node15Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root0Node15Domains0 root0Node15Domains1 f hf root0Node15Step1_checked
  have hb : Covers root0Node15Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node15Domains1 root0Outputs 11
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node16_cover
    · exact root0Node17_cover
  exact hb f h1
theorem root0Node14_cover : Covers root0Node14Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root0Node14Domains0 root0Node14Domains1 f hf root0Node14Step1_checked
  have hb : Covers root0Node14Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node14Domains1 root0Outputs 2
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node15_cover
    · exact root0Node18_cover
  exact hb f h1
theorem root0Node13_cover : Covers root0Node13Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root0Node13Domains0 root0Node13Domains1 f hf root0Node13Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root0Node13Domains1 root0Node13Domains2 f h1 root0Node13Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root0Node13Domains2 root0Node13Domains3 f h2 root0Node13Step3_checked
  have h4 := solution_checkReplacement constraints table39 table39_member
    root0Node13Domains3 root0Node13Domains4 f h3 root0Node13Step4_checked
  have hb : Covers root0Node13Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node13Domains4 root0Outputs 0
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node14_cover
    · exact root0Node21_cover
  exact hb f h4
theorem root0Node12_cover : Covers root0Node12Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root0Node12Domains0 root0Node12Domains1 f hf root0Node12Step1_checked
  have h2 := solution_checkReplacement constraints table3 table3_member
    root0Node12Domains1 root0Node12Domains2 f h1 root0Node12Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root0Node12Domains2 root0Node12Domains3 f h2 root0Node12Step3_checked
  have hb : Covers root0Node12Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node12Domains3 root0Outputs 19
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node13_cover
    · exact root0Node24_cover
  exact hb f h3
theorem root0Node11_cover : Covers root0Node11Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node11Domains0 root0Node11Domains1 f hf root0Node11Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node11Domains1 root0Node11Domains2 f h1 root0Node11Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node11Domains2 (.output 5)
    root0Node11Leaf_checked f h2
theorem root0Node10_cover : Covers root0Node10Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node10Domains0 root0Node10Domains1 f hf root0Node10Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node10Domains1 root0Node10Domains2 f h1 root0Node10Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node10Domains2 (.output 4)
    root0Node10Leaf_checked f h2
theorem root0Node9_cover : Covers root0Node9Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node9Domains0 root0Node9Domains1 f hf root0Node9Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node9Domains1 root0Node9Domains2 f h1 root0Node9Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node9Domains2 (.output 3)
    root0Node9Leaf_checked f h2
theorem root0Node8_cover : Covers root0Node8Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root0Node8Domains0 root0Node8Domains1 f hf root0Node8Step1_checked
  have hb : Covers root0Node8Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node8Domains1 root0Outputs 26
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node9_cover
    · exact root0Node10_cover
  exact hb f h1
theorem root0Node7_cover : Covers root0Node7Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root0Node7Domains0 root0Node7Domains1 f hf root0Node7Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node7Domains1 root0Node7Domains2 f h1 root0Node7Step2_checked
  have h3 := solution_checkReplacement constraints table16 table16_member
    root0Node7Domains2 root0Node7Domains3 f h2 root0Node7Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root0Node7Domains3 root0Node7Domains4 f h3 root0Node7Step4_checked
  have hb : Covers root0Node7Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node7Domains4 root0Outputs 11
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node8_cover
    · exact root0Node11_cover
  exact hb f h4
theorem root0Node6_cover : Covers root0Node6Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root0Node6Domains0 root0Node6Domains1 f hf root0Node6Step1_checked
  have h2 := solution_checkReplacement constraints table10 table10_member
    root0Node6Domains1 root0Node6Domains2 f h1 root0Node6Step2_checked
  have hb : Covers root0Node6Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node6Domains2 root0Outputs 21
    intro s hs
    change s ∈ [(3,0),(5,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node7_cover
    · exact root0Node12_cover
  exact hb f h2
theorem root0Node5_cover : Covers root0Node5Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node5Domains0 root0Node5Domains1 f hf root0Node5Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node5Domains1 root0Node5Domains2 f h1 root0Node5Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node5Domains2 (.output 2)
    root0Node5Leaf_checked f h2
theorem root0Node4_cover : Covers root0Node4Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node4Domains0 root0Node4Domains1 f hf root0Node4Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node4Domains1 root0Node4Domains2 f h1 root0Node4Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node4Domains2 (.output 1)
    root0Node4Leaf_checked f h2
theorem root0Node3_cover : Covers root0Node3Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root0Node3Domains0 root0Node3Domains1 f hf root0Node3Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root0Node3Domains1 root0Node3Domains2 f h1 root0Node3Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node3Domains2 (.output 0)
    root0Node3Leaf_checked f h2
theorem root0Node2_cover : Covers root0Node2Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root0Node2Domains0 root0Node2Domains1 f hf root0Node2Step1_checked
  have hb : Covers root0Node2Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node2Domains1 root0Outputs 26
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node3_cover
    · exact root0Node4_cover
  exact hb f h1
theorem root0Node1_cover : Covers root0Node1Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root0Node1Domains0 root0Node1Domains1 f hf root0Node1Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node1Domains1 root0Node1Domains2 f h1 root0Node1Step2_checked
  have h3 := solution_checkReplacement constraints table16 table16_member
    root0Node1Domains2 root0Node1Domains3 f h2 root0Node1Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root0Node1Domains3 root0Node1Domains4 f h3 root0Node1Step4_checked
  have hb : Covers root0Node1Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node1Domains4 root0Outputs 11
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node2_cover
    · exact root0Node5_cover
  exact hb f h4
theorem root0Node0_cover : Covers root0Node0Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root0Node0Domains0 root0Node0Domains1 f hf root0Node0Step1_checked
  have h2 := solution_checkReplacement constraints table20 table20_member
    root0Node0Domains1 root0Node0Domains2 f h1 root0Node0Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root0Node0Domains2 root0Node0Domains3 f h2 root0Node0Step3_checked
  have h4 := solution_checkReplacement constraints table35 table35_member
    root0Node0Domains3 root0Node0Domains4 f h3 root0Node0Step4_checked
  have hb : Covers root0Node0Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node0Domains4 root0Outputs 31
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node1_cover
    · exact root0Node6_cover
  exact hb f h4
theorem root0_table_cover : Covers (domains (0,0)) constraints root0Outputs := root0Node0_cover
theorem root0Family_count : root0Family.length = 36 := rfl
#print axioms root0_table_cover
end SpectreFinite.HexSearch.RadiusFour
