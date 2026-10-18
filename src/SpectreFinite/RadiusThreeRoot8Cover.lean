module

public import SpectreFinite.RadiusThreeRoot8Part36

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root8Node74_cover : Covers root8Node74Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node74Domains0 (.output 37)
    root8Node74Leaf_checked f hf
theorem root8Node73_cover : Covers root8Node73Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node73Domains0 (.output 36)
    root8Node73Leaf_checked f hf
theorem root8Node72_cover : Covers root8Node72Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node72Domains0 root8Node72Domains1 f hf root8Node72Step1_checked
  have hb : Covers root8Node72Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node72Domains1 root8Outputs 33
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node73_cover
    · exact root8Node74_cover
  exact hb f h1
theorem root8Node71_cover : Covers root8Node71Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node71Domains0 (.output 35)
    root8Node71Leaf_checked f hf
theorem root8Node70_cover : Covers root8Node70Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node70Domains0 (.output 34)
    root8Node70Leaf_checked f hf
theorem root8Node69_cover : Covers root8Node69Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node69Domains0 root8Node69Domains1 f hf root8Node69Step1_checked
  have hb : Covers root8Node69Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node69Domains1 root8Outputs 33
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node70_cover
    · exact root8Node71_cover
  exact hb f h1
theorem root8Node68_cover : Covers root8Node68Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root8Node68Domains0 root8Node68Domains1 f hf root8Node68Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root8Node68Domains1 root8Node68Domains2 f h1 root8Node68Step2_checked
  have hb : Covers root8Node68Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node68Domains2 root8Outputs 8
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node69_cover
    · exact root8Node72_cover
  exact hb f h2
theorem root8Node67_cover : Covers root8Node67Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node67Domains0 root8Node67Domains1 f hf root8Node67Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node67Domains1 (.output 33)
    root8Node67Leaf_checked f h1
theorem root8Node66_cover : Covers root8Node66Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node66Domains0 root8Node66Domains1 f hf root8Node66Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node66Domains1 (.output 32)
    root8Node66Leaf_checked f h1
theorem root8Node65_cover : Covers root8Node65Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node65Domains0 root8Node65Domains1 f hf root8Node65Step1_checked
  have hb : Covers root8Node65Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node65Domains1 root8Outputs 32
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node66_cover
    · exact root8Node67_cover
  exact hb f h1
theorem root8Node64_cover : Covers root8Node64Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node64Domains0 root8Node64Domains1 f hf root8Node64Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node64Domains1 (.output 31)
    root8Node64Leaf_checked f h1
theorem root8Node63_cover : Covers root8Node63Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node63Domains0 root8Node63Domains1 f hf root8Node63Step1_checked
  have hb : Covers root8Node63Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node63Domains1 root8Outputs 30
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node64_cover
    · exact root8Node65_cover
  exact hb f h1
theorem root8Node62_cover : Covers root8Node62Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root8Node62Domains0 root8Node62Domains1 f hf root8Node62Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root8Node62Domains1 root8Node62Domains2 f h1 root8Node62Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node62Domains2 (.output 30)
    root8Node62Leaf_checked f h2
theorem root8Node61_cover : Covers root8Node61Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root8Node61Domains0 root8Node61Domains1 f hf root8Node61Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root8Node61Domains1 root8Node61Domains2 f h1 root8Node61Step2_checked
  have hb : Covers root8Node61Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node61Domains2 root8Outputs 8
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node62_cover
    · exact root8Node63_cover
  exact hb f h2
theorem root8Node60_cover : Covers root8Node60Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root8Node60Domains0 root8Node60Domains1 f hf root8Node60Step1_checked
  have hb : Covers root8Node60Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node60Domains1 root8Outputs 4
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node61_cover
    · exact root8Node68_cover
  exact hb f h1
theorem root8Node59_cover : Covers root8Node59Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node59Domains0 (.output 29)
    root8Node59Leaf_checked f hf
theorem root8Node58_cover : Covers root8Node58Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node58Domains0 (.output 28)
    root8Node58Leaf_checked f hf
theorem root8Node57_cover : Covers root8Node57Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node57Domains0 root8Node57Domains1 f hf root8Node57Step1_checked
  have hb : Covers root8Node57Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node57Domains1 root8Outputs 33
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node58_cover
    · exact root8Node59_cover
  exact hb f h1
theorem root8Node56_cover : Covers root8Node56Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node56Domains0 (.output 27)
    root8Node56Leaf_checked f hf
theorem root8Node55_cover : Covers root8Node55Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node55Domains0 (.output 26)
    root8Node55Leaf_checked f hf
theorem root8Node54_cover : Covers root8Node54Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node54Domains0 root8Node54Domains1 f hf root8Node54Step1_checked
  have hb : Covers root8Node54Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node54Domains1 root8Outputs 33
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node55_cover
    · exact root8Node56_cover
  exact hb f h1
theorem root8Node53_cover : Covers root8Node53Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node53Domains0 root8Node53Domains1 f hf root8Node53Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root8Node53Domains1 root8Node53Domains2 f h1 root8Node53Step2_checked
  have hb : Covers root8Node53Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node53Domains2 root8Outputs 8
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node54_cover
    · exact root8Node57_cover
  exact hb f h2
theorem root8Node52_cover : Covers root8Node52Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root8Node52Domains0 root8Node52Domains1 f hf root8Node52Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root8Node52Domains1 root8Node52Domains2 f h1 root8Node52Step2_checked
  have hb : Covers root8Node52Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node52Domains2 root8Outputs 0
    intro s hs
    change s ∈ [(7,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node53_cover
    · exact root8Node60_cover
  exact hb f h2
theorem root8Node51_cover : Covers root8Node51Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node51Domains0 root8Node51Domains1 f hf root8Node51Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node51Domains1 (.output 25)
    root8Node51Leaf_checked f h1
theorem root8Node50_cover : Covers root8Node50Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node50Domains0 root8Node50Domains1 f hf root8Node50Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node50Domains1 (.output 24)
    root8Node50Leaf_checked f h1
theorem root8Node49_cover : Covers root8Node49Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node49Domains0 root8Node49Domains1 f hf root8Node49Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root8Node49Domains1 root8Node49Domains2 f h1 root8Node49Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root8Node49Domains2 root8Node49Domains3 f h2 root8Node49Step3_checked
  have hb : Covers root8Node49Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node49Domains3 root8Outputs 30
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node50_cover
    · exact root8Node51_cover
  exact hb f h3
theorem root8Node48_cover : Covers root8Node48Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node48Domains0 root8Node48Domains1 f hf root8Node48Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node48Domains1 (.output 23)
    root8Node48Leaf_checked f h1
theorem root8Node47_cover : Covers root8Node47Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node47Domains0 root8Node47Domains1 f hf root8Node47Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node47Domains1 (.output 22)
    root8Node47Leaf_checked f h1
theorem root8Node46_cover : Covers root8Node46Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node46Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node46Domains0 root8Outputs 30
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node47_cover
    · exact root8Node48_cover
  exact hb f hf
theorem root8Node45_cover : Covers root8Node45Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node45Domains0 root8Node45Domains1 f hf root8Node45Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node45Domains1 (.output 21)
    root8Node45Leaf_checked f h1
theorem root8Node44_cover : Covers root8Node44Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node44Domains0 root8Node44Domains1 f hf root8Node44Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node44Domains1 (.output 20)
    root8Node44Leaf_checked f h1
theorem root8Node43_cover : Covers root8Node43Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node43Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node43Domains0 root8Outputs 30
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node44_cover
    · exact root8Node45_cover
  exact hb f hf
theorem root8Node42_cover : Covers root8Node42Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root8Node42Domains0 root8Node42Domains1 f hf root8Node42Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root8Node42Domains1 root8Node42Domains2 f h1 root8Node42Step2_checked
  have hb : Covers root8Node42Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node42Domains2 root8Outputs 9
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node43_cover
    · exact root8Node46_cover
  exact hb f h2
theorem root8Node41_cover : Covers root8Node41Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node41Domains0 (.output 19)
    root8Node41Leaf_checked f hf
theorem root8Node40_cover : Covers root8Node40Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node40Domains0 (.output 18)
    root8Node40Leaf_checked f hf
theorem root8Node39_cover : Covers root8Node39Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root8Node39Domains0 root8Node39Domains1 f hf root8Node39Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root8Node39Domains1 root8Node39Domains2 f h1 root8Node39Step2_checked
  have hb : Covers root8Node39Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node39Domains2 root8Outputs 9
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node40_cover
    · exact root8Node41_cover
  exact hb f h2
theorem root8Node38_cover : Covers root8Node38Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node38Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node38Domains0 root8Outputs 8
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node39_cover
    · exact root8Node42_cover
  exact hb f hf
theorem root8Node37_cover : Covers root8Node37Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node37Domains0 root8Node37Domains1 f hf root8Node37Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root8Node37Domains1 root8Node37Domains2 f h1 root8Node37Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root8Node37Domains2 root8Node37Domains3 f h2 root8Node37Step3_checked
  have hb : Covers root8Node37Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node37Domains3 root8Outputs 2
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node38_cover
    · exact root8Node49_cover
  exact hb f h3
theorem root8Node36_cover : Covers root8Node36Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node36Domains0 root8Node36Domains1 f hf root8Node36Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root8Node36Domains1 root8Node36Domains2 f h1 root8Node36Step2_checked
  have h3 := solution_checkReplacement constraints table4 table4_member
    root8Node36Domains2 root8Node36Domains3 f h2 root8Node36Step3_checked
  have hb : Covers root8Node36Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node36Domains3 root8Outputs 1
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node37_cover
    · exact root8Node52_cover
  exact hb f h3
theorem root8Node35_cover : Covers root8Node35Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node35Domains0 root8Node35Domains1 f hf root8Node35Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node35Domains1 (.output 17)
    root8Node35Leaf_checked f h1
theorem root8Node34_cover : Covers root8Node34Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node34Domains0 root8Node34Domains1 f hf root8Node34Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node34Domains1 (.output 16)
    root8Node34Leaf_checked f h1
theorem root8Node33_cover : Covers root8Node33Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node33Domains0 root8Node33Domains1 f hf root8Node33Step1_checked
  have hb : Covers root8Node33Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node33Domains1 root8Outputs 21
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node34_cover
    · exact root8Node35_cover
  exact hb f h1
theorem root8Node32_cover : Covers root8Node32Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node32Domains0 root8Node32Domains1 f hf root8Node32Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node32Domains1 (.output 15)
    root8Node32Leaf_checked f h1
theorem root8Node31_cover : Covers root8Node31Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root8Node31Domains0 root8Node31Domains1 f hf root8Node31Step1_checked
  have hb : Covers root8Node31Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node31Domains1 root8Outputs 13
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node32_cover
    · exact root8Node33_cover
  exact hb f h1
theorem root8Node30_cover : Covers root8Node30Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node30Domains0 root8Node30Domains1 f hf root8Node30Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root8Node30Domains1 root8Node30Domains2 f h1 root8Node30Step2_checked
  have h3 := solution_checkReplacement constraints table30 table30_member
    root8Node30Domains2 root8Node30Domains3 f h2 root8Node30Step3_checked
  have h4 := solution_checkReplacement constraints table26 table26_member
    root8Node30Domains3 root8Node30Domains4 f h3 root8Node30Step4_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node30Domains4 (.output 14)
    root8Node30Leaf_checked f h4
theorem root8Node29_cover : Covers root8Node29Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node29Domains0 (.output 13)
    root8Node29Leaf_checked f hf
theorem root8Node28_cover : Covers root8Node28Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node28Domains0 (.output 12)
    root8Node28Leaf_checked f hf
theorem root8Node27_cover : Covers root8Node27Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node27Domains0 root8Node27Domains1 f hf root8Node27Step1_checked
  have hb : Covers root8Node27Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node27Domains1 root8Outputs 33
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node28_cover
    · exact root8Node29_cover
  exact hb f h1
theorem root8Node26_cover : Covers root8Node26Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root8Node26Domains0 root8Node26Domains1 f hf root8Node26Step1_checked
  have hb : Covers root8Node26Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node26Domains1 root8Outputs 13
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node27_cover
    · exact root8Node30_cover
  exact hb f h1
theorem root8Node25_cover : Covers root8Node25Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root8Node25Domains0 root8Node25Domains1 f hf root8Node25Step1_checked
  have hb : Covers root8Node25Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node25Domains1 root8Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node26_cover
    · exact root8Node31_cover
  exact hb f h1
theorem root8Node24_cover : Covers root8Node24Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root8Node24Domains0 root8Node24Domains1 f hf root8Node24Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node24Domains1 (.output 11)
    root8Node24Leaf_checked f h1
theorem root8Node23_cover : Covers root8Node23Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node23Domains0 root8Node23Domains1 f hf root8Node23Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node23Domains1 (.output 10)
    root8Node23Leaf_checked f h1
theorem root8Node22_cover : Covers root8Node22Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node22Domains0 root8Node22Domains1 f hf root8Node22Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root8Node22Domains1 root8Node22Domains2 f h1 root8Node22Step2_checked
  have hb : Covers root8Node22Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node22Domains2 root8Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node23_cover
    · exact root8Node24_cover
  exact hb f h2
theorem root8Node21_cover : Covers root8Node21Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root8Node21Domains0 root8Node21Domains1 f hf root8Node21Step1_checked
  have hb : Covers root8Node21Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node21Domains1 root8Outputs 3
    intro s hs
    change s ∈ [(1,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node22_cover
    · exact root8Node25_cover
  exact hb f h1
theorem root8Node20_cover : Covers root8Node20Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node20Domains0 root8Node20Domains1 f hf root8Node20Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root8Node20Domains1 root8Node20Domains2 f h1 root8Node20Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root8Node20Domains2 root8Node20Domains3 f h2 root8Node20Step3_checked
  have h4 := solution_checkReplacement constraints table22 table22_member
    root8Node20Domains3 root8Node20Domains4 f h3 root8Node20Step4_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node20Domains4 (.output 9)
    root8Node20Leaf_checked f h4
theorem root8Node19_cover : Covers root8Node19Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node19Domains0 root8Node19Domains1 f hf root8Node19Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root8Node19Domains1 root8Node19Domains2 f h1 root8Node19Step2_checked
  have hb : Covers root8Node19Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node19Domains2 root8Outputs 1
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node20_cover
    · exact root8Node21_cover
  exact hb f h2
theorem root8Node18_cover : Covers root8Node18Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node18Domains0 root8Node18Domains1 f hf root8Node18Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node18Domains1 (.output 8)
    root8Node18Leaf_checked f h1
theorem root8Node17_cover : Covers root8Node17Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node17Domains0 root8Node17Domains1 f hf root8Node17Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node17Domains1 (.output 7)
    root8Node17Leaf_checked f h1
theorem root8Node16_cover : Covers root8Node16Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node16Domains0 root8Node16Domains1 f hf root8Node16Step1_checked
  have hb : Covers root8Node16Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node16Domains1 root8Outputs 34
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node17_cover
    · exact root8Node18_cover
  exact hb f h1
theorem root8Node15_cover : Covers root8Node15Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node15Domains0 root8Node15Domains1 f hf root8Node15Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root8Node15Domains1 root8Node15Domains2 f h1 root8Node15Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node15Domains2 (.output 6)
    root8Node15Leaf_checked f h2
theorem root8Node14_cover : Covers root8Node14Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node14Domains0 root8Node14Domains1 f hf root8Node14Step1_checked
  have hb : Covers root8Node14Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node14Domains1 root8Outputs 21
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node15_cover
    · exact root8Node16_cover
  exact hb f h1
theorem root8Node13_cover : Covers root8Node13Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node13Domains0 root8Node13Domains1 f hf root8Node13Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node13Domains1 (.output 5)
    root8Node13Leaf_checked f h1
theorem root8Node12_cover : Covers root8Node12Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node12Domains0 root8Node12Domains1 f hf root8Node12Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node12Domains1 (.output 4)
    root8Node12Leaf_checked f h1
theorem root8Node11_cover : Covers root8Node11Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node11Domains0 root8Node11Domains1 f hf root8Node11Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root8Node11Domains1 root8Node11Domains2 f h1 root8Node11Step2_checked
  have hb : Covers root8Node11Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node11Domains2 root8Outputs 21
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node12_cover
    · exact root8Node13_cover
  exact hb f h2
theorem root8Node10_cover : Covers root8Node10Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node10Domains0 root8Node10Domains1 f hf root8Node10Step1_checked
  have hb : Covers root8Node10Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node10Domains1 root8Outputs 15
    intro s hs
    change s ∈ [(2,2),(2,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node11_cover
    · exact root8Node14_cover
  exact hb f h1
theorem root8Node9_cover : Covers root8Node9Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node9Domains0 root8Node9Domains1 f hf root8Node9Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node9Domains1 (.output 3)
    root8Node9Leaf_checked f h1
theorem root8Node8_cover : Covers root8Node8Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node8Domains0 root8Node8Domains1 f hf root8Node8Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node8Domains1 (.output 2)
    root8Node8Leaf_checked f h1
theorem root8Node7_cover : Covers root8Node7Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root8Node7Domains0 root8Node7Domains1 f hf root8Node7Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root8Node7Domains1 root8Node7Domains2 f h1 root8Node7Step2_checked
  have hb : Covers root8Node7Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node7Domains2 root8Outputs 15
    intro s hs
    change s ∈ [(2,2),(2,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node8_cover
    · exact root8Node9_cover
  exact hb f h2
theorem root8Node6_cover : Covers root8Node6Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root8Node6Domains0 root8Node6Domains1 f hf root8Node6Step1_checked
  have hb : Covers root8Node6Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node6Domains1 root8Outputs 13
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node7_cover
    · exact root8Node10_cover
  exact hb f h1
theorem root8Node5_cover : Covers root8Node5Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node5Domains0 root8Node5Domains1 f hf root8Node5Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node5Domains1 (.output 1)
    root8Node5Leaf_checked f h1
theorem root8Node4_cover : Covers root8Node4Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node4Domains0 root8Node4Domains1 f hf root8Node4Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node4Domains1 (.output 0)
    root8Node4Leaf_checked f h1
theorem root8Node3_cover : Covers root8Node3Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node3Domains0 root8Node3Domains1 f hf root8Node3Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root8Node3Domains1 root8Node3Domains2 f h1 root8Node3Step2_checked
  have hb : Covers root8Node3Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node3Domains2 root8Outputs 15
    intro s hs
    change s ∈ [(2,2),(2,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node4_cover
    · exact root8Node5_cover
  exact hb f h2
theorem root8Node2_cover : Covers root8Node2Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root8Node2Domains0 root8Node2Domains1 f hf root8Node2Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root8Node2Domains1 root8Node2Domains2 f h1 root8Node2Step2_checked
  have h3 := solution_checkReplacement constraints table22 table22_member
    root8Node2Domains2 root8Node2Domains3 f h2 root8Node2Step3_checked
  have hb : Covers root8Node2Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node2Domains3 root8Outputs 3
    intro s hs
    change s ∈ [(1,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node3_cover
    · exact root8Node6_cover
  exact hb f h3
theorem root8Node1_cover : Covers root8Node1Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root8Node1Domains0 root8Node1Domains1 f hf root8Node1Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root8Node1Domains1 root8Node1Domains2 f h1 root8Node1Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root8Node1Domains2 root8Node1Domains3 f h2 root8Node1Step3_checked
  have h4 := solution_checkReplacement constraints table23 table23_member
    root8Node1Domains3 root8Node1Domains4 f h3 root8Node1Step4_checked
  have hb : Covers root8Node1Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node1Domains4 root8Outputs 0
    intro s hs
    change s ∈ [(4,2),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node2_cover
    · exact root8Node19_cover
  exact hb f h4
theorem root8Node0_cover : Covers root8Node0Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table18 table18_member
    root8Node0Domains0 root8Node0Domains1 f hf root8Node0Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root8Node0Domains1 root8Node0Domains2 f h1 root8Node0Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root8Node0Domains2 root8Node0Domains3 f h2 root8Node0Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root8Node0Domains3 root8Node0Domains4 f h3 root8Node0Step4_checked
  have h5 := solution_checkReplacement constraints table25 table25_member
    root8Node0Domains4 root8Node0Domains5 f h4 root8Node0Step5_checked
  have hb : Covers root8Node0Domains5 constraints root8Outputs := by
    apply covers_of_branches root8Node0Domains5 root8Outputs 12
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node1_cover
    · exact root8Node36_cover
  exact hb f h5
theorem root8_table_cover : Covers (domains (8,0)) constraints root8Outputs := root8Node0_cover
theorem root8Family_count : root8Family.length = 38 := rfl
#print axioms root8_table_cover
end SpectreFinite.HexSearch.RadiusThree
