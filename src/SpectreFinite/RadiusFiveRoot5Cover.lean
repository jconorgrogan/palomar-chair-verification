module

public import SpectreFinite.RadiusFiveRoot5Part29

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root5Node70_cover : Covers root5Node70Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node70Domains0 root5Node70Domains1 f hf root5Node70Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node70Domains1 (.output 35)
    root5Node70Leaf_checked f h1
theorem root5Node69_cover : Covers root5Node69Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node69Domains0 root5Node69Domains1 f hf root5Node69Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node69Domains1 (.output 34)
    root5Node69Leaf_checked f h1
theorem root5Node68_cover : Covers root5Node68Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root5Node68Domains0 root5Node68Domains1 f hf root5Node68Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node68Domains1 root5Node68Domains2 f h1 root5Node68Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root5Node68Domains2 root5Node68Domains3 f h2 root5Node68Step3_checked
  have h4 := solution_checkReplacement constraints table51 table51_member
    root5Node68Domains3 root5Node68Domains4 f h3 root5Node68Step4_checked
  have hb : Covers root5Node68Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node68Domains4 root5Outputs 3
    intro s hs
    change s ∈ [(4,0),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node69_cover
    · exact root5Node70_cover
  exact hb f h4
theorem root5Node67_cover : Covers root5Node67Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node67Domains0 root5Node67Domains1 f hf root5Node67Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node67Domains1 (.output 33)
    root5Node67Leaf_checked f h1
theorem root5Node66_cover : Covers root5Node66Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node66Domains0 root5Node66Domains1 f hf root5Node66Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node66Domains1 (.output 32)
    root5Node66Leaf_checked f h1
theorem root5Node65_cover : Covers root5Node65Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table53 table53_member
    root5Node65Domains0 root5Node65Domains1 f hf root5Node65Step1_checked
  have hb : Covers root5Node65Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node65Domains1 root5Outputs 73
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node66_cover
    · exact root5Node67_cover
  exact hb f h1
theorem root5Node64_cover : Covers root5Node64Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node64Domains0 root5Node64Domains1 f hf root5Node64Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node64Domains1 root5Node64Domains2 f h1 root5Node64Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node64Domains2 (.output 31)
    root5Node64Leaf_checked f h2
theorem root5Node63_cover : Covers root5Node63Domains0 constraints root5Outputs := by
  intro f hf
  have hb : Covers root5Node63Domains0 constraints root5Outputs := by
    apply covers_of_branches root5Node63Domains0 root5Outputs 30
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node64_cover
    · exact root5Node65_cover
  exact hb f hf
theorem root5Node62_cover : Covers root5Node62Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node62Domains0 root5Node62Domains1 f hf root5Node62Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node62Domains1 root5Node62Domains2 f h1 root5Node62Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node62Domains2 (.output 30)
    root5Node62Leaf_checked f h2
theorem root5Node61_cover : Covers root5Node61Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node61Domains0 root5Node61Domains1 f hf root5Node61Step1_checked
  have hb : Covers root5Node61Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node61Domains1 root5Outputs 13
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node62_cover
    · exact root5Node63_cover
  exact hb f h1
theorem root5Node60_cover : Covers root5Node60Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node60Domains0 root5Node60Domains1 f hf root5Node60Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node60Domains1 (.output 29)
    root5Node60Leaf_checked f h1
theorem root5Node59_cover : Covers root5Node59Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node59Domains0 root5Node59Domains1 f hf root5Node59Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node59Domains1 (.output 28)
    root5Node59Leaf_checked f h1
theorem root5Node58_cover : Covers root5Node58Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table53 table53_member
    root5Node58Domains0 root5Node58Domains1 f hf root5Node58Step1_checked
  have hb : Covers root5Node58Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node58Domains1 root5Outputs 73
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node59_cover
    · exact root5Node60_cover
  exact hb f h1
theorem root5Node57_cover : Covers root5Node57Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node57Domains0 root5Node57Domains1 f hf root5Node57Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node57Domains1 root5Node57Domains2 f h1 root5Node57Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node57Domains2 (.output 27)
    root5Node57Leaf_checked f h2
theorem root5Node56_cover : Covers root5Node56Domains0 constraints root5Outputs := by
  intro f hf
  have hb : Covers root5Node56Domains0 constraints root5Outputs := by
    apply covers_of_branches root5Node56Domains0 root5Outputs 30
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node57_cover
    · exact root5Node58_cover
  exact hb f hf
theorem root5Node55_cover : Covers root5Node55Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node55Domains0 root5Node55Domains1 f hf root5Node55Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node55Domains1 root5Node55Domains2 f h1 root5Node55Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node55Domains2 (.output 26)
    root5Node55Leaf_checked f h2
theorem root5Node54_cover : Covers root5Node54Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node54Domains0 root5Node54Domains1 f hf root5Node54Step1_checked
  have hb : Covers root5Node54Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node54Domains1 root5Outputs 13
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node55_cover
    · exact root5Node56_cover
  exact hb f h1
theorem root5Node53_cover : Covers root5Node53Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root5Node53Domains0 root5Node53Domains1 f hf root5Node53Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root5Node53Domains1 root5Node53Domains2 f h1 root5Node53Step2_checked
  have h3 := solution_checkReplacement constraints table19 table19_member
    root5Node53Domains2 root5Node53Domains3 f h2 root5Node53Step3_checked
  have h4 := solution_checkReplacement constraints table13 table13_member
    root5Node53Domains3 root5Node53Domains4 f h3 root5Node53Step4_checked
  have hb : Covers root5Node53Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node53Domains4 root5Outputs 3
    intro s hs
    change s ∈ [(4,0),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node54_cover
    · exact root5Node61_cover
  exact hb f h4
theorem root5Node52_cover : Covers root5Node52Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node52Domains0 root5Node52Domains1 f hf root5Node52Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node52Domains1 (.output 25)
    root5Node52Leaf_checked f h1
theorem root5Node51_cover : Covers root5Node51Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node51Domains0 root5Node51Domains1 f hf root5Node51Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node51Domains1 (.output 24)
    root5Node51Leaf_checked f h1
theorem root5Node50_cover : Covers root5Node50Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node50Domains0 root5Node50Domains1 f hf root5Node50Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root5Node50Domains1 root5Node50Domains2 f h1 root5Node50Step2_checked
  have hb : Covers root5Node50Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node50Domains2 root5Outputs 78
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node51_cover
    · exact root5Node52_cover
  exact hb f h2
theorem root5Node49_cover : Covers root5Node49Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node49Domains0 (.output 23)
    root5Node49Leaf_checked f hf
theorem root5Node48_cover : Covers root5Node48Domains0 constraints root5Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root5Outputs root5Node48Domains0 (.output 22)
    root5Node48Leaf_checked f hf
theorem root5Node47_cover : Covers root5Node47Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root5Node47Domains0 root5Node47Domains1 f hf root5Node47Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root5Node47Domains1 root5Node47Domains2 f h1 root5Node47Step2_checked
  have hb : Covers root5Node47Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node47Domains2 root5Outputs 77
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node48_cover
    · exact root5Node49_cover
  exact hb f h2
theorem root5Node46_cover : Covers root5Node46Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node46Domains0 root5Node46Domains1 f hf root5Node46Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node46Domains1 root5Node46Domains2 f h1 root5Node46Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node46Domains2 (.output 21)
    root5Node46Leaf_checked f h2
theorem root5Node45_cover : Covers root5Node45Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node45Domains0 root5Node45Domains1 f hf root5Node45Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node45Domains1 (.output 20)
    root5Node45Leaf_checked f h1
theorem root5Node44_cover : Covers root5Node44Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node44Domains0 root5Node44Domains1 f hf root5Node44Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node44Domains1 (.output 19)
    root5Node44Leaf_checked f h1
theorem root5Node43_cover : Covers root5Node43Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root5Node43Domains0 root5Node43Domains1 f hf root5Node43Step1_checked
  have hb : Covers root5Node43Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node43Domains1 root5Outputs 73
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node44_cover
    · exact root5Node45_cover
  exact hb f h1
theorem root5Node42_cover : Covers root5Node42Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root5Node42Domains0 root5Node42Domains1 f hf root5Node42Step1_checked
  have hb : Covers root5Node42Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node42Domains1 root5Outputs 40
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node43_cover
    · exact root5Node46_cover
  exact hb f h1
theorem root5Node41_cover : Covers root5Node41Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root5Node41Domains0 root5Node41Domains1 f hf root5Node41Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node41Domains1 root5Node41Domains2 f h1 root5Node41Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root5Node41Domains2 root5Node41Domains3 f h2 root5Node41Step3_checked
  have hb : Covers root5Node41Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node41Domains3 root5Outputs 39
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node42_cover
    · exact root5Node47_cover
  exact hb f h3
theorem root5Node40_cover : Covers root5Node40Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table53 table53_member
    root5Node40Domains0 root5Node40Domains1 f hf root5Node40Step1_checked
  have hb : Covers root5Node40Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node40Domains1 root5Outputs 14
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node41_cover
    · exact root5Node50_cover
  exact hb f h1
theorem root5Node39_cover : Covers root5Node39Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root5Node39Domains0 root5Node39Domains1 f hf root5Node39Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root5Node39Domains1 root5Node39Domains2 f h1 root5Node39Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node39Domains2 (.output 18)
    root5Node39Leaf_checked f h2
theorem root5Node38_cover : Covers root5Node38Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root5Node38Domains0 root5Node38Domains1 f hf root5Node38Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node38Domains1 (.output 17)
    root5Node38Leaf_checked f h1
theorem root5Node37_cover : Covers root5Node37Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root5Node37Domains0 root5Node37Domains1 f hf root5Node37Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node37Domains1 (.output 16)
    root5Node37Leaf_checked f h1
theorem root5Node36_cover : Covers root5Node36Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root5Node36Domains0 root5Node36Domains1 f hf root5Node36Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root5Node36Domains1 root5Node36Domains2 f h1 root5Node36Step2_checked
  have hb : Covers root5Node36Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node36Domains2 root5Outputs 40
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node37_cover
    · exact root5Node38_cover
  exact hb f h2
theorem root5Node35_cover : Covers root5Node35Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table53 table53_member
    root5Node35Domains0 root5Node35Domains1 f hf root5Node35Step1_checked
  have hb : Covers root5Node35Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node35Domains1 root5Outputs 39
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node36_cover
    · exact root5Node39_cover
  exact hb f h1
theorem root5Node34_cover : Covers root5Node34Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node34Domains0 root5Node34Domains1 f hf root5Node34Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root5Node34Domains1 root5Node34Domains2 f h1 root5Node34Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node34Domains2 (.output 15)
    root5Node34Leaf_checked f h2
theorem root5Node33_cover : Covers root5Node33Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root5Node33Domains0 root5Node33Domains1 f hf root5Node33Step1_checked
  have hb : Covers root5Node33Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node33Domains1 root5Outputs 30
    intro s hs
    change s ∈ [(2,1),(4,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node34_cover
    · exact root5Node35_cover
  exact hb f h1
theorem root5Node32_cover : Covers root5Node32Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node32Domains0 root5Node32Domains1 f hf root5Node32Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root5Node32Domains1 root5Node32Domains2 f h1 root5Node32Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node32Domains2 (.output 14)
    root5Node32Leaf_checked f h2
theorem root5Node31_cover : Covers root5Node31Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root5Node31Domains0 root5Node31Domains1 f hf root5Node31Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root5Node31Domains1 root5Node31Domains2 f h1 root5Node31Step2_checked
  have hb : Covers root5Node31Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node31Domains2 root5Outputs 21
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node32_cover
    · exact root5Node33_cover
  exact hb f h2
theorem root5Node30_cover : Covers root5Node30Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node30Domains0 root5Node30Domains1 f hf root5Node30Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root5Node30Domains1 root5Node30Domains2 f h1 root5Node30Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node30Domains2 (.output 13)
    root5Node30Leaf_checked f h2
theorem root5Node29_cover : Covers root5Node29Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node29Domains0 root5Node29Domains1 f hf root5Node29Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node29Domains1 root5Node29Domains2 f h1 root5Node29Step2_checked
  have hb : Covers root5Node29Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node29Domains2 root5Outputs 14
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node30_cover
    · exact root5Node31_cover
  exact hb f h2
theorem root5Node28_cover : Covers root5Node28Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node28Domains0 root5Node28Domains1 f hf root5Node28Step1_checked
  have hb : Covers root5Node28Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node28Domains1 root5Outputs 13
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node29_cover
    · exact root5Node40_cover
  exact hb f h1
theorem root5Node27_cover : Covers root5Node27Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root5Node27Domains0 root5Node27Domains1 f hf root5Node27Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root5Node27Domains1 root5Node27Domains2 f h1 root5Node27Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node27Domains2 (.output 12)
    root5Node27Leaf_checked f h2
theorem root5Node26_cover : Covers root5Node26Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node26Domains0 root5Node26Domains1 f hf root5Node26Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node26Domains1 (.output 11)
    root5Node26Leaf_checked f h1
theorem root5Node25_cover : Covers root5Node25Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root5Node25Domains0 root5Node25Domains1 f hf root5Node25Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node25Domains1 (.output 10)
    root5Node25Leaf_checked f h1
theorem root5Node24_cover : Covers root5Node24Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root5Node24Domains0 root5Node24Domains1 f hf root5Node24Step1_checked
  have hb : Covers root5Node24Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node24Domains1 root5Outputs 78
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node25_cover
    · exact root5Node26_cover
  exact hb f h1
theorem root5Node23_cover : Covers root5Node23Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node23Domains0 root5Node23Domains1 f hf root5Node23Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root5Node23Domains1 root5Node23Domains2 f h1 root5Node23Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node23Domains2 (.output 9)
    root5Node23Leaf_checked f h2
theorem root5Node22_cover : Covers root5Node22Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root5Node22Domains0 root5Node22Domains1 f hf root5Node22Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root5Node22Domains1 root5Node22Domains2 f h1 root5Node22Step2_checked
  have hb : Covers root5Node22Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node22Domains2 root5Outputs 40
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node23_cover
    · exact root5Node24_cover
  exact hb f h2
theorem root5Node21_cover : Covers root5Node21Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table53 table53_member
    root5Node21Domains0 root5Node21Domains1 f hf root5Node21Step1_checked
  have hb : Covers root5Node21Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node21Domains1 root5Outputs 39
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node22_cover
    · exact root5Node27_cover
  exact hb f h1
theorem root5Node20_cover : Covers root5Node20Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root5Node20Domains0 root5Node20Domains1 f hf root5Node20Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root5Node20Domains1 root5Node20Domains2 f h1 root5Node20Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node20Domains2 (.output 8)
    root5Node20Leaf_checked f h2
theorem root5Node19_cover : Covers root5Node19Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root5Node19Domains0 root5Node19Domains1 f hf root5Node19Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root5Node19Domains1 root5Node19Domains2 f h1 root5Node19Step2_checked
  have h3 := solution_checkReplacement constraints table21 table21_member
    root5Node19Domains2 root5Node19Domains3 f h2 root5Node19Step3_checked
  have hb : Covers root5Node19Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node19Domains3 root5Outputs 13
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node20_cover
    · exact root5Node21_cover
  exact hb f h3
theorem root5Node18_cover : Covers root5Node18Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root5Node18Domains0 root5Node18Domains1 f hf root5Node18Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root5Node18Domains1 root5Node18Domains2 f h1 root5Node18Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root5Node18Domains2 root5Node18Domains3 f h2 root5Node18Step3_checked
  have hb : Covers root5Node18Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node18Domains3 root5Outputs 3
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node19_cover
    · exact root5Node28_cover
  exact hb f h3
theorem root5Node17_cover : Covers root5Node17Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root5Node17Domains0 root5Node17Domains1 f hf root5Node17Step1_checked
  have hb : Covers root5Node17Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node17Domains1 root5Outputs 1
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node18_cover
    · exact root5Node53_cover
  exact hb f h1
theorem root5Node16_cover : Covers root5Node16Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root5Node16Domains0 root5Node16Domains1 f hf root5Node16Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root5Node16Domains1 root5Node16Domains2 f h1 root5Node16Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root5Node16Domains2 root5Node16Domains3 f h2 root5Node16Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root5Node16Domains3 root5Node16Domains4 f h3 root5Node16Step4_checked
  have hb : Covers root5Node16Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node16Domains4 root5Outputs 0
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node17_cover
    · exact root5Node68_cover
  exact hb f h4
theorem root5Node15_cover : Covers root5Node15Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node15Domains0 root5Node15Domains1 f hf root5Node15Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node15Domains1 (.output 7)
    root5Node15Leaf_checked f h1
theorem root5Node14_cover : Covers root5Node14Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node14Domains0 root5Node14Domains1 f hf root5Node14Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node14Domains1 (.output 6)
    root5Node14Leaf_checked f h1
theorem root5Node13_cover : Covers root5Node13Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node13Domains0 root5Node13Domains1 f hf root5Node13Step1_checked
  have hb : Covers root5Node13Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node13Domains1 root5Outputs 5
    intro s hs
    change s ∈ [(2,4),(4,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node14_cover
    · exact root5Node15_cover
  exact hb f h1
theorem root5Node12_cover : Covers root5Node12Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node12Domains0 root5Node12Domains1 f hf root5Node12Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node12Domains1 (.output 5)
    root5Node12Leaf_checked f h1
theorem root5Node11_cover : Covers root5Node11Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root5Node11Domains0 root5Node11Domains1 f hf root5Node11Step1_checked
  have hb : Covers root5Node11Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node11Domains1 root5Outputs 11
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node12_cover
    · exact root5Node13_cover
  exact hb f h1
theorem root5Node10_cover : Covers root5Node10Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root5Node10Domains0 root5Node10Domains1 f hf root5Node10Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root5Node10Domains1 root5Node10Domains2 f h1 root5Node10Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root5Node10Domains2 root5Node10Domains3 f h2 root5Node10Step3_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node10Domains3 (.output 4)
    root5Node10Leaf_checked f h3
theorem root5Node9_cover : Covers root5Node9Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root5Node9Domains0 root5Node9Domains1 f hf root5Node9Step1_checked
  have h2 := solution_checkReplacement constraints table21 table21_member
    root5Node9Domains1 root5Node9Domains2 f h1 root5Node9Step2_checked
  have hb : Covers root5Node9Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node9Domains2 root5Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node10_cover
    · exact root5Node11_cover
  exact hb f h2
theorem root5Node8_cover : Covers root5Node8Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root5Node8Domains0 root5Node8Domains1 f hf root5Node8Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node8Domains1 (.output 3)
    root5Node8Leaf_checked f h1
theorem root5Node7_cover : Covers root5Node7Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root5Node7Domains0 root5Node7Domains1 f hf root5Node7Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node7Domains1 (.output 2)
    root5Node7Leaf_checked f h1
theorem root5Node6_cover : Covers root5Node6Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root5Node6Domains0 root5Node6Domains1 f hf root5Node6Step1_checked
  have hb : Covers root5Node6Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node6Domains1 root5Outputs 4
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node7_cover
    · exact root5Node8_cover
  exact hb f h1
theorem root5Node5_cover : Covers root5Node5Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root5Node5Domains0 root5Node5Domains1 f hf root5Node5Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node5Domains1 (.output 1)
    root5Node5Leaf_checked f h1
theorem root5Node4_cover : Covers root5Node4Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root5Node4Domains0 root5Node4Domains1 f hf root5Node4Step1_checked
  have hb : Covers root5Node4Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node4Domains1 root5Outputs 3
    intro s hs
    change s ∈ [(4,0),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node5_cover
    · exact root5Node6_cover
  exact hb f h1
theorem root5Node3_cover : Covers root5Node3Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root5Node3Domains0 root5Node3Domains1 f hf root5Node3Step1_checked
  have h2 := solution_checkReplacement constraints table21 table21_member
    root5Node3Domains1 root5Node3Domains2 f h1 root5Node3Step2_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node3Domains2 (.output 0)
    root5Node3Leaf_checked f h2
theorem root5Node2_cover : Covers root5Node2Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root5Node2Domains0 root5Node2Domains1 f hf root5Node2Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root5Node2Domains1 root5Node2Domains2 f h1 root5Node2Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root5Node2Domains2 root5Node2Domains3 f h2 root5Node2Step3_checked
  have hb : Covers root5Node2Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node2Domains3 root5Outputs 0
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node3_cover
    · exact root5Node4_cover
  exact hb f h3
theorem root5Node1_cover : Covers root5Node1Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root5Node1Domains0 root5Node1Domains1 f hf root5Node1Step1_checked
  have h2 := solution_checkReplacement constraints table34 table34_member
    root5Node1Domains1 root5Node1Domains2 f h1 root5Node1Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root5Node1Domains2 root5Node1Domains3 f h2 root5Node1Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root5Node1Domains3 root5Node1Domains4 f h3 root5Node1Step4_checked
  have h5 := solution_checkReplacement constraints table1 table1_member
    root5Node1Domains4 root5Node1Domains5 f h4 root5Node1Step5_checked
  have hb : Covers root5Node1Domains5 constraints root5Outputs := by
    apply covers_of_branches root5Node1Domains5 root5Outputs 8
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node2_cover
    · exact root5Node9_cover
  exact hb f h5
theorem root5Node0_cover : Covers root5Node0Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root5Node0Domains0 root5Node0Domains1 f hf root5Node0Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root5Node0Domains1 root5Node0Domains2 f h1 root5Node0Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root5Node0Domains2 root5Node0Domains3 f h2 root5Node0Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root5Node0Domains3 root5Node0Domains4 f h3 root5Node0Step4_checked
  have hb : Covers root5Node0Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node0Domains4 root5Outputs 43
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node1_cover
    · exact root5Node16_cover
  exact hb f h4
theorem root5_table_cover : Covers (domains (5,0)) constraints root5Outputs := root5Node0_cover
theorem root5Family_count : root5Family.length = 36 := rfl
#print axioms root5_table_cover
end SpectreFinite.HexSearch.RadiusFive
