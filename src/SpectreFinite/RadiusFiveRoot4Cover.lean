module

public import SpectreFinite.RadiusFiveRoot4Part37

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root4Node92_cover : Covers root4Node92Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root4Node92Domains0 root4Node92Domains1 f hf root4Node92Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node92Domains1 root4Node92Domains2 f h1 root4Node92Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node92Domains2 (.output 46)
    root4Node92Leaf_checked f h2
theorem root4Node91_cover : Covers root4Node91Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root4Node91Domains0 root4Node91Domains1 f hf root4Node91Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node91Domains1 (.output 45)
    root4Node91Leaf_checked f h1
theorem root4Node90_cover : Covers root4Node90Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root4Node90Domains0 root4Node90Domains1 f hf root4Node90Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node90Domains1 (.output 44)
    root4Node90Leaf_checked f h1
theorem root4Node89_cover : Covers root4Node89Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root4Node89Domains0 root4Node89Domains1 f hf root4Node89Step1_checked
  have hb : Covers root4Node89Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node89Domains1 root4Outputs 61
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node90_cover
    · exact root4Node91_cover
  exact hb f h1
theorem root4Node88_cover : Covers root4Node88Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root4Node88Domains0 root4Node88Domains1 f hf root4Node88Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root4Node88Domains1 root4Node88Domains2 f h1 root4Node88Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root4Node88Domains2 root4Node88Domains3 f h2 root4Node88Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root4Node88Domains3 root4Node88Domains4 f h3 root4Node88Step4_checked
  have hb : Covers root4Node88Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node88Domains4 root4Outputs 0
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node89_cover
    · exact root4Node92_cover
  exact hb f h4
theorem root4Node87_cover : Covers root4Node87Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node87Domains0 root4Node87Domains1 f hf root4Node87Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node87Domains1 (.output 43)
    root4Node87Leaf_checked f h1
theorem root4Node86_cover : Covers root4Node86Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node86Domains0 root4Node86Domains1 f hf root4Node86Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node86Domains1 (.output 42)
    root4Node86Leaf_checked f h1
theorem root4Node85_cover : Covers root4Node85Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root4Node85Domains0 root4Node85Domains1 f hf root4Node85Step1_checked
  have hb : Covers root4Node85Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node85Domains1 root4Outputs 73
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node86_cover
    · exact root4Node87_cover
  exact hb f h1
theorem root4Node84_cover : Covers root4Node84Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root4Node84Domains0 root4Node84Domains1 f hf root4Node84Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root4Node84Domains1 root4Node84Domains2 f h1 root4Node84Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node84Domains2 (.output 41)
    root4Node84Leaf_checked f h2
theorem root4Node83_cover : Covers root4Node83Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node83Domains0 root4Node83Domains1 f hf root4Node83Step1_checked
  have hb : Covers root4Node83Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node83Domains1 root4Outputs 40
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node84_cover
    · exact root4Node85_cover
  exact hb f h1
theorem root4Node82_cover : Covers root4Node82Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node82Domains0 root4Node82Domains1 f hf root4Node82Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root4Node82Domains1 root4Node82Domains2 f h1 root4Node82Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node82Domains2 (.output 40)
    root4Node82Leaf_checked f h2
theorem root4Node81_cover : Covers root4Node81Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node81Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node81Domains0 root4Outputs 39
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node82_cover
    · exact root4Node83_cover
  exact hb f hf
theorem root4Node80_cover : Covers root4Node80Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root4Node80Domains0 root4Node80Domains1 f hf root4Node80Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root4Node80Domains1 root4Node80Domains2 f h1 root4Node80Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root4Node80Domains2 root4Node80Domains3 f h2 root4Node80Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root4Node80Domains3 root4Node80Domains4 f h3 root4Node80Step4_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node80Domains4 (.output 39)
    root4Node80Leaf_checked f h4
theorem root4Node79_cover : Covers root4Node79Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root4Node79Domains0 root4Node79Domains1 f hf root4Node79Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root4Node79Domains1 root4Node79Domains2 f h1 root4Node79Step2_checked
  have h3 := solution_checkReplacement constraints table40 table40_member
    root4Node79Domains2 root4Node79Domains3 f h2 root4Node79Step3_checked
  have hb : Covers root4Node79Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node79Domains3 root4Outputs 12
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node80_cover
    · exact root4Node81_cover
  exact hb f h3
theorem root4Node78_cover : Covers root4Node78Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root4Node78Domains0 root4Node78Domains1 f hf root4Node78Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node78Domains1 root4Node78Domains2 f h1 root4Node78Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root4Node78Domains2 root4Node78Domains3 f h2 root4Node78Step3_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node78Domains3 (.output 38)
    root4Node78Leaf_checked f h3
theorem root4Node77_cover : Covers root4Node77Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root4Node77Domains0 root4Node77Domains1 f hf root4Node77Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node77Domains1 root4Node77Domains2 f h1 root4Node77Step2_checked
  have hb : Covers root4Node77Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node77Domains2 root4Outputs 19
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node78_cover
    · exact root4Node79_cover
  exact hb f h2
theorem root4Node76_cover : Covers root4Node76Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root4Node76Domains0 root4Node76Domains1 f hf root4Node76Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root4Node76Domains1 root4Node76Domains2 f h1 root4Node76Step2_checked
  have hb : Covers root4Node76Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node76Domains2 root4Outputs 1
    intro s hs
    change s ∈ [(0,0),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node77_cover
    · exact root4Node88_cover
  exact hb f h2
theorem root4Node75_cover : Covers root4Node75Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node75Domains0 root4Node75Domains1 f hf root4Node75Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node75Domains1 (.output 37)
    root4Node75Leaf_checked f h1
theorem root4Node74_cover : Covers root4Node74Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node74Domains0 root4Node74Domains1 f hf root4Node74Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node74Domains1 (.output 36)
    root4Node74Leaf_checked f h1
theorem root4Node73_cover : Covers root4Node73Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node73Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node73Domains0 root4Outputs 73
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node74_cover
    · exact root4Node75_cover
  exact hb f hf
theorem root4Node72_cover : Covers root4Node72Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node72Domains0 root4Node72Domains1 f hf root4Node72Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node72Domains1 (.output 35)
    root4Node72Leaf_checked f h1
theorem root4Node71_cover : Covers root4Node71Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node71Domains0 root4Node71Domains1 f hf root4Node71Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node71Domains1 (.output 34)
    root4Node71Leaf_checked f h1
theorem root4Node70_cover : Covers root4Node70Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node70Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node70Domains0 root4Outputs 73
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node71_cover
    · exact root4Node72_cover
  exact hb f hf
theorem root4Node69_cover : Covers root4Node69Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root4Node69Domains0 root4Node69Domains1 f hf root4Node69Step1_checked
  have hb : Covers root4Node69Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node69Domains1 root4Outputs 50
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node70_cover
    · exact root4Node73_cover
  exact hb f h1
theorem root4Node68_cover : Covers root4Node68Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node68Domains0 (.output 33)
    root4Node68Leaf_checked f hf
theorem root4Node67_cover : Covers root4Node67Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node67Domains0 (.output 32)
    root4Node67Leaf_checked f hf
theorem root4Node66_cover : Covers root4Node66Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root4Node66Domains0 root4Node66Domains1 f hf root4Node66Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root4Node66Domains1 root4Node66Domains2 f h1 root4Node66Step2_checked
  have hb : Covers root4Node66Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node66Domains2 root4Outputs 50
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node67_cover
    · exact root4Node68_cover
  exact hb f h2
theorem root4Node65_cover : Covers root4Node65Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node65Domains0 root4Node65Domains1 f hf root4Node65Step1_checked
  have hb : Covers root4Node65Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node65Domains1 root4Outputs 40
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node66_cover
    · exact root4Node69_cover
  exact hb f h1
theorem root4Node64_cover : Covers root4Node64Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node64Domains0 root4Node64Domains1 f hf root4Node64Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root4Node64Domains1 root4Node64Domains2 f h1 root4Node64Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node64Domains2 (.output 31)
    root4Node64Leaf_checked f h2
theorem root4Node63_cover : Covers root4Node63Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node63Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node63Domains0 root4Outputs 39
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node64_cover
    · exact root4Node65_cover
  exact hb f hf
theorem root4Node62_cover : Covers root4Node62Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root4Node62Domains0 root4Node62Domains1 f hf root4Node62Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root4Node62Domains1 root4Node62Domains2 f h1 root4Node62Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root4Node62Domains2 root4Node62Domains3 f h2 root4Node62Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root4Node62Domains3 root4Node62Domains4 f h3 root4Node62Step4_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node62Domains4 (.output 30)
    root4Node62Leaf_checked f h4
theorem root4Node61_cover : Covers root4Node61Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root4Node61Domains0 root4Node61Domains1 f hf root4Node61Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root4Node61Domains1 root4Node61Domains2 f h1 root4Node61Step2_checked
  have h3 := solution_checkReplacement constraints table40 table40_member
    root4Node61Domains2 root4Node61Domains3 f h2 root4Node61Step3_checked
  have hb : Covers root4Node61Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node61Domains3 root4Outputs 12
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node62_cover
    · exact root4Node63_cover
  exact hb f h3
theorem root4Node60_cover : Covers root4Node60Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root4Node60Domains0 root4Node60Domains1 f hf root4Node60Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node60Domains1 root4Node60Domains2 f h1 root4Node60Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root4Node60Domains2 root4Node60Domains3 f h2 root4Node60Step3_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node60Domains3 (.output 29)
    root4Node60Leaf_checked f h3
theorem root4Node59_cover : Covers root4Node59Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root4Node59Domains0 root4Node59Domains1 f hf root4Node59Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node59Domains1 root4Node59Domains2 f h1 root4Node59Step2_checked
  have hb : Covers root4Node59Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node59Domains2 root4Outputs 19
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node60_cover
    · exact root4Node61_cover
  exact hb f h2
theorem root4Node58_cover : Covers root4Node58Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root4Node58Domains0 root4Node58Domains1 f hf root4Node58Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node58Domains1 root4Node58Domains2 f h1 root4Node58Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root4Node58Domains2 root4Node58Domains3 f h2 root4Node58Step3_checked
  have hb : Covers root4Node58Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node58Domains3 root4Outputs 2
    intro s hs
    change s ∈ [(1,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node59_cover
    · exact root4Node76_cover
  exact hb f h3
theorem root4Node57_cover : Covers root4Node57Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root4Node57Domains0 root4Node57Domains1 f hf root4Node57Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node57Domains1 (.output 28)
    root4Node57Leaf_checked f h1
theorem root4Node56_cover : Covers root4Node56Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root4Node56Domains0 root4Node56Domains1 f hf root4Node56Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node56Domains1 (.output 27)
    root4Node56Leaf_checked f h1
theorem root4Node55_cover : Covers root4Node55Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root4Node55Domains0 root4Node55Domains1 f hf root4Node55Step1_checked
  have hb : Covers root4Node55Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node55Domains1 root4Outputs 20
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node56_cover
    · exact root4Node57_cover
  exact hb f h1
theorem root4Node54_cover : Covers root4Node54Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root4Node54Domains0 root4Node54Domains1 f hf root4Node54Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node54Domains1 (.output 26)
    root4Node54Leaf_checked f h1
theorem root4Node53_cover : Covers root4Node53Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root4Node53Domains0 root4Node53Domains1 f hf root4Node53Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node53Domains1 (.output 25)
    root4Node53Leaf_checked f h1
theorem root4Node52_cover : Covers root4Node52Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root4Node52Domains0 root4Node52Domains1 f hf root4Node52Step1_checked
  have hb : Covers root4Node52Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node52Domains1 root4Outputs 30
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node53_cover
    · exact root4Node54_cover
  exact hb f h1
theorem root4Node51_cover : Covers root4Node51Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root4Node51Domains0 root4Node51Domains1 f hf root4Node51Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node51Domains1 (.output 24)
    root4Node51Leaf_checked f h1
theorem root4Node50_cover : Covers root4Node50Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root4Node50Domains0 root4Node50Domains1 f hf root4Node50Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node50Domains1 (.output 23)
    root4Node50Leaf_checked f h1
theorem root4Node49_cover : Covers root4Node49Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root4Node49Domains0 root4Node49Domains1 f hf root4Node49Step1_checked
  have hb : Covers root4Node49Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node49Domains1 root4Outputs 30
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node50_cover
    · exact root4Node51_cover
  exact hb f h1
theorem root4Node48_cover : Covers root4Node48Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root4Node48Domains0 root4Node48Domains1 f hf root4Node48Step1_checked
  have hb : Covers root4Node48Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node48Domains1 root4Outputs 20
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node49_cover
    · exact root4Node52_cover
  exact hb f h1
theorem root4Node47_cover : Covers root4Node47Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root4Node47Domains0 root4Node47Domains1 f hf root4Node47Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root4Node47Domains1 root4Node47Domains2 f h1 root4Node47Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root4Node47Domains2 root4Node47Domains3 f h2 root4Node47Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root4Node47Domains3 root4Node47Domains4 f h3 root4Node47Step4_checked
  have hb : Covers root4Node47Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node47Domains4 root4Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node48_cover
    · exact root4Node55_cover
  exact hb f h4
theorem root4Node46_cover : Covers root4Node46Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root4Node46Domains0 root4Node46Domains1 f hf root4Node46Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root4Node46Domains1 root4Node46Domains2 f h1 root4Node46Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root4Node46Domains2 root4Node46Domains3 f h2 root4Node46Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root4Node46Domains3 root4Node46Domains4 f h3 root4Node46Step4_checked
  have hb : Covers root4Node46Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node46Domains4 root4Outputs 3
    intro s hs
    change s ∈ [(1,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node47_cover
    · exact root4Node58_cover
  exact hb f h4
theorem root4Node45_cover : Covers root4Node45Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node45Domains0 root4Node45Domains1 f hf root4Node45Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root4Node45Domains1 root4Node45Domains2 f h1 root4Node45Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node45Domains2 (.output 22)
    root4Node45Leaf_checked f h2
theorem root4Node44_cover : Covers root4Node44Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node44Domains0 root4Node44Domains1 f hf root4Node44Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node44Domains1 (.output 21)
    root4Node44Leaf_checked f h1
theorem root4Node43_cover : Covers root4Node43Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node43Domains0 root4Node43Domains1 f hf root4Node43Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node43Domains1 (.output 20)
    root4Node43Leaf_checked f h1
theorem root4Node42_cover : Covers root4Node42Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node42Domains0 root4Node42Domains1 f hf root4Node42Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node42Domains1 (.output 19)
    root4Node42Leaf_checked f h1
theorem root4Node41_cover : Covers root4Node41Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node41Domains0 root4Node41Domains1 f hf root4Node41Step1_checked
  have hb : Covers root4Node41Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node41Domains1 root4Outputs 86
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node42_cover
    · exact root4Node43_cover
  exact hb f h1
theorem root4Node40_cover : Covers root4Node40Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root4Node40Domains0 root4Node40Domains1 f hf root4Node40Step1_checked
  have hb : Covers root4Node40Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node40Domains1 root4Outputs 73
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node41_cover
    · exact root4Node44_cover
  exact hb f h1
theorem root4Node39_cover : Covers root4Node39Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root4Node39Domains0 root4Node39Domains1 f hf root4Node39Step1_checked
  have hb : Covers root4Node39Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node39Domains1 root4Outputs 39
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node40_cover
    · exact root4Node45_cover
  exact hb f h1
theorem root4Node38_cover : Covers root4Node38Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root4Node38Domains0 root4Node38Domains1 f hf root4Node38Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root4Node38Domains1 root4Node38Domains2 f h1 root4Node38Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node38Domains2 (.output 18)
    root4Node38Leaf_checked f h2
theorem root4Node37_cover : Covers root4Node37Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root4Node37Domains0 root4Node37Domains1 f hf root4Node37Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root4Node37Domains1 root4Node37Domains2 f h1 root4Node37Step2_checked
  have hb : Covers root4Node37Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node37Domains2 root4Outputs 12
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node38_cover
    · exact root4Node39_cover
  exact hb f h2
theorem root4Node36_cover : Covers root4Node36Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root4Node36Domains0 root4Node36Domains1 f hf root4Node36Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root4Node36Domains1 root4Node36Domains2 f h1 root4Node36Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node36Domains2 (.output 17)
    root4Node36Leaf_checked f h2
theorem root4Node35_cover : Covers root4Node35Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root4Node35Domains0 root4Node35Domains1 f hf root4Node35Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node35Domains1 root4Node35Domains2 f h1 root4Node35Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root4Node35Domains2 root4Node35Domains3 f h2 root4Node35Step3_checked
  have hb : Covers root4Node35Domains3 constraints root4Outputs := by
    apply covers_of_branches root4Node35Domains3 root4Outputs 3
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node36_cover
    · exact root4Node37_cover
  exact hb f h3
theorem root4Node34_cover : Covers root4Node34Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node34Domains0 root4Node34Domains1 f hf root4Node34Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root4Node34Domains1 root4Node34Domains2 f h1 root4Node34Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node34Domains2 (.output 16)
    root4Node34Leaf_checked f h2
theorem root4Node33_cover : Covers root4Node33Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node33Domains0 (.output 15)
    root4Node33Leaf_checked f hf
theorem root4Node32_cover : Covers root4Node32Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node32Domains0 (.output 14)
    root4Node32Leaf_checked f hf
theorem root4Node31_cover : Covers root4Node31Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node31Domains0 root4Node31Domains1 f hf root4Node31Step1_checked
  have hb : Covers root4Node31Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node31Domains1 root4Outputs 85
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node32_cover
    · exact root4Node33_cover
  exact hb f h1
theorem root4Node30_cover : Covers root4Node30Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node30Domains0 root4Node30Domains1 f hf root4Node30Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node30Domains1 (.output 13)
    root4Node30Leaf_checked f h1
theorem root4Node29_cover : Covers root4Node29Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node29Domains0 root4Node29Domains1 f hf root4Node29Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node29Domains1 (.output 12)
    root4Node29Leaf_checked f h1
theorem root4Node28_cover : Covers root4Node28Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node28Domains0 root4Node28Domains1 f hf root4Node28Step1_checked
  have hb : Covers root4Node28Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node28Domains1 root4Outputs 86
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node29_cover
    · exact root4Node30_cover
  exact hb f h1
theorem root4Node27_cover : Covers root4Node27Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root4Node27Domains0 root4Node27Domains1 f hf root4Node27Step1_checked
  have hb : Covers root4Node27Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node27Domains1 root4Outputs 73
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node28_cover
    · exact root4Node31_cover
  exact hb f h1
theorem root4Node26_cover : Covers root4Node26Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node26Domains0 root4Node26Domains1 f hf root4Node26Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node26Domains1 root4Node26Domains2 f h1 root4Node26Step2_checked
  have hb : Covers root4Node26Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node26Domains2 root4Outputs 39
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node27_cover
    · exact root4Node34_cover
  exact hb f h2
theorem root4Node25_cover : Covers root4Node25Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node25Domains0 root4Node25Domains1 f hf root4Node25Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node25Domains1 (.output 11)
    root4Node25Leaf_checked f h1
theorem root4Node24_cover : Covers root4Node24Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node24Domains0 root4Node24Domains1 f hf root4Node24Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node24Domains1 (.output 10)
    root4Node24Leaf_checked f h1
theorem root4Node23_cover : Covers root4Node23Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node23Domains0 root4Node23Domains1 f hf root4Node23Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node23Domains1 (.output 9)
    root4Node23Leaf_checked f h1
theorem root4Node22_cover : Covers root4Node22Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node22Domains0 root4Node22Domains1 f hf root4Node22Step1_checked
  have hb : Covers root4Node22Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node22Domains1 root4Outputs 86
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node23_cover
    · exact root4Node24_cover
  exact hb f h1
theorem root4Node21_cover : Covers root4Node21Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node21Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node21Domains0 root4Outputs 73
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node22_cover
    · exact root4Node25_cover
  exact hb f hf
theorem root4Node20_cover : Covers root4Node20Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node20Domains0 root4Node20Domains1 f hf root4Node20Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node20Domains1 (.output 8)
    root4Node20Leaf_checked f h1
theorem root4Node19_cover : Covers root4Node19Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node19Domains0 root4Node19Domains1 f hf root4Node19Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node19Domains1 (.output 7)
    root4Node19Leaf_checked f h1
theorem root4Node18_cover : Covers root4Node18Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node18Domains0 root4Node18Domains1 f hf root4Node18Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node18Domains1 (.output 6)
    root4Node18Leaf_checked f h1
theorem root4Node17_cover : Covers root4Node17Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root4Node17Domains0 root4Node17Domains1 f hf root4Node17Step1_checked
  have hb : Covers root4Node17Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node17Domains1 root4Outputs 86
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node18_cover
    · exact root4Node19_cover
  exact hb f h1
theorem root4Node16_cover : Covers root4Node16Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node16Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node16Domains0 root4Outputs 73
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node17_cover
    · exact root4Node20_cover
  exact hb f hf
theorem root4Node15_cover : Covers root4Node15Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node15Domains0 root4Node15Domains1 f hf root4Node15Step1_checked
  have hb : Covers root4Node15Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node15Domains1 root4Outputs 50
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node16_cover
    · exact root4Node21_cover
  exact hb f h1
theorem root4Node14_cover : Covers root4Node14Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root4Node14Domains0 root4Node14Domains1 f hf root4Node14Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root4Node14Domains1 root4Node14Domains2 f h1 root4Node14Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node14Domains2 (.output 5)
    root4Node14Leaf_checked f h2
theorem root4Node13_cover : Covers root4Node13Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root4Node13Domains0 root4Node13Domains1 f hf root4Node13Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node13Domains1 root4Node13Domains2 f h1 root4Node13Step2_checked
  have hb : Covers root4Node13Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node13Domains2 root4Outputs 39
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node14_cover
    · exact root4Node15_cover
  exact hb f h2
theorem root4Node12_cover : Covers root4Node12Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root4Node12Domains0 root4Node12Domains1 f hf root4Node12Step1_checked
  have hb : Covers root4Node12Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node12Domains1 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node13_cover
    · exact root4Node26_cover
  exact hb f h1
theorem root4Node11_cover : Covers root4Node11Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root4Node11Domains0 root4Node11Domains1 f hf root4Node11Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root4Node11Domains1 root4Node11Domains2 f h1 root4Node11Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root4Node11Domains2 root4Node11Domains3 f h2 root4Node11Step3_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node11Domains3 (.output 4)
    root4Node11Leaf_checked f h3
theorem root4Node10_cover : Covers root4Node10Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root4Node10Domains0 root4Node10Domains1 f hf root4Node10Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root4Node10Domains1 root4Node10Domains2 f h1 root4Node10Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root4Node10Domains2 root4Node10Domains3 f h2 root4Node10Step3_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node10Domains3 (.output 3)
    root4Node10Leaf_checked f h3
theorem root4Node9_cover : Covers root4Node9Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root4Node9Domains0 root4Node9Domains1 f hf root4Node9Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root4Node9Domains1 root4Node9Domains2 f h1 root4Node9Step2_checked
  have hb : Covers root4Node9Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node9Domains2 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node10_cover
    · exact root4Node11_cover
  exact hb f h2
theorem root4Node8_cover : Covers root4Node8Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root4Node8Domains0 root4Node8Domains1 f hf root4Node8Step1_checked
  have hb : Covers root4Node8Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node8Domains1 root4Outputs 12
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node9_cover
    · exact root4Node12_cover
  exact hb f h1
theorem root4Node7_cover : Covers root4Node7Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root4Node7Domains0 root4Node7Domains1 f hf root4Node7Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root4Node7Domains1 root4Node7Domains2 f h1 root4Node7Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node7Domains2 (.output 2)
    root4Node7Leaf_checked f h2
theorem root4Node6_cover : Covers root4Node6Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root4Node6Domains0 root4Node6Domains1 f hf root4Node6Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node6Domains1 (.output 1)
    root4Node6Leaf_checked f h1
theorem root4Node5_cover : Covers root4Node5Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root4Node5Domains0 root4Node5Domains1 f hf root4Node5Step1_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node5Domains1 (.output 0)
    root4Node5Leaf_checked f h1
theorem root4Node4_cover : Covers root4Node4Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root4Node4Domains0 root4Node4Domains1 f hf root4Node4Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root4Node4Domains1 root4Node4Domains2 f h1 root4Node4Step2_checked
  have hb : Covers root4Node4Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node4Domains2 root4Outputs 20
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node5_cover
    · exact root4Node6_cover
  exact hb f h2
theorem root4Node3_cover : Covers root4Node3Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root4Node3Domains0 root4Node3Domains1 f hf root4Node3Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root4Node3Domains1 root4Node3Domains2 f h1 root4Node3Step2_checked
  have hb : Covers root4Node3Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node3Domains2 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node4_cover
    · exact root4Node7_cover
  exact hb f h2
theorem root4Node2_cover : Covers root4Node2Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root4Node2Domains0 root4Node2Domains1 f hf root4Node2Step1_checked
  have hb : Covers root4Node2Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node2Domains1 root4Outputs 3
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node3_cover
    · exact root4Node8_cover
  exact hb f h1
theorem root4Node1_cover : Covers root4Node1Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root4Node1Domains0 root4Node1Domains1 f hf root4Node1Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root4Node1Domains1 root4Node1Domains2 f h1 root4Node1Step2_checked
  have h3 := solution_checkReplacement constraints table65 table65_member
    root4Node1Domains2 root4Node1Domains3 f h2 root4Node1Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root4Node1Domains3 root4Node1Domains4 f h3 root4Node1Step4_checked
  have hb : Covers root4Node1Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node1Domains4 root4Outputs 0
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node2_cover
    · exact root4Node35_cover
  exact hb f h4
theorem root4Node0_cover : Covers root4Node0Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root4Node0Domains0 root4Node0Domains1 f hf root4Node0Step1_checked
  have h2 := solution_checkReplacement constraints table33 table33_member
    root4Node0Domains1 root4Node0Domains2 f h1 root4Node0Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root4Node0Domains2 root4Node0Domains3 f h2 root4Node0Step3_checked
  have h4 := solution_checkReplacement constraints table51 table51_member
    root4Node0Domains3 root4Node0Domains4 f h3 root4Node0Step4_checked
  have hb : Covers root4Node0Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node0Domains4 root4Outputs 18
    intro s hs
    change s ∈ [(7,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node1_cover
    · exact root4Node46_cover
  exact hb f h4
theorem root4_table_cover : Covers (domains (4,0)) constraints root4Outputs := root4Node0_cover
theorem root4Family_count : root4Family.length = 47 := rfl
#print axioms root4_table_cover
end SpectreFinite.HexSearch.RadiusFive
