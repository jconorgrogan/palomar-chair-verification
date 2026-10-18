module

public import SpectreFinite.RadiusThreeRoot7Part58

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node94_cover : Covers root7Node94Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node94Domains0 root7Node94Domains1 f hf root7Node94Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node94Domains1 (.output 47)
    root7Node94Leaf_checked f h1
theorem root7Node93_cover : Covers root7Node93Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node93Domains0 (.output 46)
    root7Node93Leaf_checked f hf
theorem root7Node92_cover : Covers root7Node92Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node92Domains0 (.output 45)
    root7Node92Leaf_checked f hf
theorem root7Node91_cover : Covers root7Node91Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node91Domains0 root7Node91Domains1 f hf root7Node91Step1_checked
  have hb : Covers root7Node91Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node91Domains1 root7Outputs 36
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node92_cover
    · exact root7Node93_cover
  exact hb f h1
theorem root7Node90_cover : Covers root7Node90Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node90Domains0 root7Node90Domains1 f hf root7Node90Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node90Domains1 root7Node90Domains2 f h1 root7Node90Step2_checked
  have hb : Covers root7Node90Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node90Domains2 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node91_cover
    · exact root7Node94_cover
  exact hb f h2
theorem root7Node89_cover : Covers root7Node89Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node89Domains0 root7Node89Domains1 f hf root7Node89Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node89Domains1 root7Node89Domains2 f h1 root7Node89Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node89Domains2 (.output 44)
    root7Node89Leaf_checked f h2
theorem root7Node88_cover : Covers root7Node88Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root7Node88Domains0 root7Node88Domains1 f hf root7Node88Step1_checked
  have hb : Covers root7Node88Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node88Domains1 root7Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node89_cover
    · exact root7Node90_cover
  exact hb f h1
theorem root7Node87_cover : Covers root7Node87Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node87Domains0 root7Node87Domains1 f hf root7Node87Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node87Domains1 root7Node87Domains2 f h1 root7Node87Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node87Domains2 (.output 43)
    root7Node87Leaf_checked f h2
theorem root7Node86_cover : Covers root7Node86Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node86Domains0 root7Node86Domains1 f hf root7Node86Step1_checked
  have hb : Covers root7Node86Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node86Domains1 root7Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node87_cover
    · exact root7Node88_cover
  exact hb f h1
theorem root7Node85_cover : Covers root7Node85Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root7Node85Domains0 root7Node85Domains1 f hf root7Node85Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node85Domains1 (.output 42)
    root7Node85Leaf_checked f h1
theorem root7Node84_cover : Covers root7Node84Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root7Node84Domains0 root7Node84Domains1 f hf root7Node84Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node84Domains1 (.output 41)
    root7Node84Leaf_checked f h1
theorem root7Node83_cover : Covers root7Node83Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node83Domains0 root7Node83Domains1 f hf root7Node83Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node83Domains1 root7Node83Domains2 f h1 root7Node83Step2_checked
  have h3 := solution_checkReplacement constraints table9 table9_member
    root7Node83Domains2 root7Node83Domains3 f h2 root7Node83Step3_checked
  have hb : Covers root7Node83Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node83Domains3 root7Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node84_cover
    · exact root7Node85_cover
  exact hb f h3
theorem root7Node82_cover : Covers root7Node82Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root7Node82Domains0 root7Node82Domains1 f hf root7Node82Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node82Domains1 root7Node82Domains2 f h1 root7Node82Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root7Node82Domains2 root7Node82Domains3 f h2 root7Node82Step3_checked
  have hb : Covers root7Node82Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node82Domains3 root7Outputs 8
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node83_cover
    · exact root7Node86_cover
  exact hb f h3
theorem root7Node81_cover : Covers root7Node81Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node81Domains0 root7Node81Domains1 f hf root7Node81Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node81Domains1 (.output 40)
    root7Node81Leaf_checked f h1
theorem root7Node80_cover : Covers root7Node80Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node80Domains0 (.output 39)
    root7Node80Leaf_checked f hf
theorem root7Node79_cover : Covers root7Node79Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node79Domains0 (.output 38)
    root7Node79Leaf_checked f hf
theorem root7Node78_cover : Covers root7Node78Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node78Domains0 root7Node78Domains1 f hf root7Node78Step1_checked
  have hb : Covers root7Node78Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node78Domains1 root7Outputs 36
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node79_cover
    · exact root7Node80_cover
  exact hb f h1
theorem root7Node77_cover : Covers root7Node77Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node77Domains0 root7Node77Domains1 f hf root7Node77Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node77Domains1 root7Node77Domains2 f h1 root7Node77Step2_checked
  have hb : Covers root7Node77Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node77Domains2 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node78_cover
    · exact root7Node81_cover
  exact hb f h2
theorem root7Node76_cover : Covers root7Node76Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node76Domains0 root7Node76Domains1 f hf root7Node76Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node76Domains1 root7Node76Domains2 f h1 root7Node76Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node76Domains2 (.output 37)
    root7Node76Leaf_checked f h2
theorem root7Node75_cover : Covers root7Node75Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node75Domains0 root7Node75Domains1 f hf root7Node75Step1_checked
  have hb : Covers root7Node75Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node75Domains1 root7Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node76_cover
    · exact root7Node77_cover
  exact hb f h1
theorem root7Node74_cover : Covers root7Node74Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node74Domains0 root7Node74Domains1 f hf root7Node74Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node74Domains1 root7Node74Domains2 f h1 root7Node74Step2_checked
  have h3 := solution_checkReplacement constraints table9 table9_member
    root7Node74Domains2 root7Node74Domains3 f h2 root7Node74Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node74Domains3 (.output 36)
    root7Node74Leaf_checked f h3
theorem root7Node73_cover : Covers root7Node73Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node73Domains0 root7Node73Domains1 f hf root7Node73Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node73Domains1 root7Node73Domains2 f h1 root7Node73Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root7Node73Domains2 root7Node73Domains3 f h2 root7Node73Step3_checked
  have h4 := solution_checkReplacement constraints table22 table22_member
    root7Node73Domains3 root7Node73Domains4 f h3 root7Node73Step4_checked
  have hb : Covers root7Node73Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node73Domains4 root7Outputs 8
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node74_cover
    · exact root7Node75_cover
  exact hb f h4
theorem root7Node72_cover : Covers root7Node72Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root7Node72Domains0 root7Node72Domains1 f hf root7Node72Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node72Domains1 (.output 35)
    root7Node72Leaf_checked f h1
theorem root7Node71_cover : Covers root7Node71Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node71Domains0 (.output 34)
    root7Node71Leaf_checked f hf
theorem root7Node70_cover : Covers root7Node70Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node70Domains0 (.output 33)
    root7Node70Leaf_checked f hf
theorem root7Node69_cover : Covers root7Node69Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root7Node69Domains0 root7Node69Domains1 f hf root7Node69Step1_checked
  have hb : Covers root7Node69Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node69Domains1 root7Outputs 33
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node70_cover
    · exact root7Node71_cover
  exact hb f h1
theorem root7Node68_cover : Covers root7Node68Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node68Domains0 root7Node68Domains1 f hf root7Node68Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node68Domains1 root7Node68Domains2 f h1 root7Node68Step2_checked
  have h3 := solution_checkReplacement constraints table9 table9_member
    root7Node68Domains2 root7Node68Domains3 f h2 root7Node68Step3_checked
  have hb : Covers root7Node68Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node68Domains3 root7Outputs 9
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node69_cover
    · exact root7Node72_cover
  exact hb f h3
theorem root7Node67_cover : Covers root7Node67Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node67Domains0 root7Node67Domains1 f hf root7Node67Step1_checked
  have hb : Covers root7Node67Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node67Domains1 root7Outputs 3
    intro s hs
    change s ∈ [(0,3),(6,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node68_cover
    · exact root7Node73_cover
  exact hb f h1
theorem root7Node66_cover : Covers root7Node66Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root7Node66Domains0 root7Node66Domains1 f hf root7Node66Step1_checked
  have hb : Covers root7Node66Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node66Domains1 root7Outputs 1
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node67_cover
    · exact root7Node82_cover
  exact hb f h1
theorem root7Node65_cover : Covers root7Node65Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node65Domains0 (.output 32)
    root7Node65Leaf_checked f hf
theorem root7Node64_cover : Covers root7Node64Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node64Domains0 (.output 31)
    root7Node64Leaf_checked f hf
theorem root7Node63_cover : Covers root7Node63Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node63Domains0 root7Node63Domains1 f hf root7Node63Step1_checked
  have hb : Covers root7Node63Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node63Domains1 root7Outputs 33
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node64_cover
    · exact root7Node65_cover
  exact hb f h1
theorem root7Node62_cover : Covers root7Node62Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node62Domains0 (.output 30)
    root7Node62Leaf_checked f hf
theorem root7Node61_cover : Covers root7Node61Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node61Domains0 (.output 29)
    root7Node61Leaf_checked f hf
theorem root7Node60_cover : Covers root7Node60Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node60Domains0 root7Node60Domains1 f hf root7Node60Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node60Domains1 root7Node60Domains2 f h1 root7Node60Step2_checked
  have hb : Covers root7Node60Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node60Domains2 root7Outputs 36
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node61_cover
    · exact root7Node62_cover
  exact hb f h2
theorem root7Node59_cover : Covers root7Node59Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node59Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node59Domains0 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node60_cover
    · exact root7Node63_cover
  exact hb f hf
theorem root7Node58_cover : Covers root7Node58Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node58Domains0 root7Node58Domains1 f hf root7Node58Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node58Domains1 root7Node58Domains2 f h1 root7Node58Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node58Domains2 (.output 28)
    root7Node58Leaf_checked f h2
theorem root7Node57_cover : Covers root7Node57Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node57Domains0 root7Node57Domains1 f hf root7Node57Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node57Domains1 root7Node57Domains2 f h1 root7Node57Step2_checked
  have hb : Covers root7Node57Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node57Domains2 root7Outputs 22
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node58_cover
    · exact root7Node59_cover
  exact hb f h2
theorem root7Node56_cover : Covers root7Node56Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node56Domains0 root7Node56Domains1 f hf root7Node56Step1_checked
  have h2 := solution_checkReplacement constraints table22 table22_member
    root7Node56Domains1 root7Node56Domains2 f h1 root7Node56Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node56Domains2 (.output 27)
    root7Node56Leaf_checked f h2
theorem root7Node55_cover : Covers root7Node55Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node55Domains0 root7Node55Domains1 f hf root7Node55Step1_checked
  have hb : Covers root7Node55Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node55Domains1 root7Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node56_cover
    · exact root7Node57_cover
  exact hb f h1
theorem root7Node54_cover : Covers root7Node54Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node54Domains0 root7Node54Domains1 f hf root7Node54Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root7Node54Domains1 root7Node54Domains2 f h1 root7Node54Step2_checked
  have h3 := solution_checkReplacement constraints table25 table25_member
    root7Node54Domains2 root7Node54Domains3 f h2 root7Node54Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node54Domains3 (.output 26)
    root7Node54Leaf_checked f h3
theorem root7Node53_cover : Covers root7Node53Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root7Node53Domains0 root7Node53Domains1 f hf root7Node53Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node53Domains1 root7Node53Domains2 f h1 root7Node53Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root7Node53Domains2 root7Node53Domains3 f h2 root7Node53Step3_checked
  have h4 := solution_checkReplacement constraints table4 table4_member
    root7Node53Domains3 root7Node53Domains4 f h3 root7Node53Step4_checked
  have hb : Covers root7Node53Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node53Domains4 root7Outputs 8
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node54_cover
    · exact root7Node55_cover
  exact hb f h4
theorem root7Node52_cover : Covers root7Node52Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node52Domains0 root7Node52Domains1 f hf root7Node52Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root7Node52Domains1 root7Node52Domains2 f h1 root7Node52Step2_checked
  have h3 := solution_checkReplacement constraints table9 table9_member
    root7Node52Domains2 root7Node52Domains3 f h2 root7Node52Step3_checked
  have h4 := solution_checkReplacement constraints table24 table24_member
    root7Node52Domains3 root7Node52Domains4 f h3 root7Node52Step4_checked
  have h5 := solution_checkReplacement constraints table25 table25_member
    root7Node52Domains4 root7Node52Domains5 f h4 root7Node52Step5_checked
  have h6 := solution_checkReplacement constraints table30 table30_member
    root7Node52Domains5 root7Node52Domains6 f h5 root7Node52Step6_checked
  have h7 := solution_checkReplacement constraints table9 table9_member
    root7Node52Domains6 root7Node52Domains7 f h6 root7Node52Step7_checked
  have hb : Covers root7Node52Domains7 constraints root7Outputs := by
    apply covers_of_branches root7Node52Domains7 root7Outputs 0
    intro s hs
    change s ∈ [(4,2),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node53_cover
    · exact root7Node66_cover
  exact hb f h7
theorem root7Node51_cover : Covers root7Node51Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node51Domains0 (.output 25)
    root7Node51Leaf_checked f hf
theorem root7Node50_cover : Covers root7Node50Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node50Domains0 (.output 24)
    root7Node50Leaf_checked f hf
theorem root7Node49_cover : Covers root7Node49Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node49Domains0 root7Node49Domains1 f hf root7Node49Step1_checked
  have hb : Covers root7Node49Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node49Domains1 root7Outputs 36
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node50_cover
    · exact root7Node51_cover
  exact hb f h1
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
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node46Domains0 root7Node46Domains1 f hf root7Node46Step1_checked
  have hb : Covers root7Node46Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node46Domains1 root7Outputs 35
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node47_cover
    · exact root7Node48_cover
  exact hb f h1
theorem root7Node45_cover : Covers root7Node45Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root7Node45Domains0 root7Node45Domains1 f hf root7Node45Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node45Domains1 root7Node45Domains2 f h1 root7Node45Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root7Node45Domains2 root7Node45Domains3 f h2 root7Node45Step3_checked
  have h4 := solution_checkReplacement constraints table24 table24_member
    root7Node45Domains3 root7Node45Domains4 f h3 root7Node45Step4_checked
  have h5 := solution_checkReplacement constraints table30 table30_member
    root7Node45Domains4 root7Node45Domains5 f h4 root7Node45Step5_checked
  have h6 := solution_checkReplacement constraints table13 table13_member
    root7Node45Domains5 root7Node45Domains6 f h5 root7Node45Step6_checked
  have h7 := solution_checkReplacement constraints table25 table25_member
    root7Node45Domains6 root7Node45Domains7 f h6 root7Node45Step7_checked
  have hb : Covers root7Node45Domains7 constraints root7Outputs := by
    apply covers_of_branches root7Node45Domains7 root7Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node46_cover
    · exact root7Node49_cover
  exact hb f h7
theorem root7Node44_cover : Covers root7Node44Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node44Domains0 root7Node44Domains1 f hf root7Node44Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root7Node44Domains1 root7Node44Domains2 f h1 root7Node44Step2_checked
  have h3 := solution_checkReplacement constraints table19 table19_member
    root7Node44Domains2 root7Node44Domains3 f h2 root7Node44Step3_checked
  have hb : Covers root7Node44Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node44Domains3 root7Outputs 5
    intro s hs
    change s ∈ [(2,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node45_cover
    · exact root7Node52_cover
  exact hb f h3
theorem root7Node43_cover : Covers root7Node43Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root7Node43Domains0 root7Node43Domains1 f hf root7Node43Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node43Domains1 root7Node43Domains2 f h1 root7Node43Step2_checked
  have h3 := solution_checkReplacement constraints table22 table22_member
    root7Node43Domains2 root7Node43Domains3 f h2 root7Node43Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node43Domains3 (.output 21)
    root7Node43Leaf_checked f h3
theorem root7Node42_cover : Covers root7Node42Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node42Domains0 (.output 20)
    root7Node42Leaf_checked f hf
theorem root7Node41_cover : Covers root7Node41Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node41Domains0 (.output 19)
    root7Node41Leaf_checked f hf
theorem root7Node40_cover : Covers root7Node40Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node40Domains0 root7Node40Domains1 f hf root7Node40Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node40Domains1 root7Node40Domains2 f h1 root7Node40Step2_checked
  have h3 := solution_checkReplacement constraints table8 table8_member
    root7Node40Domains2 root7Node40Domains3 f h2 root7Node40Step3_checked
  have hb : Covers root7Node40Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node40Domains3 root7Outputs 22
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node41_cover
    · exact root7Node42_cover
  exact hb f h3
theorem root7Node39_cover : Covers root7Node39Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node39Domains0 root7Node39Domains1 f hf root7Node39Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node39Domains1 (.output 18)
    root7Node39Leaf_checked f h1
theorem root7Node38_cover : Covers root7Node38Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node38Domains0 root7Node38Domains1 f hf root7Node38Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node38Domains1 (.output 17)
    root7Node38Leaf_checked f h1
theorem root7Node37_cover : Covers root7Node37Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node37Domains0 root7Node37Domains1 f hf root7Node37Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node37Domains1 root7Node37Domains2 f h1 root7Node37Step2_checked
  have hb : Covers root7Node37Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node37Domains2 root7Outputs 21
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node38_cover
    · exact root7Node39_cover
  exact hb f h2
theorem root7Node36_cover : Covers root7Node36Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node36Domains0 root7Node36Domains1 f hf root7Node36Step1_checked
  have hb : Covers root7Node36Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node36Domains1 root7Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node37_cover
    · exact root7Node40_cover
  exact hb f h1
theorem root7Node35_cover : Covers root7Node35Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node35Domains0 root7Node35Domains1 f hf root7Node35Step1_checked
  have h2 := solution_checkReplacement constraints table8 table8_member
    root7Node35Domains1 root7Node35Domains2 f h1 root7Node35Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root7Node35Domains2 root7Node35Domains3 f h2 root7Node35Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node35Domains3 (.output 16)
    root7Node35Leaf_checked f h3
theorem root7Node34_cover : Covers root7Node34Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root7Node34Domains0 root7Node34Domains1 f hf root7Node34Step1_checked
  have h2 := solution_checkReplacement constraints table22 table22_member
    root7Node34Domains1 root7Node34Domains2 f h1 root7Node34Step2_checked
  have hb : Covers root7Node34Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node34Domains2 root7Outputs 13
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node35_cover
    · exact root7Node36_cover
  exact hb f h2
theorem root7Node33_cover : Covers root7Node33Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node33Domains0 root7Node33Domains1 f hf root7Node33Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node33Domains1 root7Node33Domains2 f h1 root7Node33Step2_checked
  have hb : Covers root7Node33Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node33Domains2 root7Outputs 4
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node34_cover
    · exact root7Node43_cover
  exact hb f h2
theorem root7Node32_cover : Covers root7Node32Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root7Node32Domains0 root7Node32Domains1 f hf root7Node32Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node32Domains1 root7Node32Domains2 f h1 root7Node32Step2_checked
  have h3 := solution_checkReplacement constraints table22 table22_member
    root7Node32Domains2 root7Node32Domains3 f h2 root7Node32Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node32Domains3 (.output 15)
    root7Node32Leaf_checked f h3
theorem root7Node31_cover : Covers root7Node31Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node31Domains0 root7Node31Domains1 f hf root7Node31Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node31Domains1 root7Node31Domains2 f h1 root7Node31Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node31Domains2 (.output 14)
    root7Node31Leaf_checked f h2
theorem root7Node30_cover : Covers root7Node30Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node30Domains0 root7Node30Domains1 f hf root7Node30Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node30Domains1 root7Node30Domains2 f h1 root7Node30Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node30Domains2 (.output 13)
    root7Node30Leaf_checked f h2
theorem root7Node29_cover : Covers root7Node29Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node29Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node29Domains0 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node30_cover
    · exact root7Node31_cover
  exact hb f hf
theorem root7Node28_cover : Covers root7Node28Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node28Domains0 root7Node28Domains1 f hf root7Node28Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node28Domains1 root7Node28Domains2 f h1 root7Node28Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node28Domains2 (.output 12)
    root7Node28Leaf_checked f h2
theorem root7Node27_cover : Covers root7Node27Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node27Domains0 root7Node27Domains1 f hf root7Node27Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node27Domains1 root7Node27Domains2 f h1 root7Node27Step2_checked
  have hb : Covers root7Node27Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node27Domains2 root7Outputs 22
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node28_cover
    · exact root7Node29_cover
  exact hb f h2
theorem root7Node26_cover : Covers root7Node26Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node26Domains0 root7Node26Domains1 f hf root7Node26Step1_checked
  have h2 := solution_checkReplacement constraints table22 table22_member
    root7Node26Domains1 root7Node26Domains2 f h1 root7Node26Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node26Domains2 (.output 11)
    root7Node26Leaf_checked f h2
theorem root7Node25_cover : Covers root7Node25Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root7Node25Domains0 root7Node25Domains1 f hf root7Node25Step1_checked
  have h2 := solution_checkReplacement constraints table22 table22_member
    root7Node25Domains1 root7Node25Domains2 f h1 root7Node25Step2_checked
  have hb : Covers root7Node25Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node25Domains2 root7Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node26_cover
    · exact root7Node27_cover
  exact hb f h2
theorem root7Node24_cover : Covers root7Node24Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node24Domains0 root7Node24Domains1 f hf root7Node24Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node24Domains1 root7Node24Domains2 f h1 root7Node24Step2_checked
  have hb : Covers root7Node24Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node24Domains2 root7Outputs 4
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node25_cover
    · exact root7Node32_cover
  exact hb f h2
theorem root7Node23_cover : Covers root7Node23Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node23Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node23Domains0 root7Outputs 3
    intro s hs
    change s ∈ [(1,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node24_cover
    · exact root7Node33_cover
  exact hb f hf
theorem root7Node22_cover : Covers root7Node22Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root7Node22Domains0 root7Node22Domains1 f hf root7Node22Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node22Domains1 root7Node22Domains2 f h1 root7Node22Step2_checked
  have h3 := solution_checkReplacement constraints table22 table22_member
    root7Node22Domains2 root7Node22Domains3 f h2 root7Node22Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node22Domains3 (.output 10)
    root7Node22Leaf_checked f h3
theorem root7Node21_cover : Covers root7Node21Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node21Domains0 root7Node21Domains1 f hf root7Node21Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node21Domains1 root7Node21Domains2 f h1 root7Node21Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node21Domains2 (.output 9)
    root7Node21Leaf_checked f h2
theorem root7Node20_cover : Covers root7Node20Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node20Domains0 root7Node20Domains1 f hf root7Node20Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node20Domains1 root7Node20Domains2 f h1 root7Node20Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node20Domains2 (.output 8)
    root7Node20Leaf_checked f h2
theorem root7Node19_cover : Covers root7Node19Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node19Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node19Domains0 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node20_cover
    · exact root7Node21_cover
  exact hb f hf
theorem root7Node18_cover : Covers root7Node18Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node18Domains0 root7Node18Domains1 f hf root7Node18Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node18Domains1 root7Node18Domains2 f h1 root7Node18Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node18Domains2 (.output 7)
    root7Node18Leaf_checked f h2
theorem root7Node17_cover : Covers root7Node17Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node17Domains0 root7Node17Domains1 f hf root7Node17Step1_checked
  have h2 := solution_checkReplacement constraints table15 table15_member
    root7Node17Domains1 root7Node17Domains2 f h1 root7Node17Step2_checked
  have hb : Covers root7Node17Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node17Domains2 root7Outputs 22
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node18_cover
    · exact root7Node19_cover
  exact hb f h2
theorem root7Node16_cover : Covers root7Node16Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node16Domains0 root7Node16Domains1 f hf root7Node16Step1_checked
  have h2 := solution_checkReplacement constraints table22 table22_member
    root7Node16Domains1 root7Node16Domains2 f h1 root7Node16Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node16Domains2 (.output 6)
    root7Node16Leaf_checked f h2
theorem root7Node15_cover : Covers root7Node15Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root7Node15Domains0 root7Node15Domains1 f hf root7Node15Step1_checked
  have h2 := solution_checkReplacement constraints table22 table22_member
    root7Node15Domains1 root7Node15Domains2 f h1 root7Node15Step2_checked
  have hb : Covers root7Node15Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node15Domains2 root7Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node16_cover
    · exact root7Node17_cover
  exact hb f h2
theorem root7Node14_cover : Covers root7Node14Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root7Node14Domains0 root7Node14Domains1 f hf root7Node14Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node14Domains1 root7Node14Domains2 f h1 root7Node14Step2_checked
  have hb : Covers root7Node14Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node14Domains2 root7Outputs 4
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node15_cover
    · exact root7Node22_cover
  exact hb f h2
theorem root7Node13_cover : Covers root7Node13Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node13Domains0 root7Node13Domains1 f hf root7Node13Step1_checked
  have h2 := solution_checkReplacement constraints table9 table9_member
    root7Node13Domains1 root7Node13Domains2 f h1 root7Node13Step2_checked
  have h3 := solution_checkReplacement constraints table24 table24_member
    root7Node13Domains2 root7Node13Domains3 f h2 root7Node13Step3_checked
  have hb : Covers root7Node13Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node13Domains3 root7Outputs 0
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node14_cover
    · exact root7Node23_cover
  exact hb f h3
theorem root7Node12_cover : Covers root7Node12Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node12Domains0 (.output 5)
    root7Node12Leaf_checked f hf
theorem root7Node11_cover : Covers root7Node11Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node11Domains0 (.output 4)
    root7Node11Leaf_checked f hf
theorem root7Node10_cover : Covers root7Node10Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node10Domains0 root7Node10Domains1 f hf root7Node10Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node10Domains1 root7Node10Domains2 f h1 root7Node10Step2_checked
  have hb : Covers root7Node10Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node10Domains2 root7Outputs 35
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node11_cover
    · exact root7Node12_cover
  exact hb f h2
theorem root7Node9_cover : Covers root7Node9Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node9Domains0 root7Node9Domains1 f hf root7Node9Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node9Domains1 root7Node9Domains2 f h1 root7Node9Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node9Domains2 (.output 3)
    root7Node9Leaf_checked f h2
theorem root7Node8_cover : Covers root7Node8Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node8Domains0 root7Node8Domains1 f hf root7Node8Step1_checked
  have hb : Covers root7Node8Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node8Domains1 root7Outputs 22
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node9_cover
    · exact root7Node10_cover
  exact hb f h1
theorem root7Node7_cover : Covers root7Node7Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node7Domains0 (.output 2)
    root7Node7Leaf_checked f hf
theorem root7Node6_cover : Covers root7Node6Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node6Domains0 (.output 1)
    root7Node6Leaf_checked f hf
theorem root7Node5_cover : Covers root7Node5Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node5Domains0 root7Node5Domains1 f hf root7Node5Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node5Domains1 root7Node5Domains2 f h1 root7Node5Step2_checked
  have hb : Covers root7Node5Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node5Domains2 root7Outputs 35
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node6_cover
    · exact root7Node7_cover
  exact hb f h2
theorem root7Node4_cover : Covers root7Node4Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root7Node4Domains0 root7Node4Domains1 f hf root7Node4Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node4Domains1 root7Node4Domains2 f h1 root7Node4Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node4Domains2 (.output 0)
    root7Node4Leaf_checked f h2
theorem root7Node3_cover : Covers root7Node3Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node3Domains0 root7Node3Domains1 f hf root7Node3Step1_checked
  have hb : Covers root7Node3Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node3Domains1 root7Outputs 22
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node4_cover
    · exact root7Node5_cover
  exact hb f h1
theorem root7Node2_cover : Covers root7Node2Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root7Node2Domains0 root7Node2Domains1 f hf root7Node2Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node2Domains1 root7Node2Domains2 f h1 root7Node2Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root7Node2Domains2 root7Node2Domains3 f h2 root7Node2Step3_checked
  have h4 := solution_checkReplacement constraints table8 table8_member
    root7Node2Domains3 root7Node2Domains4 f h3 root7Node2Step4_checked
  have h5 := solution_checkReplacement constraints table22 table22_member
    root7Node2Domains4 root7Node2Domains5 f h4 root7Node2Step5_checked
  have hb : Covers root7Node2Domains5 constraints root7Outputs := by
    apply covers_of_branches root7Node2Domains5 root7Outputs 1
    intro s hs
    change s ∈ [(1,0),(3,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node3_cover
    · exact root7Node8_cover
  exact hb f h5
theorem root7Node1_cover : Covers root7Node1Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root7Node1Domains0 root7Node1Domains1 f hf root7Node1Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root7Node1Domains1 root7Node1Domains2 f h1 root7Node1Step2_checked
  have h3 := solution_checkReplacement constraints table25 table25_member
    root7Node1Domains2 root7Node1Domains3 f h2 root7Node1Step3_checked
  have hb : Covers root7Node1Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node1Domains3 root7Outputs 5
    intro s hs
    change s ∈ [(4,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node2_cover
    · exact root7Node13_cover
  exact hb f h3
theorem root7Node0_cover : Covers root7Node0Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root7Node0Domains0 root7Node0Domains1 f hf root7Node0Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node0Domains1 root7Node0Domains2 f h1 root7Node0Step2_checked
  have h3 := solution_checkReplacement constraints table30 table30_member
    root7Node0Domains2 root7Node0Domains3 f h2 root7Node0Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root7Node0Domains3 root7Node0Domains4 f h3 root7Node0Step4_checked
  have hb : Covers root7Node0Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node0Domains4 root7Outputs 6
    intro s hs
    change s ∈ [(0,0),(1,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node1_cover
    · exact root7Node44_cover
  exact hb f h4
theorem root7_table_cover : Covers (domains (7,0)) constraints root7Outputs := root7Node0_cover
theorem root7Family_count : root7Family.length = 48 := rfl
#print axioms root7_table_cover
end SpectreFinite.HexSearch.RadiusThree
