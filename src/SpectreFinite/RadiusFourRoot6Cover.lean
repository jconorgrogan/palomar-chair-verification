module

public import SpectreFinite.RadiusFourRoot6Part23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root6Node86_cover : Covers root6Node86Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node86Domains0 root6Node86Domains1 f hf root6Node86Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node86Domains1 (.output 43)
    root6Node86Leaf_checked f h1
theorem root6Node85_cover : Covers root6Node85Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node85Domains0 root6Node85Domains1 f hf root6Node85Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node85Domains1 (.output 42)
    root6Node85Leaf_checked f h1
theorem root6Node84_cover : Covers root6Node84Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node84Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node84Domains0 root6Outputs 56
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node85_cover
    · exact root6Node86_cover
  exact hb f hf
theorem root6Node83_cover : Covers root6Node83Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node83Domains0 root6Node83Domains1 f hf root6Node83Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node83Domains1 (.output 41)
    root6Node83Leaf_checked f h1
theorem root6Node82_cover : Covers root6Node82Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node82Domains0 root6Node82Domains1 f hf root6Node82Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node82Domains1 (.output 40)
    root6Node82Leaf_checked f h1
theorem root6Node81_cover : Covers root6Node81Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node81Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node81Domains0 root6Outputs 56
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node82_cover
    · exact root6Node83_cover
  exact hb f hf
theorem root6Node80_cover : Covers root6Node80Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node80Domains0 root6Node80Domains1 f hf root6Node80Step1_checked
  have hb : Covers root6Node80Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node80Domains1 root6Outputs 34
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node81_cover
    · exact root6Node84_cover
  exact hb f h1
theorem root6Node79_cover : Covers root6Node79Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node79Domains0 root6Node79Domains1 f hf root6Node79Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node79Domains1 (.output 39)
    root6Node79Leaf_checked f h1
theorem root6Node78_cover : Covers root6Node78Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node78Domains0 root6Node78Domains1 f hf root6Node78Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node78Domains1 (.output 38)
    root6Node78Leaf_checked f h1
theorem root6Node77_cover : Covers root6Node77Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node77Domains0 root6Node77Domains1 f hf root6Node77Step1_checked
  have hb : Covers root6Node77Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node77Domains1 root6Outputs 56
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node78_cover
    · exact root6Node79_cover
  exact hb f h1
theorem root6Node76_cover : Covers root6Node76Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root6Node76Domains0 root6Node76Domains1 f hf root6Node76Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root6Node76Domains1 root6Node76Domains2 f h1 root6Node76Step2_checked
  have hb : Covers root6Node76Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node76Domains2 root6Outputs 17
    intro s hs
    change s ∈ [(2,3),(4,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node77_cover
    · exact root6Node80_cover
  exact hb f h2
theorem root6Node75_cover : Covers root6Node75Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root6Node75Domains0 root6Node75Domains1 f hf root6Node75Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root6Node75Domains1 root6Node75Domains2 f h1 root6Node75Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node75Domains2 (.output 37)
    root6Node75Leaf_checked f h2
theorem root6Node74_cover : Covers root6Node74Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root6Node74Domains0 root6Node74Domains1 f hf root6Node74Step1_checked
  have hb : Covers root6Node74Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node74Domains1 root6Outputs 16
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node75_cover
    · exact root6Node76_cover
  exact hb f h1
theorem root6Node73_cover : Covers root6Node73Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node73Domains0 root6Node73Domains1 f hf root6Node73Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root6Node73Domains1 root6Node73Domains2 f h1 root6Node73Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node73Domains2 (.output 36)
    root6Node73Leaf_checked f h2
theorem root6Node72_cover : Covers root6Node72Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root6Node72Domains0 root6Node72Domains1 f hf root6Node72Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root6Node72Domains1 root6Node72Domains2 f h1 root6Node72Step2_checked
  have h3 := solution_checkReplacement constraints table16 table16_member
    root6Node72Domains2 root6Node72Domains3 f h2 root6Node72Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root6Node72Domains3 root6Node72Domains4 f h3 root6Node72Step4_checked
  have hb : Covers root6Node72Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node72Domains4 root6Outputs 3
    intro s hs
    change s ∈ [(4,0),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node73_cover
    · exact root6Node74_cover
  exact hb f h4
theorem root6Node71_cover : Covers root6Node71Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node71Domains0 root6Node71Domains1 f hf root6Node71Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node71Domains1 (.output 35)
    root6Node71Leaf_checked f h1
theorem root6Node70_cover : Covers root6Node70Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node70Domains0 root6Node70Domains1 f hf root6Node70Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node70Domains1 (.output 34)
    root6Node70Leaf_checked f h1
theorem root6Node69_cover : Covers root6Node69Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node69Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node69Domains0 root6Outputs 56
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node70_cover
    · exact root6Node71_cover
  exact hb f hf
theorem root6Node68_cover : Covers root6Node68Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node68Domains0 root6Node68Domains1 f hf root6Node68Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node68Domains1 (.output 33)
    root6Node68Leaf_checked f h1
theorem root6Node67_cover : Covers root6Node67Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node67Domains0 root6Node67Domains1 f hf root6Node67Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node67Domains1 (.output 32)
    root6Node67Leaf_checked f h1
theorem root6Node66_cover : Covers root6Node66Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node66Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node66Domains0 root6Outputs 56
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node67_cover
    · exact root6Node68_cover
  exact hb f hf
theorem root6Node65_cover : Covers root6Node65Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node65Domains0 root6Node65Domains1 f hf root6Node65Step1_checked
  have hb : Covers root6Node65Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node65Domains1 root6Outputs 34
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node66_cover
    · exact root6Node69_cover
  exact hb f h1
theorem root6Node64_cover : Covers root6Node64Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node64Domains0 (.output 31)
    root6Node64Leaf_checked f hf
theorem root6Node63_cover : Covers root6Node63Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node63Domains0 (.output 30)
    root6Node63Leaf_checked f hf
theorem root6Node62_cover : Covers root6Node62Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node62Domains0 root6Node62Domains1 f hf root6Node62Step1_checked
  have hb : Covers root6Node62Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node62Domains1 root6Outputs 34
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node63_cover
    · exact root6Node64_cover
  exact hb f h1
theorem root6Node61_cover : Covers root6Node61Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root6Node61Domains0 root6Node61Domains1 f hf root6Node61Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root6Node61Domains1 root6Node61Domains2 f h1 root6Node61Step2_checked
  have h3 := solution_checkReplacement constraints table14 table14_member
    root6Node61Domains2 root6Node61Domains3 f h2 root6Node61Step3_checked
  have hb : Covers root6Node61Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node61Domains3 root6Outputs 11
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node62_cover
    · exact root6Node65_cover
  exact hb f h3
theorem root6Node60_cover : Covers root6Node60Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node60Domains0 root6Node60Domains1 f hf root6Node60Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node60Domains1 (.output 29)
    root6Node60Leaf_checked f h1
theorem root6Node59_cover : Covers root6Node59Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node59Domains0 root6Node59Domains1 f hf root6Node59Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node59Domains1 (.output 28)
    root6Node59Leaf_checked f h1
theorem root6Node58_cover : Covers root6Node58Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root6Node58Domains0 root6Node58Domains1 f hf root6Node58Step1_checked
  have hb : Covers root6Node58Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node58Domains1 root6Outputs 55
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node59_cover
    · exact root6Node60_cover
  exact hb f h1
theorem root6Node57_cover : Covers root6Node57Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root6Node57Domains0 root6Node57Domains1 f hf root6Node57Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node57Domains1 (.output 27)
    root6Node57Leaf_checked f h1
theorem root6Node56_cover : Covers root6Node56Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node56Domains0 root6Node56Domains1 f hf root6Node56Step1_checked
  have hb : Covers root6Node56Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node56Domains1 root6Outputs 50
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node57_cover
    · exact root6Node58_cover
  exact hb f h1
theorem root6Node55_cover : Covers root6Node55Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node55Domains0 root6Node55Domains1 f hf root6Node55Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node55Domains1 (.output 26)
    root6Node55Leaf_checked f h1
theorem root6Node54_cover : Covers root6Node54Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node54Domains0 root6Node54Domains1 f hf root6Node54Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node54Domains1 (.output 25)
    root6Node54Leaf_checked f h1
theorem root6Node53_cover : Covers root6Node53Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node53Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node53Domains0 root6Outputs 56
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node54_cover
    · exact root6Node55_cover
  exact hb f hf
theorem root6Node52_cover : Covers root6Node52Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node52Domains0 root6Node52Domains1 f hf root6Node52Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node52Domains1 (.output 24)
    root6Node52Leaf_checked f h1
theorem root6Node51_cover : Covers root6Node51Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node51Domains0 root6Node51Domains1 f hf root6Node51Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node51Domains1 (.output 23)
    root6Node51Leaf_checked f h1
theorem root6Node50_cover : Covers root6Node50Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node50Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node50Domains0 root6Outputs 56
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node51_cover
    · exact root6Node52_cover
  exact hb f hf
theorem root6Node49_cover : Covers root6Node49Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node49Domains0 root6Node49Domains1 f hf root6Node49Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root6Node49Domains1 root6Node49Domains2 f h1 root6Node49Step2_checked
  have hb : Covers root6Node49Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node49Domains2 root6Outputs 11
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node50_cover
    · exact root6Node53_cover
  exact hb f h2
theorem root6Node48_cover : Covers root6Node48Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node48Domains0 root6Node48Domains1 f hf root6Node48Step1_checked
  have hb : Covers root6Node48Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node48Domains1 root6Outputs 18
    intro s hs
    change s ∈ [(0,1),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node49_cover
    · exact root6Node56_cover
  exact hb f h1
theorem root6Node47_cover : Covers root6Node47Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node47Domains0 root6Node47Domains1 f hf root6Node47Step1_checked
  have h2 := solution_checkReplacement constraints table35 table35_member
    root6Node47Domains1 root6Node47Domains2 f h1 root6Node47Step2_checked
  have h3 := solution_checkReplacement constraints table4 table4_member
    root6Node47Domains2 root6Node47Domains3 f h2 root6Node47Step3_checked
  have hb : Covers root6Node47Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node47Domains3 root6Outputs 17
    intro s hs
    change s ∈ [(2,3),(4,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node48_cover
    · exact root6Node61_cover
  exact hb f h3
theorem root6Node46_cover : Covers root6Node46Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node46Domains0 root6Node46Domains1 f hf root6Node46Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root6Node46Domains1 root6Node46Domains2 f h1 root6Node46Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node46Domains2 (.output 22)
    root6Node46Leaf_checked f h2
theorem root6Node45_cover : Covers root6Node45Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node45Domains0 (.output 21)
    root6Node45Leaf_checked f hf
theorem root6Node44_cover : Covers root6Node44Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node44Domains0 (.output 20)
    root6Node44Leaf_checked f hf
theorem root6Node43_cover : Covers root6Node43Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node43Domains0 root6Node43Domains1 f hf root6Node43Step1_checked
  have hb : Covers root6Node43Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node43Domains1 root6Outputs 58
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node44_cover
    · exact root6Node45_cover
  exact hb f h1
theorem root6Node42_cover : Covers root6Node42Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node42Domains0 root6Node42Domains1 f hf root6Node42Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node42Domains1 (.output 19)
    root6Node42Leaf_checked f h1
theorem root6Node41_cover : Covers root6Node41Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node41Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node41Domains0 root6Outputs 26
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node42_cover
    · exact root6Node43_cover
  exact hb f hf
theorem root6Node40_cover : Covers root6Node40Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node40Domains0 root6Node40Domains1 f hf root6Node40Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node40Domains1 (.output 18)
    root6Node40Leaf_checked f h1
theorem root6Node39_cover : Covers root6Node39Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node39Domains0 root6Node39Domains1 f hf root6Node39Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root6Node39Domains1 root6Node39Domains2 f h1 root6Node39Step2_checked
  have hb : Covers root6Node39Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node39Domains2 root6Outputs 11
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node40_cover
    · exact root6Node41_cover
  exact hb f h2
theorem root6Node38_cover : Covers root6Node38Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root6Node38Domains0 root6Node38Domains1 f hf root6Node38Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root6Node38Domains1 root6Node38Domains2 f h1 root6Node38Step2_checked
  have hb : Covers root6Node38Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node38Domains2 root6Outputs 18
    intro s hs
    change s ∈ [(0,1),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node39_cover
    · exact root6Node46_cover
  exact hb f h2
theorem root6Node37_cover : Covers root6Node37Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root6Node37Domains0 root6Node37Domains1 f hf root6Node37Step1_checked
  have hb : Covers root6Node37Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node37Domains1 root6Outputs 16
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node38_cover
    · exact root6Node47_cover
  exact hb f h1
theorem root6Node36_cover : Covers root6Node36Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node36Domains0 root6Node36Domains1 f hf root6Node36Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root6Node36Domains1 root6Node36Domains2 f h1 root6Node36Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node36Domains2 (.output 17)
    root6Node36Leaf_checked f h2
theorem root6Node35_cover : Covers root6Node35Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node35Domains0 (.output 16)
    root6Node35Leaf_checked f hf
theorem root6Node34_cover : Covers root6Node34Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node34Domains0 (.output 15)
    root6Node34Leaf_checked f hf
theorem root6Node33_cover : Covers root6Node33Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node33Domains0 root6Node33Domains1 f hf root6Node33Step1_checked
  have hb : Covers root6Node33Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node33Domains1 root6Outputs 58
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node34_cover
    · exact root6Node35_cover
  exact hb f h1
theorem root6Node32_cover : Covers root6Node32Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node32Domains0 root6Node32Domains1 f hf root6Node32Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node32Domains1 (.output 14)
    root6Node32Leaf_checked f h1
theorem root6Node31_cover : Covers root6Node31Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node31Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node31Domains0 root6Outputs 26
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node32_cover
    · exact root6Node33_cover
  exact hb f hf
theorem root6Node30_cover : Covers root6Node30Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node30Domains0 root6Node30Domains1 f hf root6Node30Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node30Domains1 (.output 13)
    root6Node30Leaf_checked f h1
theorem root6Node29_cover : Covers root6Node29Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node29Domains0 root6Node29Domains1 f hf root6Node29Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root6Node29Domains1 root6Node29Domains2 f h1 root6Node29Step2_checked
  have hb : Covers root6Node29Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node29Domains2 root6Outputs 11
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node30_cover
    · exact root6Node31_cover
  exact hb f h2
theorem root6Node28_cover : Covers root6Node28Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node28Domains0 root6Node28Domains1 f hf root6Node28Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root6Node28Domains1 root6Node28Domains2 f h1 root6Node28Step2_checked
  have hb : Covers root6Node28Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node28Domains2 root6Outputs 18
    intro s hs
    change s ∈ [(0,1),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node29_cover
    · exact root6Node36_cover
  exact hb f h2
theorem root6Node27_cover : Covers root6Node27Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root6Node27Domains0 root6Node27Domains1 f hf root6Node27Step1_checked
  have h2 := solution_checkReplacement constraints table18 table18_member
    root6Node27Domains1 root6Node27Domains2 f h1 root6Node27Step2_checked
  have h3 := solution_checkReplacement constraints table31 table31_member
    root6Node27Domains2 root6Node27Domains3 f h2 root6Node27Step3_checked
  have hb : Covers root6Node27Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node27Domains3 root6Outputs 3
    intro s hs
    change s ∈ [(4,0),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node28_cover
    · exact root6Node37_cover
  exact hb f h3
theorem root6Node26_cover : Covers root6Node26Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node26Domains0 root6Node26Domains1 f hf root6Node26Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node26Domains1 (.output 12)
    root6Node26Leaf_checked f h1
theorem root6Node25_cover : Covers root6Node25Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node25Domains0 (.output 11)
    root6Node25Leaf_checked f hf
theorem root6Node24_cover : Covers root6Node24Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node24Domains0 (.output 10)
    root6Node24Leaf_checked f hf
theorem root6Node23_cover : Covers root6Node23Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node23Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node23Domains0 root6Outputs 58
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node24_cover
    · exact root6Node25_cover
  exact hb f hf
theorem root6Node22_cover : Covers root6Node22Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node22Domains0 root6Node22Domains1 f hf root6Node22Step1_checked
  have hb : Covers root6Node22Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node22Domains1 root6Outputs 43
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node23_cover
    · exact root6Node26_cover
  exact hb f h1
theorem root6Node21_cover : Covers root6Node21Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node21Domains0 root6Node21Domains1 f hf root6Node21Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node21Domains1 (.output 9)
    root6Node21Leaf_checked f h1
theorem root6Node20_cover : Covers root6Node20Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node20Domains0 root6Node20Domains1 f hf root6Node20Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root6Node20Domains1 root6Node20Domains2 f h1 root6Node20Step2_checked
  have hb : Covers root6Node20Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node20Domains2 root6Outputs 11
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node21_cover
    · exact root6Node22_cover
  exact hb f h2
theorem root6Node19_cover : Covers root6Node19Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node19Domains0 root6Node19Domains1 f hf root6Node19Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node19Domains1 (.output 8)
    root6Node19Leaf_checked f h1
theorem root6Node18_cover : Covers root6Node18Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node18Domains0 (.output 7)
    root6Node18Leaf_checked f hf
theorem root6Node17_cover : Covers root6Node17Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node17Domains0 (.output 6)
    root6Node17Leaf_checked f hf
theorem root6Node16_cover : Covers root6Node16Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node16Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node16Domains0 root6Outputs 58
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node17_cover
    · exact root6Node18_cover
  exact hb f hf
theorem root6Node15_cover : Covers root6Node15Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node15Domains0 root6Node15Domains1 f hf root6Node15Step1_checked
  have hb : Covers root6Node15Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node15Domains1 root6Outputs 43
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node16_cover
    · exact root6Node19_cover
  exact hb f h1
theorem root6Node14_cover : Covers root6Node14Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root6Node14Domains0 root6Node14Domains1 f hf root6Node14Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node14Domains1 (.output 5)
    root6Node14Leaf_checked f h1
theorem root6Node13_cover : Covers root6Node13Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node13Domains0 root6Node13Domains1 f hf root6Node13Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root6Node13Domains1 root6Node13Domains2 f h1 root6Node13Step2_checked
  have hb : Covers root6Node13Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node13Domains2 root6Outputs 11
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node14_cover
    · exact root6Node15_cover
  exact hb f h2
theorem root6Node12_cover : Covers root6Node12Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root6Node12Domains0 root6Node12Domains1 f hf root6Node12Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root6Node12Domains1 root6Node12Domains2 f h1 root6Node12Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root6Node12Domains2 root6Node12Domains3 f h2 root6Node12Step3_checked
  have h4 := solution_checkReplacement constraints table16 table16_member
    root6Node12Domains3 root6Node12Domains4 f h3 root6Node12Step4_checked
  have hb : Covers root6Node12Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node12Domains4 root6Outputs 3
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node13_cover
    · exact root6Node20_cover
  exact hb f h4
theorem root6Node11_cover : Covers root6Node11Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root6Node11Domains0 root6Node11Domains1 f hf root6Node11Step1_checked
  have hb : Covers root6Node11Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node11Domains1 root6Outputs 1
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node12_cover
    · exact root6Node27_cover
  exact hb f h1
theorem root6Node10_cover : Covers root6Node10Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root6Node10Domains0 root6Node10Domains1 f hf root6Node10Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root6Node10Domains1 root6Node10Domains2 f h1 root6Node10Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root6Node10Domains2 root6Node10Domains3 f h2 root6Node10Step3_checked
  have hb : Covers root6Node10Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node10Domains3 root6Outputs 0
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node11_cover
    · exact root6Node72_cover
  exact hb f h3
theorem root6Node9_cover : Covers root6Node9Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node9Domains0 root6Node9Domains1 f hf root6Node9Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node9Domains1 (.output 4)
    root6Node9Leaf_checked f h1
theorem root6Node8_cover : Covers root6Node8Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node8Domains0 root6Node8Domains1 f hf root6Node8Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node8Domains1 (.output 3)
    root6Node8Leaf_checked f h1
theorem root6Node7_cover : Covers root6Node7Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node7Domains0 root6Node7Domains1 f hf root6Node7Step1_checked
  have hb : Covers root6Node7Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node7Domains1 root6Outputs 58
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node8_cover
    · exact root6Node9_cover
  exact hb f h1
theorem root6Node6_cover : Covers root6Node6Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node6Domains0 root6Node6Domains1 f hf root6Node6Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node6Domains1 (.output 2)
    root6Node6Leaf_checked f h1
theorem root6Node5_cover : Covers root6Node5Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root6Node5Domains0 root6Node5Domains1 f hf root6Node5Step1_checked
  have hb : Covers root6Node5Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node5Domains1 root6Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node6_cover
    · exact root6Node7_cover
  exact hb f h1
theorem root6Node4_cover : Covers root6Node4Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node4Domains0 (.output 1)
    root6Node4Leaf_checked f hf
theorem root6Node3_cover : Covers root6Node3Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node3Domains0 (.output 0)
    root6Node3Leaf_checked f hf
theorem root6Node2_cover : Covers root6Node2Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root6Node2Domains0 root6Node2Domains1 f hf root6Node2Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root6Node2Domains1 root6Node2Domains2 f h1 root6Node2Step2_checked
  have hb : Covers root6Node2Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node2Domains2 root6Outputs 34
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node3_cover
    · exact root6Node4_cover
  exact hb f h2
theorem root6Node1_cover : Covers root6Node1Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root6Node1Domains0 root6Node1Domains1 f hf root6Node1Step1_checked
  have h2 := solution_checkReplacement constraints table20 table20_member
    root6Node1Domains1 root6Node1Domains2 f h1 root6Node1Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root6Node1Domains2 root6Node1Domains3 f h2 root6Node1Step3_checked
  have h4 := solution_checkReplacement constraints table35 table35_member
    root6Node1Domains3 root6Node1Domains4 f h3 root6Node1Step4_checked
  have hb : Covers root6Node1Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node1Domains4 root6Outputs 3
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node2_cover
    · exact root6Node5_cover
  exact hb f h4
theorem root6Node0_cover : Covers root6Node0Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root6Node0Domains0 root6Node0Domains1 f hf root6Node0Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root6Node0Domains1 root6Node0Domains2 f h1 root6Node0Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root6Node0Domains2 root6Node0Domains3 f h2 root6Node0Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root6Node0Domains3 root6Node0Domains4 f h3 root6Node0Step4_checked
  have hb : Covers root6Node0Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node0Domains4 root6Outputs 29
    intro s hs
    change s ∈ [(2,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node1_cover
    · exact root6Node10_cover
  exact hb f h4
theorem root6_table_cover : Covers (domains (6,0)) constraints root6Outputs := root6Node0_cover
theorem root6Family_count : root6Family.length = 44 := rfl
#print axioms root6_table_cover
end SpectreFinite.HexSearch.RadiusFour
