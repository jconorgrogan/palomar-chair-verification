module

public import SpectreFinite.RadiusFourRoot8Part30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root8Node102_cover : Covers root8Node102Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node102Domains0 root8Node102Domains1 f hf root8Node102Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root8Node102Domains1 root8Node102Domains2 f h1 root8Node102Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node102Domains2 (.output 51)
    root8Node102Leaf_checked f h2
theorem root8Node101_cover : Covers root8Node101Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node101Domains0 root8Node101Domains1 f hf root8Node101Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node101Domains1 (.output 50)
    root8Node101Leaf_checked f h1
theorem root8Node100_cover : Covers root8Node100Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node100Domains0 root8Node100Domains1 f hf root8Node100Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node100Domains1 (.output 49)
    root8Node100Leaf_checked f h1
theorem root8Node99_cover : Covers root8Node99Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node99Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node99Domains0 root8Outputs 50
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node100_cover
    · exact root8Node101_cover
  exact hb f hf
theorem root8Node98_cover : Covers root8Node98Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node98Domains0 root8Node98Domains1 f hf root8Node98Step1_checked
  have hb : Covers root8Node98Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node98Domains1 root8Outputs 25
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node99_cover
    · exact root8Node102_cover
  exact hb f h1
theorem root8Node97_cover : Covers root8Node97Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node97Domains0 root8Node97Domains1 f hf root8Node97Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node97Domains1 (.output 48)
    root8Node97Leaf_checked f h1
theorem root8Node96_cover : Covers root8Node96Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node96Domains0 root8Node96Domains1 f hf root8Node96Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node96Domains1 (.output 47)
    root8Node96Leaf_checked f h1
theorem root8Node95_cover : Covers root8Node95Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node95Domains0 root8Node95Domains1 f hf root8Node95Step1_checked
  have hb : Covers root8Node95Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node95Domains1 root8Outputs 50
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node96_cover
    · exact root8Node97_cover
  exact hb f h1
theorem root8Node94_cover : Covers root8Node94Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table20 table20_member
    root8Node94Domains0 root8Node94Domains1 f hf root8Node94Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node94Domains1 root8Node94Domains2 f h1 root8Node94Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root8Node94Domains2 root8Node94Domains3 f h2 root8Node94Step3_checked
  have hb : Covers root8Node94Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node94Domains3 root8Outputs 10
    intro s hs
    change s ∈ [(2,3),(4,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node95_cover
    · exact root8Node98_cover
  exact hb f h3
theorem root8Node93_cover : Covers root8Node93Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node93Domains0 root8Node93Domains1 f hf root8Node93Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root8Node93Domains1 root8Node93Domains2 f h1 root8Node93Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node93Domains2 (.output 46)
    root8Node93Leaf_checked f h2
theorem root8Node92_cover : Covers root8Node92Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node92Domains0 root8Node92Domains1 f hf root8Node92Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node92Domains1 (.output 45)
    root8Node92Leaf_checked f h1
theorem root8Node91_cover : Covers root8Node91Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node91Domains0 root8Node91Domains1 f hf root8Node91Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node91Domains1 (.output 44)
    root8Node91Leaf_checked f h1
theorem root8Node90_cover : Covers root8Node90Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node90Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node90Domains0 root8Outputs 50
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node91_cover
    · exact root8Node92_cover
  exact hb f hf
theorem root8Node89_cover : Covers root8Node89Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node89Domains0 root8Node89Domains1 f hf root8Node89Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root8Node89Domains1 root8Node89Domains2 f h1 root8Node89Step2_checked
  have hb : Covers root8Node89Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node89Domains2 root8Outputs 25
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node90_cover
    · exact root8Node93_cover
  exact hb f h2
theorem root8Node88_cover : Covers root8Node88Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node88Domains0 root8Node88Domains1 f hf root8Node88Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node88Domains1 (.output 43)
    root8Node88Leaf_checked f h1
theorem root8Node87_cover : Covers root8Node87Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node87Domains0 root8Node87Domains1 f hf root8Node87Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node87Domains1 (.output 42)
    root8Node87Leaf_checked f h1
theorem root8Node86_cover : Covers root8Node86Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node86Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node86Domains0 root8Outputs 55
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node87_cover
    · exact root8Node88_cover
  exact hb f hf
theorem root8Node85_cover : Covers root8Node85Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node85Domains0 root8Node85Domains1 f hf root8Node85Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node85Domains1 (.output 41)
    root8Node85Leaf_checked f h1
theorem root8Node84_cover : Covers root8Node84Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node84Domains0 root8Node84Domains1 f hf root8Node84Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node84Domains1 (.output 40)
    root8Node84Leaf_checked f h1
theorem root8Node83_cover : Covers root8Node83Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node83Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node83Domains0 root8Outputs 55
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node84_cover
    · exact root8Node85_cover
  exact hb f hf
theorem root8Node82_cover : Covers root8Node82Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node82Domains0 root8Node82Domains1 f hf root8Node82Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node82Domains1 root8Node82Domains2 f h1 root8Node82Step2_checked
  have hb : Covers root8Node82Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node82Domains2 root8Outputs 25
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node83_cover
    · exact root8Node86_cover
  exact hb f h2
theorem root8Node81_cover : Covers root8Node81Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root8Node81Domains0 root8Node81Domains1 f hf root8Node81Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node81Domains1 root8Node81Domains2 f h1 root8Node81Step2_checked
  have hb : Covers root8Node81Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node81Domains2 root8Outputs 11
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node82_cover
    · exact root8Node89_cover
  exact hb f h2
theorem root8Node80_cover : Covers root8Node80Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node80Domains0 root8Node80Domains1 f hf root8Node80Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node80Domains1 (.output 39)
    root8Node80Leaf_checked f h1
theorem root8Node79_cover : Covers root8Node79Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node79Domains0 root8Node79Domains1 f hf root8Node79Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node79Domains1 (.output 38)
    root8Node79Leaf_checked f h1
theorem root8Node78_cover : Covers root8Node78Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node78Domains0 root8Node78Domains1 f hf root8Node78Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root8Node78Domains1 root8Node78Domains2 f h1 root8Node78Step2_checked
  have hb : Covers root8Node78Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node78Domains2 root8Outputs 50
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node79_cover
    · exact root8Node80_cover
  exact hb f h2
theorem root8Node77_cover : Covers root8Node77Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node77Domains0 root8Node77Domains1 f hf root8Node77Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node77Domains1 (.output 37)
    root8Node77Leaf_checked f h1
theorem root8Node76_cover : Covers root8Node76Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node76Domains0 root8Node76Domains1 f hf root8Node76Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node76Domains1 (.output 36)
    root8Node76Leaf_checked f h1
theorem root8Node75_cover : Covers root8Node75Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node75Domains0 root8Node75Domains1 f hf root8Node75Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root8Node75Domains1 root8Node75Domains2 f h1 root8Node75Step2_checked
  have hb : Covers root8Node75Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node75Domains2 root8Outputs 43
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node76_cover
    · exact root8Node77_cover
  exact hb f h2
theorem root8Node74_cover : Covers root8Node74Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node74Domains0 root8Node74Domains1 f hf root8Node74Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node74Domains1 (.output 35)
    root8Node74Leaf_checked f h1
theorem root8Node73_cover : Covers root8Node73Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node73Domains0 root8Node73Domains1 f hf root8Node73Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node73Domains1 (.output 34)
    root8Node73Leaf_checked f h1
theorem root8Node72_cover : Covers root8Node72Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node72Domains0 root8Node72Domains1 f hf root8Node72Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root8Node72Domains1 root8Node72Domains2 f h1 root8Node72Step2_checked
  have hb : Covers root8Node72Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node72Domains2 root8Outputs 55
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node73_cover
    · exact root8Node74_cover
  exact hb f h2
theorem root8Node71_cover : Covers root8Node71Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node71Domains0 root8Node71Domains1 f hf root8Node71Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node71Domains1 root8Node71Domains2 f h1 root8Node71Step2_checked
  have hb : Covers root8Node71Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node71Domains2 root8Outputs 42
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node72_cover
    · exact root8Node75_cover
  exact hb f h2
theorem root8Node70_cover : Covers root8Node70Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node70Domains0 root8Node70Domains1 f hf root8Node70Step1_checked
  have hb : Covers root8Node70Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node70Domains1 root8Outputs 11
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node71_cover
    · exact root8Node78_cover
  exact hb f h1
theorem root8Node69_cover : Covers root8Node69Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root8Node69Domains0 root8Node69Domains1 f hf root8Node69Step1_checked
  have hb : Covers root8Node69Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node69Domains1 root8Outputs 10
    intro s hs
    change s ∈ [(2,3),(4,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node70_cover
    · exact root8Node81_cover
  exact hb f h1
theorem root8Node68_cover : Covers root8Node68Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root8Node68Domains0 root8Node68Domains1 f hf root8Node68Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root8Node68Domains1 root8Node68Domains2 f h1 root8Node68Step2_checked
  have h3 := solution_checkReplacement constraints table4 table4_member
    root8Node68Domains2 root8Node68Domains3 f h2 root8Node68Step3_checked
  have hb : Covers root8Node68Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node68Domains3 root8Outputs 0
    intro s hs
    change s ∈ [(0,2),(1,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node69_cover
    · exact root8Node94_cover
  exact hb f h3
theorem root8Node67_cover : Covers root8Node67Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node67Domains0 root8Node67Domains1 f hf root8Node67Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node67Domains1 (.output 33)
    root8Node67Leaf_checked f h1
theorem root8Node66_cover : Covers root8Node66Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node66Domains0 root8Node66Domains1 f hf root8Node66Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node66Domains1 (.output 32)
    root8Node66Leaf_checked f h1
theorem root8Node65_cover : Covers root8Node65Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node65Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node65Domains0 root8Outputs 43
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node66_cover
    · exact root8Node67_cover
  exact hb f hf
theorem root8Node64_cover : Covers root8Node64Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table20 table20_member
    root8Node64Domains0 root8Node64Domains1 f hf root8Node64Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node64Domains1 root8Node64Domains2 f h1 root8Node64Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node64Domains2 (.output 31)
    root8Node64Leaf_checked f h2
theorem root8Node63_cover : Covers root8Node63Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root8Node63Domains0 root8Node63Domains1 f hf root8Node63Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root8Node63Domains1 root8Node63Domains2 f h1 root8Node63Step2_checked
  have h3 := solution_checkReplacement constraints table36 table36_member
    root8Node63Domains2 root8Node63Domains3 f h2 root8Node63Step3_checked
  have hb : Covers root8Node63Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node63Domains3 root8Outputs 0
    intro s hs
    change s ∈ [(1,0),(6,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node64_cover
    · exact root8Node65_cover
  exact hb f h3
theorem root8Node62_cover : Covers root8Node62Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node62Domains0 root8Node62Domains1 f hf root8Node62Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node62Domains1 (.output 30)
    root8Node62Leaf_checked f h1
theorem root8Node61_cover : Covers root8Node61Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node61Domains0 root8Node61Domains1 f hf root8Node61Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node61Domains1 (.output 29)
    root8Node61Leaf_checked f h1
theorem root8Node60_cover : Covers root8Node60Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root8Node60Domains0 root8Node60Domains1 f hf root8Node60Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node60Domains1 root8Node60Domains2 f h1 root8Node60Step2_checked
  have hb : Covers root8Node60Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node60Domains2 root8Outputs 55
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node61_cover
    · exact root8Node62_cover
  exact hb f h2
theorem root8Node59_cover : Covers root8Node59Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node59Domains0 root8Node59Domains1 f hf root8Node59Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node59Domains1 (.output 28)
    root8Node59Leaf_checked f h1
theorem root8Node58_cover : Covers root8Node58Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node58Domains0 root8Node58Domains1 f hf root8Node58Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node58Domains1 (.output 27)
    root8Node58Leaf_checked f h1
theorem root8Node57_cover : Covers root8Node57Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root8Node57Domains0 root8Node57Domains1 f hf root8Node57Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node57Domains1 root8Node57Domains2 f h1 root8Node57Step2_checked
  have hb : Covers root8Node57Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node57Domains2 root8Outputs 43
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node58_cover
    · exact root8Node59_cover
  exact hb f h2
theorem root8Node56_cover : Covers root8Node56Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root8Node56Domains0 root8Node56Domains1 f hf root8Node56Step1_checked
  have hb : Covers root8Node56Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node56Domains1 root8Outputs 10
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node57_cover
    · exact root8Node60_cover
  exact hb f h1
theorem root8Node55_cover : Covers root8Node55Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node55Domains0 root8Node55Domains1 f hf root8Node55Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node55Domains1 (.output 26)
    root8Node55Leaf_checked f h1
theorem root8Node54_cover : Covers root8Node54Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node54Domains0 root8Node54Domains1 f hf root8Node54Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node54Domains1 (.output 25)
    root8Node54Leaf_checked f h1
theorem root8Node53_cover : Covers root8Node53Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root8Node53Domains0 root8Node53Domains1 f hf root8Node53Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node53Domains1 root8Node53Domains2 f h1 root8Node53Step2_checked
  have hb : Covers root8Node53Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node53Domains2 root8Outputs 55
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node54_cover
    · exact root8Node55_cover
  exact hb f h2
theorem root8Node52_cover : Covers root8Node52Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node52Domains0 root8Node52Domains1 f hf root8Node52Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node52Domains1 (.output 24)
    root8Node52Leaf_checked f h1
theorem root8Node51_cover : Covers root8Node51Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root8Node51Domains0 root8Node51Domains1 f hf root8Node51Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node51Domains1 (.output 23)
    root8Node51Leaf_checked f h1
theorem root8Node50_cover : Covers root8Node50Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root8Node50Domains0 root8Node50Domains1 f hf root8Node50Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node50Domains1 root8Node50Domains2 f h1 root8Node50Step2_checked
  have hb : Covers root8Node50Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node50Domains2 root8Outputs 43
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node51_cover
    · exact root8Node52_cover
  exact hb f h2
theorem root8Node49_cover : Covers root8Node49Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root8Node49Domains0 root8Node49Domains1 f hf root8Node49Step1_checked
  have hb : Covers root8Node49Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node49Domains1 root8Outputs 10
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node50_cover
    · exact root8Node53_cover
  exact hb f h1
theorem root8Node48_cover : Covers root8Node48Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root8Node48Domains0 root8Node48Domains1 f hf root8Node48Step1_checked
  have hb : Covers root8Node48Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node48Domains1 root8Outputs 5
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node49_cover
    · exact root8Node56_cover
  exact hb f h1
theorem root8Node47_cover : Covers root8Node47Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root8Node47Domains0 root8Node47Domains1 f hf root8Node47Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node47Domains1 root8Node47Domains2 f h1 root8Node47Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root8Node47Domains2 root8Node47Domains3 f h2 root8Node47Step3_checked
  have hb : Covers root8Node47Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node47Domains3 root8Outputs 1
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node48_cover
    · exact root8Node63_cover
  exact hb f h3
theorem root8Node46_cover : Covers root8Node46Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root8Node46Domains0 root8Node46Domains1 f hf root8Node46Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root8Node46Domains1 root8Node46Domains2 f h1 root8Node46Step2_checked
  have h3 := solution_checkReplacement constraints table18 table18_member
    root8Node46Domains2 root8Node46Domains3 f h2 root8Node46Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root8Node46Domains3 root8Node46Domains4 f h3 root8Node46Step4_checked
  have hb : Covers root8Node46Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node46Domains4 root8Outputs 7
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node47_cover
    · exact root8Node68_cover
  exact hb f h4
theorem root8Node45_cover : Covers root8Node45Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node45Domains0 root8Node45Domains1 f hf root8Node45Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root8Node45Domains1 root8Node45Domains2 f h1 root8Node45Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node45Domains2 (.output 22)
    root8Node45Leaf_checked f h2
theorem root8Node44_cover : Covers root8Node44Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node44Domains0 root8Node44Domains1 f hf root8Node44Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node44Domains1 (.output 21)
    root8Node44Leaf_checked f h1
theorem root8Node43_cover : Covers root8Node43Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root8Node43Domains0 root8Node43Domains1 f hf root8Node43Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node43Domains1 (.output 20)
    root8Node43Leaf_checked f h1
theorem root8Node42_cover : Covers root8Node42Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node42Domains0 root8Node42Domains1 f hf root8Node42Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node42Domains1 root8Node42Domains2 f h1 root8Node42Step2_checked
  have hb : Covers root8Node42Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node42Domains2 root8Outputs 55
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node43_cover
    · exact root8Node44_cover
  exact hb f h2
theorem root8Node41_cover : Covers root8Node41Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node41Domains0 root8Node41Domains1 f hf root8Node41Step1_checked
  have hb : Covers root8Node41Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node41Domains1 root8Outputs 18
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node42_cover
    · exact root8Node45_cover
  exact hb f h1
theorem root8Node40_cover : Covers root8Node40Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node40Domains0 root8Node40Domains1 f hf root8Node40Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node40Domains1 (.output 19)
    root8Node40Leaf_checked f h1
theorem root8Node39_cover : Covers root8Node39Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node39Domains0 root8Node39Domains1 f hf root8Node39Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node39Domains1 (.output 18)
    root8Node39Leaf_checked f h1
theorem root8Node38_cover : Covers root8Node38Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node38Domains0 root8Node38Domains1 f hf root8Node38Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node38Domains1 root8Node38Domains2 f h1 root8Node38Step2_checked
  have hb : Covers root8Node38Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node38Domains2 root8Outputs 33
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node39_cover
    · exact root8Node40_cover
  exact hb f h2
theorem root8Node37_cover : Covers root8Node37Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node37Domains0 root8Node37Domains1 f hf root8Node37Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node37Domains1 (.output 17)
    root8Node37Leaf_checked f h1
theorem root8Node36_cover : Covers root8Node36Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node36Domains0 root8Node36Domains1 f hf root8Node36Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node36Domains1 (.output 16)
    root8Node36Leaf_checked f h1
theorem root8Node35_cover : Covers root8Node35Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node35Domains0 root8Node35Domains1 f hf root8Node35Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node35Domains1 root8Node35Domains2 f h1 root8Node35Step2_checked
  have hb : Covers root8Node35Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node35Domains2 root8Outputs 33
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node36_cover
    · exact root8Node37_cover
  exact hb f h2
theorem root8Node34_cover : Covers root8Node34Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node34Domains0 root8Node34Domains1 f hf root8Node34Step1_checked
  have hb : Covers root8Node34Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node34Domains1 root8Outputs 18
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node35_cover
    · exact root8Node38_cover
  exact hb f h1
theorem root8Node33_cover : Covers root8Node33Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root8Node33Domains0 root8Node33Domains1 f hf root8Node33Step1_checked
  have hb : Covers root8Node33Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node33Domains1 root8Outputs 17
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node34_cover
    · exact root8Node41_cover
  exact hb f h1
theorem root8Node32_cover : Covers root8Node32Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node32Domains0 root8Node32Domains1 f hf root8Node32Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node32Domains1 root8Node32Domains2 f h1 root8Node32Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node32Domains2 (.output 15)
    root8Node32Leaf_checked f h2
theorem root8Node31_cover : Covers root8Node31Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node31Domains0 root8Node31Domains1 f hf root8Node31Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node31Domains1 root8Node31Domains2 f h1 root8Node31Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node31Domains2 (.output 14)
    root8Node31Leaf_checked f h2
theorem root8Node30_cover : Covers root8Node30Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node30Domains0 root8Node30Domains1 f hf root8Node30Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root8Node30Domains1 root8Node30Domains2 f h1 root8Node30Step2_checked
  have hb : Covers root8Node30Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node30Domains2 root8Outputs 18
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node31_cover
    · exact root8Node32_cover
  exact hb f h2
theorem root8Node29_cover : Covers root8Node29Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node29Domains0 root8Node29Domains1 f hf root8Node29Step1_checked
  have hb : Covers root8Node29Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node29Domains1 root8Outputs 3
    intro s hs
    change s ∈ [(1,5),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node30_cover
    · exact root8Node33_cover
  exact hb f h1
theorem root8Node28_cover : Covers root8Node28Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node28Domains0 root8Node28Domains1 f hf root8Node28Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node28Domains1 root8Node28Domains2 f h1 root8Node28Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node28Domains2 (.output 13)
    root8Node28Leaf_checked f h2
theorem root8Node27_cover : Covers root8Node27Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node27Domains0 root8Node27Domains1 f hf root8Node27Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root8Node27Domains1 root8Node27Domains2 f h1 root8Node27Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node27Domains2 (.output 12)
    root8Node27Leaf_checked f h2
theorem root8Node26_cover : Covers root8Node26Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node26Domains0 root8Node26Domains1 f hf root8Node26Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root8Node26Domains1 root8Node26Domains2 f h1 root8Node26Step2_checked
  have hb : Covers root8Node26Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node26Domains2 root8Outputs 18
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node27_cover
    · exact root8Node28_cover
  exact hb f h2
theorem root8Node25_cover : Covers root8Node25Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root8Node25Domains0 root8Node25Domains1 f hf root8Node25Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root8Node25Domains1 root8Node25Domains2 f h1 root8Node25Step2_checked
  have hb : Covers root8Node25Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node25Domains2 root8Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node26_cover
    · exact root8Node29_cover
  exact hb f h2
theorem root8Node24_cover : Covers root8Node24Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node24Domains0 root8Node24Domains1 f hf root8Node24Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node24Domains1 (.output 11)
    root8Node24Leaf_checked f h1
theorem root8Node23_cover : Covers root8Node23Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node23Domains0 root8Node23Domains1 f hf root8Node23Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node23Domains1 (.output 10)
    root8Node23Leaf_checked f h1
theorem root8Node22_cover : Covers root8Node22Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node22Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node22Domains0 root8Outputs 50
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node23_cover
    · exact root8Node24_cover
  exact hb f hf
theorem root8Node21_cover : Covers root8Node21Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node21Domains0 root8Node21Domains1 f hf root8Node21Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node21Domains1 (.output 9)
    root8Node21Leaf_checked f h1
theorem root8Node20_cover : Covers root8Node20Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root8Node20Domains0 root8Node20Domains1 f hf root8Node20Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node20Domains1 (.output 8)
    root8Node20Leaf_checked f h1
theorem root8Node19_cover : Covers root8Node19Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node19Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node19Domains0 root8Outputs 50
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node20_cover
    · exact root8Node21_cover
  exact hb f hf
theorem root8Node18_cover : Covers root8Node18Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node18Domains0 root8Node18Domains1 f hf root8Node18Step1_checked
  have hb : Covers root8Node18Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node18Domains1 root8Outputs 26
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node19_cover
    · exact root8Node22_cover
  exact hb f h1
theorem root8Node17_cover : Covers root8Node17Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node17Domains0 (.output 7)
    root8Node17Leaf_checked f hf
theorem root8Node16_cover : Covers root8Node16Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node16Domains0 (.output 6)
    root8Node16Leaf_checked f hf
theorem root8Node15_cover : Covers root8Node15Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node15Domains0 root8Node15Domains1 f hf root8Node15Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root8Node15Domains1 root8Node15Domains2 f h1 root8Node15Step2_checked
  have hb : Covers root8Node15Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node15Domains2 root8Outputs 26
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node16_cover
    · exact root8Node17_cover
  exact hb f h2
theorem root8Node14_cover : Covers root8Node14Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table18 table18_member
    root8Node14Domains0 root8Node14Domains1 f hf root8Node14Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node14Domains1 root8Node14Domains2 f h1 root8Node14Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root8Node14Domains2 root8Node14Domains3 f h2 root8Node14Step3_checked
  have hb : Covers root8Node14Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node14Domains3 root8Outputs 17
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node15_cover
    · exact root8Node18_cover
  exact hb f h3
theorem root8Node13_cover : Covers root8Node13Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node13Domains0 root8Node13Domains1 f hf root8Node13Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node13Domains1 (.output 5)
    root8Node13Leaf_checked f h1
theorem root8Node12_cover : Covers root8Node12Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node12Domains0 root8Node12Domains1 f hf root8Node12Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node12Domains1 (.output 4)
    root8Node12Leaf_checked f h1
theorem root8Node11_cover : Covers root8Node11Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node11Domains0 root8Node11Domains1 f hf root8Node11Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node11Domains1 (.output 3)
    root8Node11Leaf_checked f h1
theorem root8Node10_cover : Covers root8Node10Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root8Node10Domains0 root8Node10Domains1 f hf root8Node10Step1_checked
  have hb : Covers root8Node10Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node10Domains1 root8Outputs 33
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node11_cover
    · exact root8Node12_cover
  exact hb f h1
theorem root8Node9_cover : Covers root8Node9Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table27 table27_member
    root8Node9Domains0 root8Node9Domains1 f hf root8Node9Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root8Node9Domains1 root8Node9Domains2 f h1 root8Node9Step2_checked
  have hb : Covers root8Node9Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node9Domains2 root8Outputs 17
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node10_cover
    · exact root8Node13_cover
  exact hb f h2
theorem root8Node8_cover : Covers root8Node8Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node8Domains0 root8Node8Domains1 f hf root8Node8Step1_checked
  have hb : Covers root8Node8Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node8Domains1 root8Outputs 5
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node9_cover
    · exact root8Node14_cover
  exact hb f h1
theorem root8Node7_cover : Covers root8Node7Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node7Domains0 (.output 2)
    root8Node7Leaf_checked f hf
theorem root8Node6_cover : Covers root8Node6Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node6Domains0 (.output 1)
    root8Node6Leaf_checked f hf
theorem root8Node5_cover : Covers root8Node5Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table28 table28_member
    root8Node5Domains0 root8Node5Domains1 f hf root8Node5Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root8Node5Domains1 root8Node5Domains2 f h1 root8Node5Step2_checked
  have hb : Covers root8Node5Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node5Domains2 root8Outputs 26
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node6_cover
    · exact root8Node7_cover
  exact hb f h2
theorem root8Node4_cover : Covers root8Node4Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table27 table27_member
    root8Node4Domains0 root8Node4Domains1 f hf root8Node4Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root8Node4Domains1 root8Node4Domains2 f h1 root8Node4Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node4Domains2 (.output 0)
    root8Node4Leaf_checked f h2
theorem root8Node3_cover : Covers root8Node3Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root8Node3Domains0 root8Node3Domains1 f hf root8Node3Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root8Node3Domains1 root8Node3Domains2 f h1 root8Node3Step2_checked
  have hb : Covers root8Node3Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node3Domains2 root8Outputs 5
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node4_cover
    · exact root8Node5_cover
  exact hb f h2
theorem root8Node2_cover : Covers root8Node2Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root8Node2Domains0 root8Node2Domains1 f hf root8Node2Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root8Node2Domains1 root8Node2Domains2 f h1 root8Node2Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root8Node2Domains2 root8Node2Domains3 f h2 root8Node2Step3_checked
  have h4 := solution_checkReplacement constraints table35 table35_member
    root8Node2Domains3 root8Node2Domains4 f h3 root8Node2Step4_checked
  have hb : Covers root8Node2Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node2Domains4 root8Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node3_cover
    · exact root8Node8_cover
  exact hb f h4
theorem root8Node1_cover : Covers root8Node1Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root8Node1Domains0 root8Node1Domains1 f hf root8Node1Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root8Node1Domains1 root8Node1Domains2 f h1 root8Node1Step2_checked
  have h3 := solution_checkReplacement constraints table36 table36_member
    root8Node1Domains2 root8Node1Domains3 f h2 root8Node1Step3_checked
  have hb : Covers root8Node1Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node1Domains3 root8Outputs 0
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node2_cover
    · exact root8Node25_cover
  exact hb f h3
theorem root8Node0_cover : Covers root8Node0Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root8Node0Domains0 root8Node0Domains1 f hf root8Node0Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root8Node0Domains1 root8Node0Domains2 f h1 root8Node0Step2_checked
  have h3 := solution_checkReplacement constraints table14 table14_member
    root8Node0Domains2 root8Node0Domains3 f h2 root8Node0Step3_checked
  have h4 := solution_checkReplacement constraints table11 table11_member
    root8Node0Domains3 root8Node0Domains4 f h3 root8Node0Step4_checked
  have h5 := solution_checkReplacement constraints table16 table16_member
    root8Node0Domains4 root8Node0Domains5 f h4 root8Node0Step5_checked
  have hb : Covers root8Node0Domains5 constraints root8Outputs := by
    apply covers_of_branches root8Node0Domains5 root8Outputs 22
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node1_cover
    · exact root8Node46_cover
  exact hb f h5
theorem root8_table_cover : Covers (domains (8,0)) constraints root8Outputs := root8Node0_cover
theorem root8Family_count : root8Family.length = 52 := rfl
#print axioms root8_table_cover
end SpectreFinite.HexSearch.RadiusFour
