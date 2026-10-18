module

public import SpectreFinite.RadiusFiveRoot6Part50

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root6Node124_cover : Covers root6Node124Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node124Domains0 root6Node124Domains1 f hf root6Node124Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node124Domains1 (.output 62)
    root6Node124Leaf_checked f h1
theorem root6Node123_cover : Covers root6Node123Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node123Domains0 root6Node123Domains1 f hf root6Node123Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node123Domains1 (.output 61)
    root6Node123Leaf_checked f h1
theorem root6Node122_cover : Covers root6Node122Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node122Domains0 root6Node122Domains1 f hf root6Node122Step1_checked
  have hb : Covers root6Node122Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node122Domains1 root6Outputs 78
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node123_cover
    · exact root6Node124_cover
  exact hb f h1
theorem root6Node121_cover : Covers root6Node121Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node121Domains0 root6Node121Domains1 f hf root6Node121Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root6Node121Domains1 root6Node121Domains2 f h1 root6Node121Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node121Domains2 (.output 60)
    root6Node121Leaf_checked f h2
theorem root6Node120_cover : Covers root6Node120Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node120Domains0 root6Node120Domains1 f hf root6Node120Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node120Domains1 root6Node120Domains2 f h1 root6Node120Step2_checked
  have hb : Covers root6Node120Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node120Domains2 root6Outputs 20
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node121_cover
    · exact root6Node122_cover
  exact hb f h2
theorem root6Node119_cover : Covers root6Node119Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node119Domains0 root6Node119Domains1 f hf root6Node119Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node119Domains1 (.output 59)
    root6Node119Leaf_checked f h1
theorem root6Node118_cover : Covers root6Node118Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node118Domains0 root6Node118Domains1 f hf root6Node118Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node118Domains1 (.output 58)
    root6Node118Leaf_checked f h1
theorem root6Node117_cover : Covers root6Node117Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node117Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node117Domains0 root6Outputs 81
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node118_cover
    · exact root6Node119_cover
  exact hb f hf
theorem root6Node116_cover : Covers root6Node116Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node116Domains0 root6Node116Domains1 f hf root6Node116Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node116Domains1 (.output 57)
    root6Node116Leaf_checked f h1
theorem root6Node115_cover : Covers root6Node115Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node115Domains0 root6Node115Domains1 f hf root6Node115Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node115Domains1 (.output 56)
    root6Node115Leaf_checked f h1
theorem root6Node114_cover : Covers root6Node114Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node114Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node114Domains0 root6Outputs 81
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node115_cover
    · exact root6Node116_cover
  exact hb f hf
theorem root6Node113_cover : Covers root6Node113Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node113Domains0 root6Node113Domains1 f hf root6Node113Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root6Node113Domains1 root6Node113Domains2 f h1 root6Node113Step2_checked
  have hb : Covers root6Node113Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node113Domains2 root6Outputs 40
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node114_cover
    · exact root6Node117_cover
  exact hb f h2
theorem root6Node112_cover : Covers root6Node112Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node112Domains0 root6Node112Domains1 f hf root6Node112Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root6Node112Domains1 root6Node112Domains2 f h1 root6Node112Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root6Node112Domains2 root6Node112Domains3 f h2 root6Node112Step3_checked
  have hb : Covers root6Node112Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node112Domains3 root6Outputs 13
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node113_cover
    · exact root6Node120_cover
  exact hb f h3
theorem root6Node111_cover : Covers root6Node111Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node111Domains0 root6Node111Domains1 f hf root6Node111Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node111Domains1 root6Node111Domains2 f h1 root6Node111Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node111Domains2 (.output 55)
    root6Node111Leaf_checked f h2
theorem root6Node110_cover : Covers root6Node110Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node110Domains0 root6Node110Domains1 f hf root6Node110Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node110Domains1 (.output 54)
    root6Node110Leaf_checked f h1
theorem root6Node109_cover : Covers root6Node109Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node109Domains0 root6Node109Domains1 f hf root6Node109Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node109Domains1 (.output 53)
    root6Node109Leaf_checked f h1
theorem root6Node108_cover : Covers root6Node108Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node108Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node108Domains0 root6Outputs 81
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node109_cover
    · exact root6Node110_cover
  exact hb f hf
theorem root6Node107_cover : Covers root6Node107Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node107Domains0 root6Node107Domains1 f hf root6Node107Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node107Domains1 (.output 52)
    root6Node107Leaf_checked f h1
theorem root6Node106_cover : Covers root6Node106Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node106Domains0 root6Node106Domains1 f hf root6Node106Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node106Domains1 (.output 51)
    root6Node106Leaf_checked f h1
theorem root6Node105_cover : Covers root6Node105Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node105Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node105Domains0 root6Outputs 81
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node106_cover
    · exact root6Node107_cover
  exact hb f hf
theorem root6Node104_cover : Covers root6Node104Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table53 table53_member
    root6Node104Domains0 root6Node104Domains1 f hf root6Node104Step1_checked
  have hb : Covers root6Node104Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node104Domains1 root6Outputs 40
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node105_cover
    · exact root6Node108_cover
  exact hb f h1
theorem root6Node103_cover : Covers root6Node103Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root6Node103Domains0 root6Node103Domains1 f hf root6Node103Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root6Node103Domains1 root6Node103Domains2 f h1 root6Node103Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root6Node103Domains2 root6Node103Domains3 f h2 root6Node103Step3_checked
  have hb : Covers root6Node103Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node103Domains3 root6Outputs 13
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node104_cover
    · exact root6Node111_cover
  exact hb f h3
theorem root6Node102_cover : Covers root6Node102Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node102Domains0 root6Node102Domains1 f hf root6Node102Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node102Domains1 root6Node102Domains2 f h1 root6Node102Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node102Domains2 (.output 50)
    root6Node102Leaf_checked f h2
theorem root6Node101_cover : Covers root6Node101Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node101Domains0 root6Node101Domains1 f hf root6Node101Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node101Domains1 root6Node101Domains2 f h1 root6Node101Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node101Domains2 (.output 49)
    root6Node101Leaf_checked f h2
theorem root6Node100_cover : Covers root6Node100Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node100Domains0 root6Node100Domains1 f hf root6Node100Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root6Node100Domains1 root6Node100Domains2 f h1 root6Node100Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node100Domains2 (.output 48)
    root6Node100Leaf_checked f h2
theorem root6Node99_cover : Covers root6Node99Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node99Domains0 root6Node99Domains1 f hf root6Node99Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node99Domains1 (.output 47)
    root6Node99Leaf_checked f h1
theorem root6Node98_cover : Covers root6Node98Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node98Domains0 root6Node98Domains1 f hf root6Node98Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node98Domains1 (.output 46)
    root6Node98Leaf_checked f h1
theorem root6Node97_cover : Covers root6Node97Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node97Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node97Domains0 root6Outputs 81
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node98_cover
    · exact root6Node99_cover
  exact hb f hf
theorem root6Node96_cover : Covers root6Node96Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root6Node96Domains0 root6Node96Domains1 f hf root6Node96Step1_checked
  have hb : Covers root6Node96Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node96Domains1 root6Outputs 50
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node97_cover
    · exact root6Node100_cover
  exact hb f h1
theorem root6Node95_cover : Covers root6Node95Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root6Node95Domains0 root6Node95Domains1 f hf root6Node95Step1_checked
  have hb : Covers root6Node95Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node95Domains1 root6Outputs 30
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node96_cover
    · exact root6Node101_cover
  exact hb f h1
theorem root6Node94_cover : Covers root6Node94Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root6Node94Domains0 root6Node94Domains1 f hf root6Node94Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node94Domains1 root6Node94Domains2 f h1 root6Node94Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root6Node94Domains2 root6Node94Domains3 f h2 root6Node94Step3_checked
  have hb : Covers root6Node94Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node94Domains3 root6Outputs 13
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node95_cover
    · exact root6Node102_cover
  exact hb f h3
theorem root6Node93_cover : Covers root6Node93Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node93Domains0 root6Node93Domains1 f hf root6Node93Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root6Node93Domains1 root6Node93Domains2 f h1 root6Node93Step2_checked
  have hb : Covers root6Node93Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node93Domains2 root6Outputs 8
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node94_cover
    · exact root6Node103_cover
  exact hb f h2
theorem root6Node92_cover : Covers root6Node92Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node92Domains0 root6Node92Domains1 f hf root6Node92Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node92Domains1 (.output 45)
    root6Node92Leaf_checked f h1
theorem root6Node91_cover : Covers root6Node91Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node91Domains0 root6Node91Domains1 f hf root6Node91Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node91Domains1 (.output 44)
    root6Node91Leaf_checked f h1
theorem root6Node90_cover : Covers root6Node90Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node90Domains0 root6Node90Domains1 f hf root6Node90Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node90Domains1 root6Node90Domains2 f h1 root6Node90Step2_checked
  have hb : Covers root6Node90Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node90Domains2 root6Outputs 85
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node91_cover
    · exact root6Node92_cover
  exact hb f h2
theorem root6Node89_cover : Covers root6Node89Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node89Domains0 root6Node89Domains1 f hf root6Node89Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node89Domains1 (.output 43)
    root6Node89Leaf_checked f h1
theorem root6Node88_cover : Covers root6Node88Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node88Domains0 root6Node88Domains1 f hf root6Node88Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node88Domains1 (.output 42)
    root6Node88Leaf_checked f h1
theorem root6Node87_cover : Covers root6Node87Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node87Domains0 root6Node87Domains1 f hf root6Node87Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node87Domains1 root6Node87Domains2 f h1 root6Node87Step2_checked
  have hb : Covers root6Node87Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node87Domains2 root6Outputs 85
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node88_cover
    · exact root6Node89_cover
  exact hb f h2
theorem root6Node86_cover : Covers root6Node86Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node86Domains0 root6Node86Domains1 f hf root6Node86Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root6Node86Domains1 root6Node86Domains2 f h1 root6Node86Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node86Domains2 (.output 41)
    root6Node86Leaf_checked f h2
theorem root6Node85_cover : Covers root6Node85Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node85Domains0 root6Node85Domains1 f hf root6Node85Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root6Node85Domains1 root6Node85Domains2 f h1 root6Node85Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node85Domains2 (.output 40)
    root6Node85Leaf_checked f h2
theorem root6Node84_cover : Covers root6Node84Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root6Node84Domains0 root6Node84Domains1 f hf root6Node84Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node84Domains1 root6Node84Domains2 f h1 root6Node84Step2_checked
  have hb : Covers root6Node84Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node84Domains2 root6Outputs 50
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node85_cover
    · exact root6Node86_cover
  exact hb f h2
theorem root6Node83_cover : Covers root6Node83Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root6Node83Domains0 root6Node83Domains1 f hf root6Node83Step1_checked
  have hb : Covers root6Node83Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node83Domains1 root6Outputs 30
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node84_cover
    · exact root6Node87_cover
  exact hb f h1
theorem root6Node82_cover : Covers root6Node82Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root6Node82Domains0 root6Node82Domains1 f hf root6Node82Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root6Node82Domains1 root6Node82Domains2 f h1 root6Node82Step2_checked
  have h3 := solution_checkReplacement constraints table36 table36_member
    root6Node82Domains2 root6Node82Domains3 f h2 root6Node82Step3_checked
  have hb : Covers root6Node82Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node82Domains3 root6Outputs 13
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node83_cover
    · exact root6Node90_cover
  exact hb f h3
theorem root6Node81_cover : Covers root6Node81Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root6Node81Domains0 root6Node81Domains1 f hf root6Node81Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root6Node81Domains1 root6Node81Domains2 f h1 root6Node81Step2_checked
  have hb : Covers root6Node81Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node81Domains2 root6Outputs 5
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node82_cover
    · exact root6Node93_cover
  exact hb f h2
theorem root6Node80_cover : Covers root6Node80Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root6Node80Domains0 root6Node80Domains1 f hf root6Node80Step1_checked
  have hb : Covers root6Node80Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node80Domains1 root6Outputs 3
    intro s hs
    change s ∈ [(1,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node81_cover
    · exact root6Node112_cover
  exact hb f h1
theorem root6Node79_cover : Covers root6Node79Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node79Domains0 root6Node79Domains1 f hf root6Node79Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root6Node79Domains1 root6Node79Domains2 f h1 root6Node79Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node79Domains2 (.output 39)
    root6Node79Leaf_checked f h2
theorem root6Node78_cover : Covers root6Node78Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node78Domains0 root6Node78Domains1 f hf root6Node78Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node78Domains1 (.output 38)
    root6Node78Leaf_checked f h1
theorem root6Node77_cover : Covers root6Node77Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node77Domains0 root6Node77Domains1 f hf root6Node77Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node77Domains1 (.output 37)
    root6Node77Leaf_checked f h1
theorem root6Node76_cover : Covers root6Node76Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node76Domains0 root6Node76Domains1 f hf root6Node76Step1_checked
  have hb : Covers root6Node76Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node76Domains1 root6Outputs 85
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node77_cover
    · exact root6Node78_cover
  exact hb f h1
theorem root6Node75_cover : Covers root6Node75Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root6Node75Domains0 root6Node75Domains1 f hf root6Node75Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root6Node75Domains1 root6Node75Domains2 f h1 root6Node75Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root6Node75Domains2 root6Node75Domains3 f h2 root6Node75Step3_checked
  have hb : Covers root6Node75Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node75Domains3 root6Outputs 5
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node76_cover
    · exact root6Node79_cover
  exact hb f h3
theorem root6Node74_cover : Covers root6Node74Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root6Node74Domains0 root6Node74Domains1 f hf root6Node74Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node74Domains1 root6Node74Domains2 f h1 root6Node74Step2_checked
  have h3 := solution_checkReplacement constraints table2 table2_member
    root6Node74Domains2 root6Node74Domains3 f h2 root6Node74Step3_checked
  have h4 := solution_checkReplacement constraints table52 table52_member
    root6Node74Domains3 root6Node74Domains4 f h3 root6Node74Step4_checked
  have hb : Covers root6Node74Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node74Domains4 root6Outputs 1
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node75_cover
    · exact root6Node80_cover
  exact hb f h4
theorem root6Node73_cover : Covers root6Node73Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node73Domains0 root6Node73Domains1 f hf root6Node73Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node73Domains1 (.output 36)
    root6Node73Leaf_checked f h1
theorem root6Node72_cover : Covers root6Node72Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node72Domains0 root6Node72Domains1 f hf root6Node72Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node72Domains1 (.output 35)
    root6Node72Leaf_checked f h1
theorem root6Node71_cover : Covers root6Node71Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node71Domains0 root6Node71Domains1 f hf root6Node71Step1_checked
  have hb : Covers root6Node71Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node71Domains1 root6Outputs 84
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node72_cover
    · exact root6Node73_cover
  exact hb f h1
theorem root6Node70_cover : Covers root6Node70Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node70Domains0 root6Node70Domains1 f hf root6Node70Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node70Domains1 (.output 34)
    root6Node70Leaf_checked f h1
theorem root6Node69_cover : Covers root6Node69Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node69Domains0 root6Node69Domains1 f hf root6Node69Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node69Domains1 (.output 33)
    root6Node69Leaf_checked f h1
theorem root6Node68_cover : Covers root6Node68Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node68Domains0 root6Node68Domains1 f hf root6Node68Step1_checked
  have hb : Covers root6Node68Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node68Domains1 root6Outputs 84
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node69_cover
    · exact root6Node70_cover
  exact hb f h1
theorem root6Node67_cover : Covers root6Node67Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node67Domains0 root6Node67Domains1 f hf root6Node67Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root6Node67Domains1 root6Node67Domains2 f h1 root6Node67Step2_checked
  have hb : Covers root6Node67Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node67Domains2 root6Outputs 29
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node68_cover
    · exact root6Node71_cover
  exact hb f h2
theorem root6Node66_cover : Covers root6Node66Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node66Domains0 root6Node66Domains1 f hf root6Node66Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root6Node66Domains1 root6Node66Domains2 f h1 root6Node66Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node66Domains2 (.output 32)
    root6Node66Leaf_checked f h2
theorem root6Node65_cover : Covers root6Node65Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node65Domains0 root6Node65Domains1 f hf root6Node65Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node65Domains1 (.output 31)
    root6Node65Leaf_checked f h1
theorem root6Node64_cover : Covers root6Node64Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node64Domains0 root6Node64Domains1 f hf root6Node64Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node64Domains1 (.output 30)
    root6Node64Leaf_checked f h1
theorem root6Node63_cover : Covers root6Node63Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node63Domains0 root6Node63Domains1 f hf root6Node63Step1_checked
  have hb : Covers root6Node63Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node63Domains1 root6Outputs 78
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node64_cover
    · exact root6Node65_cover
  exact hb f h1
theorem root6Node62_cover : Covers root6Node62Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node62Domains0 root6Node62Domains1 f hf root6Node62Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node62Domains1 root6Node62Domains2 f h1 root6Node62Step2_checked
  have hb : Covers root6Node62Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node62Domains2 root6Outputs 29
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node63_cover
    · exact root6Node66_cover
  exact hb f h2
theorem root6Node61_cover : Covers root6Node61Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node61Domains0 root6Node61Domains1 f hf root6Node61Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root6Node61Domains1 root6Node61Domains2 f h1 root6Node61Step2_checked
  have hb : Covers root6Node61Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node61Domains2 root6Outputs 21
    intro s hs
    change s ∈ [(2,2),(2,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node62_cover
    · exact root6Node67_cover
  exact hb f h2
theorem root6Node60_cover : Covers root6Node60Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node60Domains0 root6Node60Domains1 f hf root6Node60Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node60Domains1 (.output 29)
    root6Node60Leaf_checked f h1
theorem root6Node59_cover : Covers root6Node59Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node59Domains0 root6Node59Domains1 f hf root6Node59Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node59Domains1 (.output 28)
    root6Node59Leaf_checked f h1
theorem root6Node58_cover : Covers root6Node58Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node58Domains0 root6Node58Domains1 f hf root6Node58Step1_checked
  have hb : Covers root6Node58Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node58Domains1 root6Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node59_cover
    · exact root6Node60_cover
  exact hb f h1
theorem root6Node57_cover : Covers root6Node57Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node57Domains0 root6Node57Domains1 f hf root6Node57Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node57Domains1 (.output 27)
    root6Node57Leaf_checked f h1
theorem root6Node56_cover : Covers root6Node56Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node56Domains0 root6Node56Domains1 f hf root6Node56Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node56Domains1 (.output 26)
    root6Node56Leaf_checked f h1
theorem root6Node55_cover : Covers root6Node55Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root6Node55Domains0 root6Node55Domains1 f hf root6Node55Step1_checked
  have hb : Covers root6Node55Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node55Domains1 root6Outputs 84
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node56_cover
    · exact root6Node57_cover
  exact hb f h1
theorem root6Node54_cover : Covers root6Node54Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node54Domains0 root6Node54Domains1 f hf root6Node54Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root6Node54Domains1 root6Node54Domains2 f h1 root6Node54Step2_checked
  have hb : Covers root6Node54Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node54Domains2 root6Outputs 69
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node55_cover
    · exact root6Node58_cover
  exact hb f h2
theorem root6Node53_cover : Covers root6Node53Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node53Domains0 root6Node53Domains1 f hf root6Node53Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node53Domains1 (.output 25)
    root6Node53Leaf_checked f h1
theorem root6Node52_cover : Covers root6Node52Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node52Domains0 root6Node52Domains1 f hf root6Node52Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node52Domains1 (.output 24)
    root6Node52Leaf_checked f h1
theorem root6Node51_cover : Covers root6Node51Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node51Domains0 root6Node51Domains1 f hf root6Node51Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node51Domains1 root6Node51Domains2 f h1 root6Node51Step2_checked
  have hb : Covers root6Node51Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node51Domains2 root6Outputs 78
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node52_cover
    · exact root6Node53_cover
  exact hb f h2
theorem root6Node50_cover : Covers root6Node50Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node50Domains0 root6Node50Domains1 f hf root6Node50Step1_checked
  have hb : Covers root6Node50Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node50Domains1 root6Outputs 21
    intro s hs
    change s ∈ [(2,2),(2,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node51_cover
    · exact root6Node54_cover
  exact hb f h1
theorem root6Node49_cover : Covers root6Node49Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node49Domains0 root6Node49Domains1 f hf root6Node49Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node49Domains1 root6Node49Domains2 f h1 root6Node49Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node49Domains2 (.output 23)
    root6Node49Leaf_checked f h2
theorem root6Node48_cover : Covers root6Node48Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node48Domains0 root6Node48Domains1 f hf root6Node48Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node48Domains1 root6Node48Domains2 f h1 root6Node48Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node48Domains2 (.output 22)
    root6Node48Leaf_checked f h2
theorem root6Node47_cover : Covers root6Node47Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node47Domains0 root6Node47Domains1 f hf root6Node47Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root6Node47Domains1 root6Node47Domains2 f h1 root6Node47Step2_checked
  have hb : Covers root6Node47Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node47Domains2 root6Outputs 21
    intro s hs
    change s ∈ [(2,2),(2,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node48_cover
    · exact root6Node49_cover
  exact hb f h2
theorem root6Node46_cover : Covers root6Node46Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node46Domains0 root6Node46Domains1 f hf root6Node46Step1_checked
  have hb : Covers root6Node46Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node46Domains1 root6Outputs 20
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node47_cover
    · exact root6Node50_cover
  exact hb f h1
theorem root6Node45_cover : Covers root6Node45Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root6Node45Domains0 root6Node45Domains1 f hf root6Node45Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root6Node45Domains1 root6Node45Domains2 f h1 root6Node45Step2_checked
  have h3 := solution_checkReplacement constraints table36 table36_member
    root6Node45Domains2 root6Node45Domains3 f h2 root6Node45Step3_checked
  have hb : Covers root6Node45Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node45Domains3 root6Outputs 4
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node46_cover
    · exact root6Node61_cover
  exact hb f h3
theorem root6Node44_cover : Covers root6Node44Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node44Domains0 root6Node44Domains1 f hf root6Node44Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node44Domains1 root6Node44Domains2 f h1 root6Node44Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node44Domains2 (.output 21)
    root6Node44Leaf_checked f h2
theorem root6Node43_cover : Covers root6Node43Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node43Domains0 root6Node43Domains1 f hf root6Node43Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node43Domains1 root6Node43Domains2 f h1 root6Node43Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node43Domains2 (.output 20)
    root6Node43Leaf_checked f h2
theorem root6Node42_cover : Covers root6Node42Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root6Node42Domains0 root6Node42Domains1 f hf root6Node42Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root6Node42Domains1 root6Node42Domains2 f h1 root6Node42Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root6Node42Domains2 root6Node42Domains3 f h2 root6Node42Step3_checked
  have hb : Covers root6Node42Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node42Domains3 root6Outputs 21
    intro s hs
    change s ∈ [(2,2),(2,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node43_cover
    · exact root6Node44_cover
  exact hb f h3
theorem root6Node41_cover : Covers root6Node41Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table45 table45_member
    root6Node41Domains0 root6Node41Domains1 f hf root6Node41Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root6Node41Domains1 root6Node41Domains2 f h1 root6Node41Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root6Node41Domains2 root6Node41Domains3 f h2 root6Node41Step3_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node41Domains3 (.output 19)
    root6Node41Leaf_checked f h3
theorem root6Node40_cover : Covers root6Node40Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node40Domains0 root6Node40Domains1 f hf root6Node40Step1_checked
  have hb : Covers root6Node40Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node40Domains1 root6Outputs 8
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node41_cover
    · exact root6Node42_cover
  exact hb f h1
theorem root6Node39_cover : Covers root6Node39Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root6Node39Domains0 root6Node39Domains1 f hf root6Node39Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root6Node39Domains1 root6Node39Domains2 f h1 root6Node39Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root6Node39Domains2 root6Node39Domains3 f h2 root6Node39Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root6Node39Domains3 root6Node39Domains4 f h3 root6Node39Step4_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node39Domains4 (.output 18)
    root6Node39Leaf_checked f h4
theorem root6Node38_cover : Covers root6Node38Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node38Domains0 root6Node38Domains1 f hf root6Node38Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root6Node38Domains1 root6Node38Domains2 f h1 root6Node38Step2_checked
  have hb : Covers root6Node38Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node38Domains2 root6Outputs 5
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node39_cover
    · exact root6Node40_cover
  exact hb f h2
theorem root6Node37_cover : Covers root6Node37Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root6Node37Domains0 root6Node37Domains1 f hf root6Node37Step1_checked
  have hb : Covers root6Node37Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node37Domains1 root6Outputs 3
    intro s hs
    change s ∈ [(1,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node38_cover
    · exact root6Node45_cover
  exact hb f h1
theorem root6Node36_cover : Covers root6Node36Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node36Domains0 root6Node36Domains1 f hf root6Node36Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root6Node36Domains1 root6Node36Domains2 f h1 root6Node36Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node36Domains2 (.output 17)
    root6Node36Leaf_checked f h2
theorem root6Node35_cover : Covers root6Node35Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node35Domains0 root6Node35Domains1 f hf root6Node35Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node35Domains1 (.output 16)
    root6Node35Leaf_checked f h1
theorem root6Node34_cover : Covers root6Node34Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node34Domains0 root6Node34Domains1 f hf root6Node34Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node34Domains1 (.output 15)
    root6Node34Leaf_checked f h1
theorem root6Node33_cover : Covers root6Node33Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node33Domains0 root6Node33Domains1 f hf root6Node33Step1_checked
  have hb : Covers root6Node33Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node33Domains1 root6Outputs 78
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node34_cover
    · exact root6Node35_cover
  exact hb f h1
theorem root6Node32_cover : Covers root6Node32Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node32Domains0 root6Node32Domains1 f hf root6Node32Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root6Node32Domains1 root6Node32Domains2 f h1 root6Node32Step2_checked
  have hb : Covers root6Node32Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node32Domains2 root6Outputs 29
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node33_cover
    · exact root6Node36_cover
  exact hb f h2
theorem root6Node31_cover : Covers root6Node31Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node31Domains0 root6Node31Domains1 f hf root6Node31Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root6Node31Domains1 root6Node31Domains2 f h1 root6Node31Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node31Domains2 (.output 14)
    root6Node31Leaf_checked f h2
theorem root6Node30_cover : Covers root6Node30Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node30Domains0 root6Node30Domains1 f hf root6Node30Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node30Domains1 (.output 13)
    root6Node30Leaf_checked f h1
theorem root6Node29_cover : Covers root6Node29Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node29Domains0 root6Node29Domains1 f hf root6Node29Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node29Domains1 (.output 12)
    root6Node29Leaf_checked f h1
theorem root6Node28_cover : Covers root6Node28Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node28Domains0 root6Node28Domains1 f hf root6Node28Step1_checked
  have hb : Covers root6Node28Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node28Domains1 root6Outputs 78
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node29_cover
    · exact root6Node30_cover
  exact hb f h1
theorem root6Node27_cover : Covers root6Node27Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root6Node27Domains0 root6Node27Domains1 f hf root6Node27Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root6Node27Domains1 root6Node27Domains2 f h1 root6Node27Step2_checked
  have hb : Covers root6Node27Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node27Domains2 root6Outputs 29
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node28_cover
    · exact root6Node31_cover
  exact hb f h2
theorem root6Node26_cover : Covers root6Node26Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node26Domains0 root6Node26Domains1 f hf root6Node26Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node26Domains1 (.output 11)
    root6Node26Leaf_checked f h1
theorem root6Node25_cover : Covers root6Node25Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root6Node25Domains0 root6Node25Domains1 f hf root6Node25Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node25Domains1 (.output 10)
    root6Node25Leaf_checked f h1
theorem root6Node24_cover : Covers root6Node24Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node24Domains0 root6Node24Domains1 f hf root6Node24Step1_checked
  have hb : Covers root6Node24Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node24Domains1 root6Outputs 78
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node25_cover
    · exact root6Node26_cover
  exact hb f h1
theorem root6Node23_cover : Covers root6Node23Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node23Domains0 root6Node23Domains1 f hf root6Node23Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root6Node23Domains1 root6Node23Domains2 f h1 root6Node23Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node23Domains2 (.output 9)
    root6Node23Leaf_checked f h2
theorem root6Node22_cover : Covers root6Node22Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node22Domains0 root6Node22Domains1 f hf root6Node22Step1_checked
  have hb : Covers root6Node22Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node22Domains1 root6Outputs 20
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node23_cover
    · exact root6Node24_cover
  exact hb f h1
theorem root6Node21_cover : Covers root6Node21Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root6Node21Domains0 root6Node21Domains1 f hf root6Node21Step1_checked
  have hb : Covers root6Node21Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node21Domains1 root6Outputs 12
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node22_cover
    · exact root6Node27_cover
  exact hb f h1
theorem root6Node20_cover : Covers root6Node20Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root6Node20Domains0 root6Node20Domains1 f hf root6Node20Step1_checked
  have hb : Covers root6Node20Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node20Domains1 root6Outputs 4
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node21_cover
    · exact root6Node32_cover
  exact hb f h1
theorem root6Node19_cover : Covers root6Node19Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node19Domains0 root6Node19Domains1 f hf root6Node19Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root6Node19Domains1 root6Node19Domains2 f h1 root6Node19Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node19Domains2 (.output 8)
    root6Node19Leaf_checked f h2
theorem root6Node18_cover : Covers root6Node18Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node18Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node18Domains0 root6Outputs 3
    intro s hs
    change s ∈ [(1,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node19_cover
    · exact root6Node20_cover
  exact hb f hf
theorem root6Node17_cover : Covers root6Node17Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root6Node17Domains0 root6Node17Domains1 f hf root6Node17Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node17Domains1 root6Node17Domains2 f h1 root6Node17Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root6Node17Domains2 root6Node17Domains3 f h2 root6Node17Step3_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node17Domains3 (.output 7)
    root6Node17Leaf_checked f h3
theorem root6Node16_cover : Covers root6Node16Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root6Node16Domains0 root6Node16Domains1 f hf root6Node16Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root6Node16Domains1 root6Node16Domains2 f h1 root6Node16Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root6Node16Domains2 root6Node16Domains3 f h2 root6Node16Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root6Node16Domains3 root6Node16Domains4 f h3 root6Node16Step4_checked
  have hb : Covers root6Node16Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node16Domains4 root6Outputs 0
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node17_cover
    · exact root6Node18_cover
  exact hb f h4
theorem root6Node15_cover : Covers root6Node15Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root6Node15Domains0 root6Node15Domains1 f hf root6Node15Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root6Node15Domains1 root6Node15Domains2 f h1 root6Node15Step2_checked
  have h3 := solution_checkReplacement constraints table36 table36_member
    root6Node15Domains2 root6Node15Domains3 f h2 root6Node15Step3_checked
  have hb : Covers root6Node15Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node15Domains3 root6Outputs 1
    intro s hs
    change s ∈ [(5,0),(5,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node16_cover
    · exact root6Node37_cover
  exact hb f h3
theorem root6Node14_cover : Covers root6Node14Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root6Node14Domains0 root6Node14Domains1 f hf root6Node14Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node14Domains1 root6Node14Domains2 f h1 root6Node14Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root6Node14Domains2 root6Node14Domains3 f h2 root6Node14Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root6Node14Domains3 root6Node14Domains4 f h3 root6Node14Step4_checked
  have hb : Covers root6Node14Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node14Domains4 root6Outputs 6
    intro s hs
    change s ∈ [(1,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node15_cover
    · exact root6Node74_cover
  exact hb f h4
theorem root6Node13_cover : Covers root6Node13Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node13Domains0 root6Node13Domains1 f hf root6Node13Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node13Domains1 (.output 6)
    root6Node13Leaf_checked f h1
theorem root6Node12_cover : Covers root6Node12Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root6Node12Domains0 root6Node12Domains1 f hf root6Node12Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node12Domains1 (.output 5)
    root6Node12Leaf_checked f h1
theorem root6Node11_cover : Covers root6Node11Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node11Domains0 root6Node11Domains1 f hf root6Node11Step1_checked
  have hb : Covers root6Node11Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node11Domains1 root6Outputs 81
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node12_cover
    · exact root6Node13_cover
  exact hb f h1
theorem root6Node10_cover : Covers root6Node10Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node10Domains0 root6Node10Domains1 f hf root6Node10Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root6Node10Domains1 root6Node10Domains2 f h1 root6Node10Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node10Domains2 (.output 4)
    root6Node10Leaf_checked f h2
theorem root6Node9_cover : Covers root6Node9Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node9Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node9Domains0 root6Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node10_cover
    · exact root6Node11_cover
  exact hb f hf
theorem root6Node8_cover : Covers root6Node8Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root6Node8Domains0 root6Node8Domains1 f hf root6Node8Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root6Node8Domains1 root6Node8Domains2 f h1 root6Node8Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node8Domains2 (.output 3)
    root6Node8Leaf_checked f h2
theorem root6Node7_cover : Covers root6Node7Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node7Domains0 root6Node7Domains1 f hf root6Node7Step1_checked
  have hb : Covers root6Node7Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node7Domains1 root6Outputs 20
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node8_cover
    · exact root6Node9_cover
  exact hb f h1
theorem root6Node6_cover : Covers root6Node6Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node6Domains0 root6Node6Domains1 f hf root6Node6Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node6Domains1 (.output 2)
    root6Node6Leaf_checked f h1
theorem root6Node5_cover : Covers root6Node5Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root6Node5Domains0 root6Node5Domains1 f hf root6Node5Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node5Domains1 (.output 1)
    root6Node5Leaf_checked f h1
theorem root6Node4_cover : Covers root6Node4Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root6Node4Domains0 root6Node4Domains1 f hf root6Node4Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root6Node4Domains1 root6Node4Domains2 f h1 root6Node4Step2_checked
  have hb : Covers root6Node4Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node4Domains2 root6Outputs 29
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node5_cover
    · exact root6Node6_cover
  exact hb f h2
theorem root6Node3_cover : Covers root6Node3Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root6Node3Domains0 root6Node3Domains1 f hf root6Node3Step1_checked
  have hb : Covers root6Node3Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node3Domains1 root6Outputs 3
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node4_cover
    · exact root6Node7_cover
  exact hb f h1
theorem root6Node2_cover : Covers root6Node2Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root6Node2Domains0 root6Node2Domains1 f hf root6Node2Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root6Node2Domains1 root6Node2Domains2 f h1 root6Node2Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root6Node2Domains2 root6Node2Domains3 f h2 root6Node2Step3_checked
  have h4 := solution_checkReplacement constraints table52 table52_member
    root6Node2Domains3 root6Node2Domains4 f h3 root6Node2Step4_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node2Domains4 (.output 0)
    root6Node2Leaf_checked f h4
theorem root6Node1_cover : Covers root6Node1Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root6Node1Domains0 root6Node1Domains1 f hf root6Node1Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root6Node1Domains1 root6Node1Domains2 f h1 root6Node1Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root6Node1Domains2 root6Node1Domains3 f h2 root6Node1Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root6Node1Domains3 root6Node1Domains4 f h3 root6Node1Step4_checked
  have hb : Covers root6Node1Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node1Domains4 root6Outputs 0
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node2_cover
    · exact root6Node3_cover
  exact hb f h4
theorem root6Node0_cover : Covers root6Node0Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root6Node0Domains0 root6Node0Domains1 f hf root6Node0Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root6Node0Domains1 root6Node0Domains2 f h1 root6Node0Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root6Node0Domains2 root6Node0Domains3 f h2 root6Node0Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root6Node0Domains3 root6Node0Domains4 f h3 root6Node0Step4_checked
  have hb : Covers root6Node0Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node0Domains4 root6Outputs 44
    intro s hs
    change s ∈ [(2,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node1_cover
    · exact root6Node14_cover
  exact hb f h4
theorem root6_table_cover : Covers (domains (6,0)) constraints root6Outputs := root6Node0_cover
theorem root6Family_count : root6Family.length = 63 := rfl
#print axioms root6_table_cover
end SpectreFinite.HexSearch.RadiusFive
