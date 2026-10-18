module

public import SpectreFinite.RadiusFiveRoot0Part48

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root0Node118_cover : Covers root0Node118Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node118Domains0 root0Node118Domains1 f hf root0Node118Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root0Node118Domains1 root0Node118Domains2 f h1 root0Node118Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node118Domains2 (.output 59)
    root0Node118Leaf_checked f h2
theorem root0Node117_cover : Covers root0Node117Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node117Domains0 root0Node117Domains1 f hf root0Node117Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node117Domains1 (.output 58)
    root0Node117Leaf_checked f h1
theorem root0Node116_cover : Covers root0Node116Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node116Domains0 root0Node116Domains1 f hf root0Node116Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node116Domains1 (.output 57)
    root0Node116Leaf_checked f h1
theorem root0Node115_cover : Covers root0Node115Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node115Domains0 root0Node115Domains1 f hf root0Node115Step1_checked
  have hb : Covers root0Node115Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node115Domains1 root0Outputs 70
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node116_cover
    · exact root0Node117_cover
  exact hb f h1
theorem root0Node114_cover : Covers root0Node114Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node114Domains0 root0Node114Domains1 f hf root0Node114Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root0Node114Domains1 root0Node114Domains2 f h1 root0Node114Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node114Domains2 (.output 56)
    root0Node114Leaf_checked f h2
theorem root0Node113_cover : Covers root0Node113Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root0Node113Domains0 root0Node113Domains1 f hf root0Node113Step1_checked
  have hb : Covers root0Node113Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node113Domains1 root0Outputs 50
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node114_cover
    · exact root0Node115_cover
  exact hb f h1
theorem root0Node112_cover : Covers root0Node112Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node112Domains0 root0Node112Domains1 f hf root0Node112Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node112Domains1 root0Node112Domains2 f h1 root0Node112Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node112Domains2 (.output 55)
    root0Node112Leaf_checked f h2
theorem root0Node111_cover : Covers root0Node111Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root0Node111Domains0 root0Node111Domains1 f hf root0Node111Step1_checked
  have hb : Covers root0Node111Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node111Domains1 root0Outputs 40
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node112_cover
    · exact root0Node113_cover
  exact hb f h1
theorem root0Node110_cover : Covers root0Node110Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root0Node110Domains0 root0Node110Domains1 f hf root0Node110Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node110Domains1 (.output 54)
    root0Node110Leaf_checked f h1
theorem root0Node109_cover : Covers root0Node109Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root0Node109Domains0 root0Node109Domains1 f hf root0Node109Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node109Domains1 (.output 53)
    root0Node109Leaf_checked f h1
theorem root0Node108_cover : Covers root0Node108Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node108Domains0 root0Node108Domains1 f hf root0Node108Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node108Domains1 root0Node108Domains2 f h1 root0Node108Step2_checked
  have hb : Covers root0Node108Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node108Domains2 root0Outputs 30
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node109_cover
    · exact root0Node110_cover
  exact hb f h2
theorem root0Node107_cover : Covers root0Node107Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node107Domains0 root0Node107Domains1 f hf root0Node107Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node107Domains1 root0Node107Domains2 f h1 root0Node107Step2_checked
  have hb : Covers root0Node107Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node107Domains2 root0Outputs 31
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node108_cover
    · exact root0Node111_cover
  exact hb f h2
theorem root0Node106_cover : Covers root0Node106Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root0Node106Domains0 root0Node106Domains1 f hf root0Node106Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root0Node106Domains1 root0Node106Domains2 f h1 root0Node106Step2_checked
  have hb : Covers root0Node106Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node106Domains2 root0Outputs 29
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node107_cover
    · exact root0Node118_cover
  exact hb f h2
theorem root0Node105_cover : Covers root0Node105Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node105Domains0 root0Node105Domains1 f hf root0Node105Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node105Domains1 (.output 52)
    root0Node105Leaf_checked f h1
theorem root0Node104_cover : Covers root0Node104Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node104Domains0 root0Node104Domains1 f hf root0Node104Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node104Domains1 (.output 51)
    root0Node104Leaf_checked f h1
theorem root0Node103_cover : Covers root0Node103Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node103Domains0 root0Node103Domains1 f hf root0Node103Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root0Node103Domains1 root0Node103Domains2 f h1 root0Node103Step2_checked
  have hb : Covers root0Node103Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node103Domains2 root0Outputs 60
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node104_cover
    · exact root0Node105_cover
  exact hb f h2
theorem root0Node102_cover : Covers root0Node102Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node102Domains0 root0Node102Domains1 f hf root0Node102Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node102Domains1 (.output 50)
    root0Node102Leaf_checked f h1
theorem root0Node101_cover : Covers root0Node101Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node101Domains0 root0Node101Domains1 f hf root0Node101Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node101Domains1 (.output 49)
    root0Node101Leaf_checked f h1
theorem root0Node100_cover : Covers root0Node100Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node100Domains0 root0Node100Domains1 f hf root0Node100Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node100Domains1 root0Node100Domains2 f h1 root0Node100Step2_checked
  have hb : Covers root0Node100Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node100Domains2 root0Outputs 84
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node101_cover
    · exact root0Node102_cover
  exact hb f h2
theorem root0Node99_cover : Covers root0Node99Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node99Domains0 root0Node99Domains1 f hf root0Node99Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node99Domains1 (.output 48)
    root0Node99Leaf_checked f h1
theorem root0Node98_cover : Covers root0Node98Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node98Domains0 root0Node98Domains1 f hf root0Node98Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node98Domains1 (.output 47)
    root0Node98Leaf_checked f h1
theorem root0Node97_cover : Covers root0Node97Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node97Domains0 root0Node97Domains1 f hf root0Node97Step1_checked
  have hb : Covers root0Node97Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node97Domains1 root0Outputs 84
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node98_cover
    · exact root0Node99_cover
  exact hb f h1
theorem root0Node96_cover : Covers root0Node96Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node96Domains0 root0Node96Domains1 f hf root0Node96Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node96Domains1 (.output 46)
    root0Node96Leaf_checked f h1
theorem root0Node95_cover : Covers root0Node95Domains0 constraints root0Outputs := by
  intro f hf
  have hb : Covers root0Node95Domains0 constraints root0Outputs := by
    apply covers_of_branches root0Node95Domains0 root0Outputs 64
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node96_cover
    · exact root0Node97_cover
  exact hb f hf
theorem root0Node94_cover : Covers root0Node94Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node94Domains0 root0Node94Domains1 f hf root0Node94Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node94Domains1 root0Node94Domains2 f h1 root0Node94Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node94Domains2 (.output 45)
    root0Node94Leaf_checked f h2
theorem root0Node93_cover : Covers root0Node93Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root0Node93Domains0 root0Node93Domains1 f hf root0Node93Step1_checked
  have hb : Covers root0Node93Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node93Domains1 root0Outputs 50
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node94_cover
    · exact root0Node95_cover
  exact hb f h1
theorem root0Node92_cover : Covers root0Node92Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root0Node92Domains0 root0Node92Domains1 f hf root0Node92Step1_checked
  have hb : Covers root0Node92Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node92Domains1 root0Outputs 40
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node93_cover
    · exact root0Node100_cover
  exact hb f h1
theorem root0Node91_cover : Covers root0Node91Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node91Domains0 root0Node91Domains1 f hf root0Node91Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node91Domains1 (.output 44)
    root0Node91Leaf_checked f h1
theorem root0Node90_cover : Covers root0Node90Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node90Domains0 root0Node90Domains1 f hf root0Node90Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node90Domains1 (.output 43)
    root0Node90Leaf_checked f h1
theorem root0Node89_cover : Covers root0Node89Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node89Domains0 root0Node89Domains1 f hf root0Node89Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node89Domains1 root0Node89Domains2 f h1 root0Node89Step2_checked
  have hb : Covers root0Node89Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node89Domains2 root0Outputs 84
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node90_cover
    · exact root0Node91_cover
  exact hb f h2
theorem root0Node88_cover : Covers root0Node88Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node88Domains0 root0Node88Domains1 f hf root0Node88Step1_checked
  have hb : Covers root0Node88Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node88Domains1 root0Outputs 30
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node89_cover
    · exact root0Node92_cover
  exact hb f h1
theorem root0Node87_cover : Covers root0Node87Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root0Node87Domains0 root0Node87Domains1 f hf root0Node87Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root0Node87Domains1 root0Node87Domains2 f h1 root0Node87Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root0Node87Domains2 root0Node87Domains3 f h2 root0Node87Step3_checked
  have hb : Covers root0Node87Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node87Domains3 root0Outputs 29
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node88_cover
    · exact root0Node103_cover
  exact hb f h3
theorem root0Node86_cover : Covers root0Node86Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root0Node86Domains0 root0Node86Domains1 f hf root0Node86Step1_checked
  have hb : Covers root0Node86Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node86Domains1 root0Outputs 6
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node87_cover
    · exact root0Node106_cover
  exact hb f h1
theorem root0Node85_cover : Covers root0Node85Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node85Domains0 root0Node85Domains1 f hf root0Node85Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root0Node85Domains1 root0Node85Domains2 f h1 root0Node85Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node85Domains2 (.output 42)
    root0Node85Leaf_checked f h2
theorem root0Node84_cover : Covers root0Node84Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node84Domains0 root0Node84Domains1 f hf root0Node84Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node84Domains1 (.output 41)
    root0Node84Leaf_checked f h1
theorem root0Node83_cover : Covers root0Node83Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node83Domains0 root0Node83Domains1 f hf root0Node83Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node83Domains1 (.output 40)
    root0Node83Leaf_checked f h1
theorem root0Node82_cover : Covers root0Node82Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node82Domains0 root0Node82Domains1 f hf root0Node82Step1_checked
  have hb : Covers root0Node82Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node82Domains1 root0Outputs 70
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node83_cover
    · exact root0Node84_cover
  exact hb f h1
theorem root0Node81_cover : Covers root0Node81Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node81Domains0 root0Node81Domains1 f hf root0Node81Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root0Node81Domains1 root0Node81Domains2 f h1 root0Node81Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node81Domains2 (.output 39)
    root0Node81Leaf_checked f h2
theorem root0Node80_cover : Covers root0Node80Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root0Node80Domains0 root0Node80Domains1 f hf root0Node80Step1_checked
  have hb : Covers root0Node80Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node80Domains1 root0Outputs 50
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node81_cover
    · exact root0Node82_cover
  exact hb f h1
theorem root0Node79_cover : Covers root0Node79Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node79Domains0 root0Node79Domains1 f hf root0Node79Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node79Domains1 root0Node79Domains2 f h1 root0Node79Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node79Domains2 (.output 38)
    root0Node79Leaf_checked f h2
theorem root0Node78_cover : Covers root0Node78Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root0Node78Domains0 root0Node78Domains1 f hf root0Node78Step1_checked
  have hb : Covers root0Node78Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node78Domains1 root0Outputs 40
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node79_cover
    · exact root0Node80_cover
  exact hb f h1
theorem root0Node77_cover : Covers root0Node77Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node77Domains0 root0Node77Domains1 f hf root0Node77Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node77Domains1 root0Node77Domains2 f h1 root0Node77Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node77Domains2 (.output 37)
    root0Node77Leaf_checked f h2
theorem root0Node76_cover : Covers root0Node76Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node76Domains0 root0Node76Domains1 f hf root0Node76Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node76Domains1 root0Node76Domains2 f h1 root0Node76Step2_checked
  have hb : Covers root0Node76Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node76Domains2 root0Outputs 30
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node77_cover
    · exact root0Node78_cover
  exact hb f h2
theorem root0Node75_cover : Covers root0Node75Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node75Domains0 root0Node75Domains1 f hf root0Node75Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root0Node75Domains1 root0Node75Domains2 f h1 root0Node75Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root0Node75Domains2 root0Node75Domains3 f h2 root0Node75Step3_checked
  have hb : Covers root0Node75Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node75Domains3 root0Outputs 29
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node76_cover
    · exact root0Node85_cover
  exact hb f h3
theorem root0Node74_cover : Covers root0Node74Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root0Node74Domains0 root0Node74Domains1 f hf root0Node74Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root0Node74Domains1 root0Node74Domains2 f h1 root0Node74Step2_checked
  have hb : Covers root0Node74Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node74Domains2 root0Outputs 3
    intro s hs
    change s ∈ [(0,0),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node75_cover
    · exact root0Node86_cover
  exact hb f h2
theorem root0Node73_cover : Covers root0Node73Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node73Domains0 root0Node73Domains1 f hf root0Node73Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node73Domains1 (.output 36)
    root0Node73Leaf_checked f h1
theorem root0Node72_cover : Covers root0Node72Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node72Domains0 root0Node72Domains1 f hf root0Node72Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node72Domains1 (.output 35)
    root0Node72Leaf_checked f h1
theorem root0Node71_cover : Covers root0Node71Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root0Node71Domains0 root0Node71Domains1 f hf root0Node71Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root0Node71Domains1 root0Node71Domains2 f h1 root0Node71Step2_checked
  have h3 := solution_checkReplacement constraints table27 table27_member
    root0Node71Domains2 root0Node71Domains3 f h2 root0Node71Step3_checked
  have hb : Covers root0Node71Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node71Domains3 root0Outputs 84
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node72_cover
    · exact root0Node73_cover
  exact hb f h3
theorem root0Node70_cover : Covers root0Node70Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node70Domains0 root0Node70Domains1 f hf root0Node70Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node70Domains1 (.output 34)
    root0Node70Leaf_checked f h1
theorem root0Node69_cover : Covers root0Node69Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node69Domains0 root0Node69Domains1 f hf root0Node69Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node69Domains1 (.output 33)
    root0Node69Leaf_checked f h1
theorem root0Node68_cover : Covers root0Node68Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node68Domains0 root0Node68Domains1 f hf root0Node68Step1_checked
  have hb : Covers root0Node68Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node68Domains1 root0Outputs 84
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node69_cover
    · exact root0Node70_cover
  exact hb f h1
theorem root0Node67_cover : Covers root0Node67Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node67Domains0 root0Node67Domains1 f hf root0Node67Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node67Domains1 (.output 32)
    root0Node67Leaf_checked f h1
theorem root0Node66_cover : Covers root0Node66Domains0 constraints root0Outputs := by
  intro f hf
  have hb : Covers root0Node66Domains0 constraints root0Outputs := by
    apply covers_of_branches root0Node66Domains0 root0Outputs 64
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node67_cover
    · exact root0Node68_cover
  exact hb f hf
theorem root0Node65_cover : Covers root0Node65Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node65Domains0 root0Node65Domains1 f hf root0Node65Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node65Domains1 root0Node65Domains2 f h1 root0Node65Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node65Domains2 (.output 31)
    root0Node65Leaf_checked f h2
theorem root0Node64_cover : Covers root0Node64Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root0Node64Domains0 root0Node64Domains1 f hf root0Node64Step1_checked
  have hb : Covers root0Node64Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node64Domains1 root0Outputs 50
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node65_cover
    · exact root0Node66_cover
  exact hb f h1
theorem root0Node63_cover : Covers root0Node63Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node63Domains0 root0Node63Domains1 f hf root0Node63Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node63Domains1 (.output 30)
    root0Node63Leaf_checked f h1
theorem root0Node62_cover : Covers root0Node62Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node62Domains0 root0Node62Domains1 f hf root0Node62Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node62Domains1 (.output 29)
    root0Node62Leaf_checked f h1
theorem root0Node61_cover : Covers root0Node61Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node61Domains0 root0Node61Domains1 f hf root0Node61Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node61Domains1 root0Node61Domains2 f h1 root0Node61Step2_checked
  have hb : Covers root0Node61Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node61Domains2 root0Outputs 84
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node62_cover
    · exact root0Node63_cover
  exact hb f h2
theorem root0Node60_cover : Covers root0Node60Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root0Node60Domains0 root0Node60Domains1 f hf root0Node60Step1_checked
  have hb : Covers root0Node60Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node60Domains1 root0Outputs 30
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node61_cover
    · exact root0Node64_cover
  exact hb f h1
theorem root0Node59_cover : Covers root0Node59Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node59Domains0 root0Node59Domains1 f hf root0Node59Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root0Node59Domains1 root0Node59Domains2 f h1 root0Node59Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root0Node59Domains2 root0Node59Domains3 f h2 root0Node59Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root0Node59Domains3 root0Node59Domains4 f h3 root0Node59Step4_checked
  have hb : Covers root0Node59Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node59Domains4 root0Outputs 0
    intro s hs
    change s ∈ [(0,2),(1,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node60_cover
    · exact root0Node71_cover
  exact hb f h4
theorem root0Node58_cover : Covers root0Node58Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node58Domains0 root0Node58Domains1 f hf root0Node58Step1_checked
  have hb : Covers root0Node58Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node58Domains1 root0Outputs 2
    intro s hs
    change s ∈ [(5,1),(5,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node59_cover
    · exact root0Node74_cover
  exact hb f h1
theorem root0Node57_cover : Covers root0Node57Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root0Node57Domains0 root0Node57Domains1 f hf root0Node57Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root0Node57Domains1 root0Node57Domains2 f h1 root0Node57Step2_checked
  have h3 := solution_checkReplacement constraints table27 table27_member
    root0Node57Domains2 root0Node57Domains3 f h2 root0Node57Step3_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node57Domains3 (.output 28)
    root0Node57Leaf_checked f h3
theorem root0Node56_cover : Covers root0Node56Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node56Domains0 root0Node56Domains1 f hf root0Node56Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node56Domains1 (.output 27)
    root0Node56Leaf_checked f h1
theorem root0Node55_cover : Covers root0Node55Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root0Node55Domains0 root0Node55Domains1 f hf root0Node55Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node55Domains1 (.output 26)
    root0Node55Leaf_checked f h1
theorem root0Node54_cover : Covers root0Node54Domains0 constraints root0Outputs := by
  intro f hf
  have hb : Covers root0Node54Domains0 constraints root0Outputs := by
    apply covers_of_branches root0Node54Domains0 root0Outputs 64
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node55_cover
    · exact root0Node56_cover
  exact hb f hf
theorem root0Node53_cover : Covers root0Node53Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node53Domains0 root0Node53Domains1 f hf root0Node53Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node53Domains1 root0Node53Domains2 f h1 root0Node53Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node53Domains2 (.output 25)
    root0Node53Leaf_checked f h2
theorem root0Node52_cover : Covers root0Node52Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root0Node52Domains0 root0Node52Domains1 f hf root0Node52Step1_checked
  have hb : Covers root0Node52Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node52Domains1 root0Outputs 50
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node53_cover
    · exact root0Node54_cover
  exact hb f h1
theorem root0Node51_cover : Covers root0Node51Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node51Domains0 root0Node51Domains1 f hf root0Node51Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node51Domains1 root0Node51Domains2 f h1 root0Node51Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node51Domains2 (.output 24)
    root0Node51Leaf_checked f h2
theorem root0Node50_cover : Covers root0Node50Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root0Node50Domains0 root0Node50Domains1 f hf root0Node50Step1_checked
  have hb : Covers root0Node50Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node50Domains1 root0Outputs 30
    intro s hs
    change s ∈ [(7,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node51_cover
    · exact root0Node52_cover
  exact hb f h1
theorem root0Node49_cover : Covers root0Node49Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node49Domains0 root0Node49Domains1 f hf root0Node49Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root0Node49Domains1 root0Node49Domains2 f h1 root0Node49Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root0Node49Domains2 root0Node49Domains3 f h2 root0Node49Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root0Node49Domains3 root0Node49Domains4 f h3 root0Node49Step4_checked
  have hb : Covers root0Node49Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node49Domains4 root0Outputs 0
    intro s hs
    change s ∈ [(0,2),(1,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node50_cover
    · exact root0Node57_cover
  exact hb f h4
theorem root0Node48_cover : Covers root0Node48Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root0Node48Domains0 root0Node48Domains1 f hf root0Node48Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node48Domains1 root0Node48Domains2 f h1 root0Node48Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root0Node48Domains2 root0Node48Domains3 f h2 root0Node48Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root0Node48Domains3 root0Node48Domains4 f h3 root0Node48Step4_checked
  have hb : Covers root0Node48Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node48Domains4 root0Outputs 5
    intro s hs
    change s ∈ [(1,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node49_cover
    · exact root0Node58_cover
  exact hb f h4
theorem root0Node47_cover : Covers root0Node47Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node47Domains0 root0Node47Domains1 f hf root0Node47Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node47Domains1 (.output 23)
    root0Node47Leaf_checked f h1
theorem root0Node46_cover : Covers root0Node46Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node46Domains0 root0Node46Domains1 f hf root0Node46Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node46Domains1 (.output 22)
    root0Node46Leaf_checked f h1
theorem root0Node45_cover : Covers root0Node45Domains0 constraints root0Outputs := by
  intro f hf
  have hb : Covers root0Node45Domains0 constraints root0Outputs := by
    apply covers_of_branches root0Node45Domains0 root0Outputs 60
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node46_cover
    · exact root0Node47_cover
  exact hb f hf
theorem root0Node44_cover : Covers root0Node44Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node44Domains0 root0Node44Domains1 f hf root0Node44Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node44Domains1 (.output 21)
    root0Node44Leaf_checked f h1
theorem root0Node43_cover : Covers root0Node43Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node43Domains0 root0Node43Domains1 f hf root0Node43Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node43Domains1 (.output 20)
    root0Node43Leaf_checked f h1
theorem root0Node42_cover : Covers root0Node42Domains0 constraints root0Outputs := by
  intro f hf
  have hb : Covers root0Node42Domains0 constraints root0Outputs := by
    apply covers_of_branches root0Node42Domains0 root0Outputs 60
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node43_cover
    · exact root0Node44_cover
  exact hb f hf
theorem root0Node41_cover : Covers root0Node41Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root0Node41Domains0 root0Node41Domains1 f hf root0Node41Step1_checked
  have hb : Covers root0Node41Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node41Domains1 root0Outputs 5
    intro s hs
    change s ∈ [(1,5),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node42_cover
    · exact root0Node45_cover
  exact hb f h1
theorem root0Node40_cover : Covers root0Node40Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node40Domains0 root0Node40Domains1 f hf root0Node40Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node40Domains1 (.output 19)
    root0Node40Leaf_checked f h1
theorem root0Node39_cover : Covers root0Node39Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node39Domains0 root0Node39Domains1 f hf root0Node39Step1_checked
  have hb : Covers root0Node39Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node39Domains1 root0Outputs 4
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node40_cover
    · exact root0Node41_cover
  exact hb f h1
theorem root0Node38_cover : Covers root0Node38Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node38Domains0 root0Node38Domains1 f hf root0Node38Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node38Domains1 (.output 18)
    root0Node38Leaf_checked f h1
theorem root0Node37_cover : Covers root0Node37Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node37Domains0 root0Node37Domains1 f hf root0Node37Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node37Domains1 (.output 17)
    root0Node37Leaf_checked f h1
theorem root0Node36_cover : Covers root0Node36Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root0Node36Domains0 root0Node36Domains1 f hf root0Node36Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root0Node36Domains1 root0Node36Domains2 f h1 root0Node36Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root0Node36Domains2 root0Node36Domains3 f h2 root0Node36Step3_checked
  have hb : Covers root0Node36Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node36Domains3 root0Outputs 60
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node37_cover
    · exact root0Node38_cover
  exact hb f h3
theorem root0Node35_cover : Covers root0Node35Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root0Node35Domains0 root0Node35Domains1 f hf root0Node35Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node35Domains1 root0Node35Domains2 f h1 root0Node35Step2_checked
  have hb : Covers root0Node35Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node35Domains2 root0Outputs 0
    intro s hs
    change s ∈ [(1,0),(6,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node36_cover
    · exact root0Node39_cover
  exact hb f h2
theorem root0Node34_cover : Covers root0Node34Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node34Domains0 root0Node34Domains1 f hf root0Node34Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node34Domains1 (.output 16)
    root0Node34Leaf_checked f h1
theorem root0Node33_cover : Covers root0Node33Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node33Domains0 root0Node33Domains1 f hf root0Node33Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node33Domains1 (.output 15)
    root0Node33Leaf_checked f h1
theorem root0Node32_cover : Covers root0Node32Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root0Node32Domains0 root0Node32Domains1 f hf root0Node32Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node32Domains1 root0Node32Domains2 f h1 root0Node32Step2_checked
  have hb : Covers root0Node32Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node32Domains2 root0Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node33_cover
    · exact root0Node34_cover
  exact hb f h2
theorem root0Node31_cover : Covers root0Node31Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root0Node31Domains0 root0Node31Domains1 f hf root0Node31Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node31Domains1 root0Node31Domains2 f h1 root0Node31Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node31Domains2 (.output 14)
    root0Node31Leaf_checked f h2
theorem root0Node30_cover : Covers root0Node30Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root0Node30Domains0 root0Node30Domains1 f hf root0Node30Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root0Node30Domains1 root0Node30Domains2 f h1 root0Node30Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node30Domains2 (.output 13)
    root0Node30Leaf_checked f h2
theorem root0Node29_cover : Covers root0Node29Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node29Domains0 root0Node29Domains1 f hf root0Node29Step1_checked
  have hb : Covers root0Node29Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node29Domains1 root0Outputs 6
    intro s hs
    change s ∈ [(1,2),(3,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node30_cover
    · exact root0Node31_cover
  exact hb f h1
theorem root0Node28_cover : Covers root0Node28Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root0Node28Domains0 root0Node28Domains1 f hf root0Node28Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root0Node28Domains1 root0Node28Domains2 f h1 root0Node28Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root0Node28Domains2 root0Node28Domains3 f h2 root0Node28Step3_checked
  have hb : Covers root0Node28Domains3 constraints root0Outputs := by
    apply covers_of_branches root0Node28Domains3 root0Outputs 7
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node29_cover
    · exact root0Node32_cover
  exact hb f h3
theorem root0Node27_cover : Covers root0Node27Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root0Node27Domains0 root0Node27Domains1 f hf root0Node27Step1_checked
  have h2 := solution_checkReplacement constraints table33 table33_member
    root0Node27Domains1 root0Node27Domains2 f h1 root0Node27Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root0Node27Domains2 root0Node27Domains3 f h2 root0Node27Step3_checked
  have h4 := solution_checkReplacement constraints table51 table51_member
    root0Node27Domains3 root0Node27Domains4 f h3 root0Node27Step4_checked
  have hb : Covers root0Node27Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node27Domains4 root0Outputs 1
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node28_cover
    · exact root0Node35_cover
  exact hb f h4
theorem root0Node26_cover : Covers root0Node26Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node26Domains0 root0Node26Domains1 f hf root0Node26Step1_checked
  have h2 := solution_checkReplacement constraints table3 table3_member
    root0Node26Domains1 root0Node26Domains2 f h1 root0Node26Step2_checked
  have hb : Covers root0Node26Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node26Domains2 root0Outputs 32
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node27_cover
    · exact root0Node48_cover
  exact hb f h2
theorem root0Node25_cover : Covers root0Node25Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node25Domains0 root0Node25Domains1 f hf root0Node25Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node25Domains1 (.output 12)
    root0Node25Leaf_checked f h1
theorem root0Node24_cover : Covers root0Node24Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node24Domains0 root0Node24Domains1 f hf root0Node24Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node24Domains1 (.output 11)
    root0Node24Leaf_checked f h1
theorem root0Node23_cover : Covers root0Node23Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node23Domains0 root0Node23Domains1 f hf root0Node23Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node23Domains1 (.output 10)
    root0Node23Leaf_checked f h1
theorem root0Node22_cover : Covers root0Node22Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root0Node22Domains0 root0Node22Domains1 f hf root0Node22Step1_checked
  have hb : Covers root0Node22Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node22Domains1 root0Outputs 85
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node23_cover
    · exact root0Node24_cover
  exact hb f h1
theorem root0Node21_cover : Covers root0Node21Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node21Domains0 root0Node21Domains1 f hf root0Node21Step1_checked
  have hb : Covers root0Node21Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node21Domains1 root0Outputs 70
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node22_cover
    · exact root0Node25_cover
  exact hb f h1
theorem root0Node20_cover : Covers root0Node20Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root0Node20Domains0 root0Node20Domains1 f hf root0Node20Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root0Node20Domains1 root0Node20Domains2 f h1 root0Node20Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node20Domains2 (.output 9)
    root0Node20Leaf_checked f h2
theorem root0Node19_cover : Covers root0Node19Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node19Domains0 root0Node19Domains1 f hf root0Node19Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root0Node19Domains1 root0Node19Domains2 f h1 root0Node19Step2_checked
  have hb : Covers root0Node19Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node19Domains2 root0Outputs 50
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node20_cover
    · exact root0Node21_cover
  exact hb f h2
theorem root0Node18_cover : Covers root0Node18Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node18Domains0 root0Node18Domains1 f hf root0Node18Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node18Domains1 root0Node18Domains2 f h1 root0Node18Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node18Domains2 (.output 8)
    root0Node18Leaf_checked f h2
theorem root0Node17_cover : Covers root0Node17Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node17Domains0 root0Node17Domains1 f hf root0Node17Step1_checked
  have hb : Covers root0Node17Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node17Domains1 root0Outputs 40
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node18_cover
    · exact root0Node19_cover
  exact hb f h1
theorem root0Node16_cover : Covers root0Node16Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root0Node16Domains0 root0Node16Domains1 f hf root0Node16Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root0Node16Domains1 root0Node16Domains2 f h1 root0Node16Step2_checked
  have h3 := solution_checkReplacement constraints table36 table36_member
    root0Node16Domains2 root0Node16Domains3 f h2 root0Node16Step3_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node16Domains3 (.output 7)
    root0Node16Leaf_checked f h3
theorem root0Node15_cover : Covers root0Node15Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root0Node15Domains0 root0Node15Domains1 f hf root0Node15Step1_checked
  have hb : Covers root0Node15Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node15Domains1 root0Outputs 6
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node16_cover
    · exact root0Node17_cover
  exact hb f h1
theorem root0Node14_cover : Covers root0Node14Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root0Node14Domains0 root0Node14Domains1 f hf root0Node14Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node14Domains1 root0Node14Domains2 f h1 root0Node14Step2_checked
  have h3 := solution_checkReplacement constraints table65 table65_member
    root0Node14Domains2 root0Node14Domains3 f h2 root0Node14Step3_checked
  have h4 := solution_checkReplacement constraints table21 table21_member
    root0Node14Domains3 root0Node14Domains4 f h3 root0Node14Step4_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node14Domains4 (.output 6)
    root0Node14Leaf_checked f h4
theorem root0Node13_cover : Covers root0Node13Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root0Node13Domains0 root0Node13Domains1 f hf root0Node13Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node13Domains1 root0Node13Domains2 f h1 root0Node13Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root0Node13Domains2 root0Node13Domains3 f h2 root0Node13Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root0Node13Domains3 root0Node13Domains4 f h3 root0Node13Step4_checked
  have hb : Covers root0Node13Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node13Domains4 root0Outputs 5
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node14_cover
    · exact root0Node15_cover
  exact hb f h4
theorem root0Node12_cover : Covers root0Node12Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table18 table18_member
    root0Node12Domains0 root0Node12Domains1 f hf root0Node12Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root0Node12Domains1 root0Node12Domains2 f h1 root0Node12Step2_checked
  have hb : Covers root0Node12Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node12Domains2 root0Outputs 34
    intro s hs
    change s ∈ [(3,0),(5,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node13_cover
    · exact root0Node26_cover
  exact hb f h2
theorem root0Node11_cover : Covers root0Node11Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node11Domains0 root0Node11Domains1 f hf root0Node11Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node11Domains1 (.output 5)
    root0Node11Leaf_checked f h1
theorem root0Node10_cover : Covers root0Node10Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node10Domains0 root0Node10Domains1 f hf root0Node10Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node10Domains1 (.output 4)
    root0Node10Leaf_checked f h1
theorem root0Node9_cover : Covers root0Node9Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node9Domains0 root0Node9Domains1 f hf root0Node9Step1_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node9Domains1 (.output 3)
    root0Node9Leaf_checked f h1
theorem root0Node8_cover : Covers root0Node8Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root0Node8Domains0 root0Node8Domains1 f hf root0Node8Step1_checked
  have hb : Covers root0Node8Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node8Domains1 root0Outputs 85
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node9_cover
    · exact root0Node10_cover
  exact hb f h1
theorem root0Node7_cover : Covers root0Node7Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node7Domains0 root0Node7Domains1 f hf root0Node7Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root0Node7Domains1 root0Node7Domains2 f h1 root0Node7Step2_checked
  have hb : Covers root0Node7Domains2 constraints root0Outputs := by
    apply covers_of_branches root0Node7Domains2 root0Outputs 70
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node8_cover
    · exact root0Node11_cover
  exact hb f h2
theorem root0Node6_cover : Covers root0Node6Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root0Node6Domains0 root0Node6Domains1 f hf root0Node6Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root0Node6Domains1 root0Node6Domains2 f h1 root0Node6Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node6Domains2 (.output 2)
    root0Node6Leaf_checked f h2
theorem root0Node5_cover : Covers root0Node5Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root0Node5Domains0 root0Node5Domains1 f hf root0Node5Step1_checked
  have hb : Covers root0Node5Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node5Domains1 root0Outputs 40
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node6_cover
    · exact root0Node7_cover
  exact hb f h1
theorem root0Node4_cover : Covers root0Node4Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root0Node4Domains0 root0Node4Domains1 f hf root0Node4Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root0Node4Domains1 root0Node4Domains2 f h1 root0Node4Step2_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node4Domains2 (.output 1)
    root0Node4Leaf_checked f h2
theorem root0Node3_cover : Covers root0Node3Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root0Node3Domains0 root0Node3Domains1 f hf root0Node3Step1_checked
  have hb : Covers root0Node3Domains1 constraints root0Outputs := by
    apply covers_of_branches root0Node3Domains1 root0Outputs 6
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node4_cover
    · exact root0Node5_cover
  exact hb f h1
theorem root0Node2_cover : Covers root0Node2Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root0Node2Domains0 root0Node2Domains1 f hf root0Node2Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root0Node2Domains1 root0Node2Domains2 f h1 root0Node2Step2_checked
  have h3 := solution_checkReplacement constraints table65 table65_member
    root0Node2Domains2 root0Node2Domains3 f h2 root0Node2Step3_checked
  have h4 := solution_checkReplacement constraints table21 table21_member
    root0Node2Domains3 root0Node2Domains4 f h3 root0Node2Step4_checked
  exact checkCover_sound 1 constraints root0Outputs root0Node2Domains4 (.output 0)
    root0Node2Leaf_checked f h4
theorem root0Node1_cover : Covers root0Node1Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root0Node1Domains0 root0Node1Domains1 f hf root0Node1Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node1Domains1 root0Node1Domains2 f h1 root0Node1Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root0Node1Domains2 root0Node1Domains3 f h2 root0Node1Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root0Node1Domains3 root0Node1Domains4 f h3 root0Node1Step4_checked
  have hb : Covers root0Node1Domains4 constraints root0Outputs := by
    apply covers_of_branches root0Node1Domains4 root0Outputs 5
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node2_cover
    · exact root0Node3_cover
  exact hb f h4
theorem root0Node0_cover : Covers root0Node0Domains0 constraints root0Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table45 table45_member
    root0Node0Domains0 root0Node0Domains1 f hf root0Node0Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root0Node0Domains1 root0Node0Domains2 f h1 root0Node0Step2_checked
  have h3 := solution_checkReplacement constraints table33 table33_member
    root0Node0Domains2 root0Node0Domains3 f h2 root0Node0Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root0Node0Domains3 root0Node0Domains4 f h3 root0Node0Step4_checked
  have h5 := solution_checkReplacement constraints table52 table52_member
    root0Node0Domains4 root0Node0Domains5 f h4 root0Node0Step5_checked
  have hb : Covers root0Node0Domains5 constraints root0Outputs := by
    apply covers_of_branches root0Node0Domains5 root0Outputs 46
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root0Node1_cover
    · exact root0Node12_cover
  exact hb f h5
theorem root0_table_cover : Covers (domains (0,0)) constraints root0Outputs := root0Node0_cover
theorem root0Family_count : root0Family.length = 60 := rfl
#print axioms root0_table_cover
end SpectreFinite.HexSearch.RadiusFive
