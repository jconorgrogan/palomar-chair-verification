module

public import SpectreFinite.RadiusFiveRoot1Part47

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root1Node116_cover : Covers root1Node116Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node116Domains0 root1Node116Domains1 f hf root1Node116Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node116Domains1 (.output 58)
    root1Node116Leaf_checked f h1
theorem root1Node115_cover : Covers root1Node115Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node115Domains0 root1Node115Domains1 f hf root1Node115Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node115Domains1 (.output 57)
    root1Node115Leaf_checked f h1
theorem root1Node114_cover : Covers root1Node114Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root1Node114Domains0 root1Node114Domains1 f hf root1Node114Step1_checked
  have hb : Covers root1Node114Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node114Domains1 root1Outputs 78
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node115_cover
    · exact root1Node116_cover
  exact hb f h1
theorem root1Node113_cover : Covers root1Node113Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node113Domains0 root1Node113Domains1 f hf root1Node113Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node113Domains1 (.output 56)
    root1Node113Leaf_checked f h1
theorem root1Node112_cover : Covers root1Node112Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node112Domains0 root1Node112Domains1 f hf root1Node112Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node112Domains1 (.output 55)
    root1Node112Leaf_checked f h1
theorem root1Node111_cover : Covers root1Node111Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root1Node111Domains0 root1Node111Domains1 f hf root1Node111Step1_checked
  have hb : Covers root1Node111Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node111Domains1 root1Outputs 78
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node112_cover
    · exact root1Node113_cover
  exact hb f h1
theorem root1Node110_cover : Covers root1Node110Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root1Node110Domains0 root1Node110Domains1 f hf root1Node110Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node110Domains1 root1Node110Domains2 f h1 root1Node110Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root1Node110Domains2 root1Node110Domains3 f h2 root1Node110Step3_checked
  have hb : Covers root1Node110Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node110Domains3 root1Outputs 5
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node111_cover
    · exact root1Node114_cover
  exact hb f h3
theorem root1Node109_cover : Covers root1Node109Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node109Domains0 root1Node109Domains1 f hf root1Node109Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node109Domains1 (.output 54)
    root1Node109Leaf_checked f h1
theorem root1Node108_cover : Covers root1Node108Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node108Domains0 root1Node108Domains1 f hf root1Node108Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node108Domains1 (.output 53)
    root1Node108Leaf_checked f h1
theorem root1Node107_cover : Covers root1Node107Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root1Node107Domains0 root1Node107Domains1 f hf root1Node107Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root1Node107Domains1 root1Node107Domains2 f h1 root1Node107Step2_checked
  have hb : Covers root1Node107Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node107Domains2 root1Outputs 78
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node108_cover
    · exact root1Node109_cover
  exact hb f h2
theorem root1Node106_cover : Covers root1Node106Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root1Node106Domains0 root1Node106Domains1 f hf root1Node106Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root1Node106Domains1 root1Node106Domains2 f h1 root1Node106Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node106Domains2 (.output 52)
    root1Node106Leaf_checked f h2
theorem root1Node105_cover : Covers root1Node105Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root1Node105Domains0 root1Node105Domains1 f hf root1Node105Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root1Node105Domains1 root1Node105Domains2 f h1 root1Node105Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node105Domains2 (.output 51)
    root1Node105Leaf_checked f h2
theorem root1Node104_cover : Covers root1Node104Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node104Domains0 root1Node104Domains1 f hf root1Node104Step1_checked
  have hb : Covers root1Node104Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node104Domains1 root1Outputs 40
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node105_cover
    · exact root1Node106_cover
  exact hb f h1
theorem root1Node103_cover : Covers root1Node103Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root1Node103Domains0 root1Node103Domains1 f hf root1Node103Step1_checked
  have hb : Covers root1Node103Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node103Domains1 root1Outputs 13
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node104_cover
    · exact root1Node107_cover
  exact hb f h1
theorem root1Node102_cover : Covers root1Node102Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root1Node102Domains0 root1Node102Domains1 f hf root1Node102Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node102Domains1 root1Node102Domains2 f h1 root1Node102Step2_checked
  have h3 := solution_checkReplacement constraints table19 table19_member
    root1Node102Domains2 root1Node102Domains3 f h2 root1Node102Step3_checked
  have h4 := solution_checkReplacement constraints table13 table13_member
    root1Node102Domains3 root1Node102Domains4 f h3 root1Node102Step4_checked
  have hb : Covers root1Node102Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node102Domains4 root1Outputs 2
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node103_cover
    · exact root1Node110_cover
  exact hb f h4
theorem root1Node101_cover : Covers root1Node101Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node101Domains0 root1Node101Domains1 f hf root1Node101Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node101Domains1 (.output 50)
    root1Node101Leaf_checked f h1
theorem root1Node100_cover : Covers root1Node100Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node100Domains0 root1Node100Domains1 f hf root1Node100Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node100Domains1 (.output 49)
    root1Node100Leaf_checked f h1
theorem root1Node99_cover : Covers root1Node99Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root1Node99Domains0 root1Node99Domains1 f hf root1Node99Step1_checked
  have hb : Covers root1Node99Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node99Domains1 root1Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node100_cover
    · exact root1Node101_cover
  exact hb f h1
theorem root1Node98_cover : Covers root1Node98Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root1Node98Domains0 root1Node98Domains1 f hf root1Node98Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root1Node98Domains1 root1Node98Domains2 f h1 root1Node98Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node98Domains2 (.output 48)
    root1Node98Leaf_checked f h2
theorem root1Node97_cover : Covers root1Node97Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node97Domains0 root1Node97Domains1 f hf root1Node97Step1_checked
  have hb : Covers root1Node97Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node97Domains1 root1Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node98_cover
    · exact root1Node99_cover
  exact hb f h1
theorem root1Node96_cover : Covers root1Node96Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node96Domains0 root1Node96Domains1 f hf root1Node96Step1_checked
  have h2 := solution_checkReplacement constraints table41 table41_member
    root1Node96Domains1 root1Node96Domains2 f h1 root1Node96Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node96Domains2 (.output 47)
    root1Node96Leaf_checked f h2
theorem root1Node95_cover : Covers root1Node95Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root1Node95Domains0 root1Node95Domains1 f hf root1Node95Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root1Node95Domains1 root1Node95Domains2 f h1 root1Node95Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root1Node95Domains2 root1Node95Domains3 f h2 root1Node95Step3_checked
  have hb : Covers root1Node95Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node95Domains3 root1Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node96_cover
    · exact root1Node97_cover
  exact hb f h3
theorem root1Node94_cover : Covers root1Node94Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root1Node94Domains0 root1Node94Domains1 f hf root1Node94Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node94Domains1 root1Node94Domains2 f h1 root1Node94Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root1Node94Domains2 root1Node94Domains3 f h2 root1Node94Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root1Node94Domains3 root1Node94Domains4 f h3 root1Node94Step4_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node94Domains4 (.output 46)
    root1Node94Leaf_checked f h4
theorem root1Node93_cover : Covers root1Node93Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root1Node93Domains0 root1Node93Domains1 f hf root1Node93Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node93Domains1 root1Node93Domains2 f h1 root1Node93Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root1Node93Domains2 root1Node93Domains3 f h2 root1Node93Step3_checked
  have hb : Covers root1Node93Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node93Domains3 root1Outputs 4
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node94_cover
    · exact root1Node95_cover
  exact hb f h3
theorem root1Node92_cover : Covers root1Node92Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root1Node92Domains0 root1Node92Domains1 f hf root1Node92Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root1Node92Domains1 root1Node92Domains2 f h1 root1Node92Step2_checked
  have hb : Covers root1Node92Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node92Domains2 root1Outputs 0
    intro s hs
    change s ∈ [(2,0),(4,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node93_cover
    · exact root1Node102_cover
  exact hb f h2
theorem root1Node91_cover : Covers root1Node91Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node91Domains0 root1Node91Domains1 f hf root1Node91Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node91Domains1 (.output 45)
    root1Node91Leaf_checked f h1
theorem root1Node90_cover : Covers root1Node90Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node90Domains0 root1Node90Domains1 f hf root1Node90Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node90Domains1 (.output 44)
    root1Node90Leaf_checked f h1
theorem root1Node89_cover : Covers root1Node89Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root1Node89Domains0 root1Node89Domains1 f hf root1Node89Step1_checked
  have hb : Covers root1Node89Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node89Domains1 root1Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node90_cover
    · exact root1Node91_cover
  exact hb f h1
theorem root1Node88_cover : Covers root1Node88Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root1Node88Domains0 root1Node88Domains1 f hf root1Node88Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root1Node88Domains1 root1Node88Domains2 f h1 root1Node88Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node88Domains2 (.output 43)
    root1Node88Leaf_checked f h2
theorem root1Node87_cover : Covers root1Node87Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node87Domains0 root1Node87Domains1 f hf root1Node87Step1_checked
  have hb : Covers root1Node87Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node87Domains1 root1Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node88_cover
    · exact root1Node89_cover
  exact hb f h1
theorem root1Node86_cover : Covers root1Node86Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node86Domains0 root1Node86Domains1 f hf root1Node86Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node86Domains1 (.output 42)
    root1Node86Leaf_checked f h1
theorem root1Node85_cover : Covers root1Node85Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node85Domains0 root1Node85Domains1 f hf root1Node85Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node85Domains1 (.output 41)
    root1Node85Leaf_checked f h1
theorem root1Node84_cover : Covers root1Node84Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root1Node84Domains0 root1Node84Domains1 f hf root1Node84Step1_checked
  have hb : Covers root1Node84Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node84Domains1 root1Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node85_cover
    · exact root1Node86_cover
  exact hb f h1
theorem root1Node83_cover : Covers root1Node83Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root1Node83Domains0 root1Node83Domains1 f hf root1Node83Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root1Node83Domains1 root1Node83Domains2 f h1 root1Node83Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node83Domains2 (.output 40)
    root1Node83Leaf_checked f h2
theorem root1Node82_cover : Covers root1Node82Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node82Domains0 root1Node82Domains1 f hf root1Node82Step1_checked
  have hb : Covers root1Node82Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node82Domains1 root1Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node83_cover
    · exact root1Node84_cover
  exact hb f h1
theorem root1Node81_cover : Covers root1Node81Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node81Domains0 root1Node81Domains1 f hf root1Node81Step1_checked
  have hb : Covers root1Node81Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node81Domains1 root1Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node82_cover
    · exact root1Node87_cover
  exact hb f h1
theorem root1Node80_cover : Covers root1Node80Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node80Domains0 root1Node80Domains1 f hf root1Node80Step1_checked
  have h2 := solution_checkReplacement constraints table41 table41_member
    root1Node80Domains1 root1Node80Domains2 f h1 root1Node80Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node80Domains2 (.output 39)
    root1Node80Leaf_checked f h2
theorem root1Node79_cover : Covers root1Node79Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root1Node79Domains0 root1Node79Domains1 f hf root1Node79Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root1Node79Domains1 root1Node79Domains2 f h1 root1Node79Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root1Node79Domains2 root1Node79Domains3 f h2 root1Node79Step3_checked
  have hb : Covers root1Node79Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node79Domains3 root1Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node80_cover
    · exact root1Node81_cover
  exact hb f h3
theorem root1Node78_cover : Covers root1Node78Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root1Node78Domains0 root1Node78Domains1 f hf root1Node78Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node78Domains1 root1Node78Domains2 f h1 root1Node78Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root1Node78Domains2 root1Node78Domains3 f h2 root1Node78Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root1Node78Domains3 root1Node78Domains4 f h3 root1Node78Step4_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node78Domains4 (.output 38)
    root1Node78Leaf_checked f h4
theorem root1Node77_cover : Covers root1Node77Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root1Node77Domains0 root1Node77Domains1 f hf root1Node77Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node77Domains1 root1Node77Domains2 f h1 root1Node77Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root1Node77Domains2 root1Node77Domains3 f h2 root1Node77Step3_checked
  have hb : Covers root1Node77Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node77Domains3 root1Outputs 4
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node78_cover
    · exact root1Node79_cover
  exact hb f h3
theorem root1Node76_cover : Covers root1Node76Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root1Node76Domains0 root1Node76Domains1 f hf root1Node76Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root1Node76Domains1 root1Node76Domains2 f h1 root1Node76Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root1Node76Domains2 root1Node76Domains3 f h2 root1Node76Step3_checked
  have hb : Covers root1Node76Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node76Domains3 root1Outputs 1
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node77_cover
    · exact root1Node92_cover
  exact hb f h3
theorem root1Node75_cover : Covers root1Node75Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node75Domains0 root1Node75Domains1 f hf root1Node75Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node75Domains1 (.output 37)
    root1Node75Leaf_checked f h1
theorem root1Node74_cover : Covers root1Node74Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node74Domains0 root1Node74Domains1 f hf root1Node74Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node74Domains1 (.output 36)
    root1Node74Leaf_checked f h1
theorem root1Node73_cover : Covers root1Node73Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node73Domains0 root1Node73Domains1 f hf root1Node73Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node73Domains1 (.output 35)
    root1Node73Leaf_checked f h1
theorem root1Node72_cover : Covers root1Node72Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node72Domains0 root1Node72Domains1 f hf root1Node72Step1_checked
  have hb : Covers root1Node72Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node72Domains1 root1Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node73_cover
    · exact root1Node74_cover
  exact hb f h1
theorem root1Node71_cover : Covers root1Node71Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node71Domains0 root1Node71Domains1 f hf root1Node71Step1_checked
  have hb : Covers root1Node71Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node71Domains1 root1Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node72_cover
    · exact root1Node75_cover
  exact hb f h1
theorem root1Node70_cover : Covers root1Node70Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node70Domains0 root1Node70Domains1 f hf root1Node70Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node70Domains1 (.output 34)
    root1Node70Leaf_checked f h1
theorem root1Node69_cover : Covers root1Node69Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node69Domains0 root1Node69Domains1 f hf root1Node69Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node69Domains1 (.output 33)
    root1Node69Leaf_checked f h1
theorem root1Node68_cover : Covers root1Node68Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node68Domains0 root1Node68Domains1 f hf root1Node68Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node68Domains1 (.output 32)
    root1Node68Leaf_checked f h1
theorem root1Node67_cover : Covers root1Node67Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node67Domains0 root1Node67Domains1 f hf root1Node67Step1_checked
  have hb : Covers root1Node67Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node67Domains1 root1Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node68_cover
    · exact root1Node69_cover
  exact hb f h1
theorem root1Node66_cover : Covers root1Node66Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node66Domains0 root1Node66Domains1 f hf root1Node66Step1_checked
  have hb : Covers root1Node66Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node66Domains1 root1Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node67_cover
    · exact root1Node70_cover
  exact hb f h1
theorem root1Node65_cover : Covers root1Node65Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node65Domains0 root1Node65Domains1 f hf root1Node65Step1_checked
  have hb : Covers root1Node65Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node65Domains1 root1Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node66_cover
    · exact root1Node71_cover
  exact hb f h1
theorem root1Node64_cover : Covers root1Node64Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node64Domains0 root1Node64Domains1 f hf root1Node64Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root1Node64Domains1 root1Node64Domains2 f h1 root1Node64Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node64Domains2 (.output 31)
    root1Node64Leaf_checked f h2
theorem root1Node63_cover : Covers root1Node63Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node63Domains0 root1Node63Domains1 f hf root1Node63Step1_checked
  have hb : Covers root1Node63Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node63Domains1 root1Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node64_cover
    · exact root1Node65_cover
  exact hb f h1
theorem root1Node62_cover : Covers root1Node62Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node62Domains0 root1Node62Domains1 f hf root1Node62Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node62Domains1 (.output 30)
    root1Node62Leaf_checked f h1
theorem root1Node61_cover : Covers root1Node61Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root1Node61Domains0 root1Node61Domains1 f hf root1Node61Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node61Domains1 (.output 29)
    root1Node61Leaf_checked f h1
theorem root1Node60_cover : Covers root1Node60Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root1Node60Domains0 root1Node60Domains1 f hf root1Node60Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node60Domains1 root1Node60Domains2 f h1 root1Node60Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root1Node60Domains2 root1Node60Domains3 f h2 root1Node60Step3_checked
  have hb : Covers root1Node60Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node60Domains3 root1Outputs 5
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node61_cover
    · exact root1Node62_cover
  exact hb f h3
theorem root1Node59_cover : Covers root1Node59Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root1Node59Domains0 root1Node59Domains1 f hf root1Node59Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root1Node59Domains1 root1Node59Domains2 f h1 root1Node59Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root1Node59Domains2 root1Node59Domains3 f h2 root1Node59Step3_checked
  have h4 := solution_checkReplacement constraints table51 table51_member
    root1Node59Domains3 root1Node59Domains4 f h3 root1Node59Step4_checked
  have hb : Covers root1Node59Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node59Domains4 root1Outputs 4
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node60_cover
    · exact root1Node63_cover
  exact hb f h4
theorem root1Node58_cover : Covers root1Node58Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root1Node58Domains0 root1Node58Domains1 f hf root1Node58Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node58Domains1 root1Node58Domains2 f h1 root1Node58Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root1Node58Domains2 root1Node58Domains3 f h2 root1Node58Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root1Node58Domains3 root1Node58Domains4 f h3 root1Node58Step4_checked
  have hb : Covers root1Node58Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node58Domains4 root1Outputs 3
    intro s hs
    change s ∈ [(7,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node59_cover
    · exact root1Node76_cover
  exact hb f h4
theorem root1Node57_cover : Covers root1Node57Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node57Domains0 root1Node57Domains1 f hf root1Node57Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node57Domains1 (.output 28)
    root1Node57Leaf_checked f h1
theorem root1Node56_cover : Covers root1Node56Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node56Domains0 root1Node56Domains1 f hf root1Node56Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node56Domains1 (.output 27)
    root1Node56Leaf_checked f h1
theorem root1Node55_cover : Covers root1Node55Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node55Domains0 root1Node55Domains1 f hf root1Node55Step1_checked
  have hb : Covers root1Node55Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node55Domains1 root1Outputs 81
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node56_cover
    · exact root1Node57_cover
  exact hb f h1
theorem root1Node54_cover : Covers root1Node54Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node54Domains0 root1Node54Domains1 f hf root1Node54Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root1Node54Domains1 root1Node54Domains2 f h1 root1Node54Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node54Domains2 (.output 26)
    root1Node54Leaf_checked f h2
theorem root1Node53_cover : Covers root1Node53Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node53Domains0 root1Node53Domains1 f hf root1Node53Step1_checked
  have hb : Covers root1Node53Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node53Domains1 root1Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node54_cover
    · exact root1Node55_cover
  exact hb f h1
theorem root1Node52_cover : Covers root1Node52Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root1Node52Domains0 root1Node52Domains1 f hf root1Node52Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root1Node52Domains1 root1Node52Domains2 f h1 root1Node52Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node52Domains2 (.output 25)
    root1Node52Leaf_checked f h2
theorem root1Node51_cover : Covers root1Node51Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node51Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node51Domains0 root1Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node52_cover
    · exact root1Node53_cover
  exact hb f hf
theorem root1Node50_cover : Covers root1Node50Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node50Domains0 root1Node50Domains1 f hf root1Node50Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root1Node50Domains1 root1Node50Domains2 f h1 root1Node50Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node50Domains2 (.output 24)
    root1Node50Leaf_checked f h2
theorem root1Node49_cover : Covers root1Node49Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node49Domains0 root1Node49Domains1 f hf root1Node49Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root1Node49Domains1 root1Node49Domains2 f h1 root1Node49Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root1Node49Domains2 root1Node49Domains3 f h2 root1Node49Step3_checked
  have hb : Covers root1Node49Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node49Domains3 root1Outputs 20
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node50_cover
    · exact root1Node51_cover
  exact hb f h3
theorem root1Node48_cover : Covers root1Node48Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node48Domains0 root1Node48Domains1 f hf root1Node48Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root1Node48Domains1 root1Node48Domains2 f h1 root1Node48Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root1Node48Domains2 root1Node48Domains3 f h2 root1Node48Step3_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node48Domains3 (.output 23)
    root1Node48Leaf_checked f h3
theorem root1Node47_cover : Covers root1Node47Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root1Node47Domains0 root1Node47Domains1 f hf root1Node47Step1_checked
  have hb : Covers root1Node47Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node47Domains1 root1Outputs 28
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node48_cover
    · exact root1Node49_cover
  exact hb f h1
theorem root1Node46_cover : Covers root1Node46Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node46Domains0 root1Node46Domains1 f hf root1Node46Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node46Domains1 (.output 22)
    root1Node46Leaf_checked f h1
theorem root1Node45_cover : Covers root1Node45Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node45Domains0 root1Node45Domains1 f hf root1Node45Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node45Domains1 (.output 21)
    root1Node45Leaf_checked f h1
theorem root1Node44_cover : Covers root1Node44Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node44Domains0 root1Node44Domains1 f hf root1Node44Step1_checked
  have hb : Covers root1Node44Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node44Domains1 root1Outputs 81
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node45_cover
    · exact root1Node46_cover
  exact hb f h1
theorem root1Node43_cover : Covers root1Node43Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node43Domains0 root1Node43Domains1 f hf root1Node43Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root1Node43Domains1 root1Node43Domains2 f h1 root1Node43Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node43Domains2 (.output 20)
    root1Node43Leaf_checked f h2
theorem root1Node42_cover : Covers root1Node42Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node42Domains0 root1Node42Domains1 f hf root1Node42Step1_checked
  have hb : Covers root1Node42Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node42Domains1 root1Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node43_cover
    · exact root1Node44_cover
  exact hb f h1
theorem root1Node41_cover : Covers root1Node41Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root1Node41Domains0 root1Node41Domains1 f hf root1Node41Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root1Node41Domains1 root1Node41Domains2 f h1 root1Node41Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node41Domains2 (.output 19)
    root1Node41Leaf_checked f h2
theorem root1Node40_cover : Covers root1Node40Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node40Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node40Domains0 root1Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node41_cover
    · exact root1Node42_cover
  exact hb f hf
theorem root1Node39_cover : Covers root1Node39Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node39Domains0 root1Node39Domains1 f hf root1Node39Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root1Node39Domains1 root1Node39Domains2 f h1 root1Node39Step2_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node39Domains2 (.output 18)
    root1Node39Leaf_checked f h2
theorem root1Node38_cover : Covers root1Node38Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node38Domains0 root1Node38Domains1 f hf root1Node38Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root1Node38Domains1 root1Node38Domains2 f h1 root1Node38Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root1Node38Domains2 root1Node38Domains3 f h2 root1Node38Step3_checked
  have hb : Covers root1Node38Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node38Domains3 root1Outputs 20
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node39_cover
    · exact root1Node40_cover
  exact hb f h3
theorem root1Node37_cover : Covers root1Node37Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node37Domains0 root1Node37Domains1 f hf root1Node37Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root1Node37Domains1 root1Node37Domains2 f h1 root1Node37Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root1Node37Domains2 root1Node37Domains3 f h2 root1Node37Step3_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node37Domains3 (.output 17)
    root1Node37Leaf_checked f h3
theorem root1Node36_cover : Covers root1Node36Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root1Node36Domains0 root1Node36Domains1 f hf root1Node36Step1_checked
  have hb : Covers root1Node36Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node36Domains1 root1Outputs 28
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node37_cover
    · exact root1Node38_cover
  exact hb f h1
theorem root1Node35_cover : Covers root1Node35Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root1Node35Domains0 root1Node35Domains1 f hf root1Node35Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node35Domains1 root1Node35Domains2 f h1 root1Node35Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root1Node35Domains2 root1Node35Domains3 f h2 root1Node35Step3_checked
  have h4 := solution_checkReplacement constraints table13 table13_member
    root1Node35Domains3 root1Node35Domains4 f h3 root1Node35Step4_checked
  have hb : Covers root1Node35Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node35Domains4 root1Outputs 1
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node36_cover
    · exact root1Node47_cover
  exact hb f h4
theorem root1Node34_cover : Covers root1Node34Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node34Domains0 root1Node34Domains1 f hf root1Node34Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node34Domains1 (.output 16)
    root1Node34Leaf_checked f h1
theorem root1Node33_cover : Covers root1Node33Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node33Domains0 root1Node33Domains1 f hf root1Node33Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node33Domains1 (.output 15)
    root1Node33Leaf_checked f h1
theorem root1Node32_cover : Covers root1Node32Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node32Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node32Domains0 root1Outputs 84
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node33_cover
    · exact root1Node34_cover
  exact hb f hf
theorem root1Node31_cover : Covers root1Node31Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node31Domains0 root1Node31Domains1 f hf root1Node31Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node31Domains1 (.output 14)
    root1Node31Leaf_checked f h1
theorem root1Node30_cover : Covers root1Node30Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node30Domains0 root1Node30Domains1 f hf root1Node30Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node30Domains1 (.output 13)
    root1Node30Leaf_checked f h1
theorem root1Node29_cover : Covers root1Node29Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node29Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node29Domains0 root1Outputs 84
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node30_cover
    · exact root1Node31_cover
  exact hb f hf
theorem root1Node28_cover : Covers root1Node28Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node28Domains0 root1Node28Domains1 f hf root1Node28Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root1Node28Domains1 root1Node28Domains2 f h1 root1Node28Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root1Node28Domains2 root1Node28Domains3 f h2 root1Node28Step3_checked
  have hb : Covers root1Node28Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node28Domains3 root1Outputs 20
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node29_cover
    · exact root1Node32_cover
  exact hb f h3
theorem root1Node27_cover : Covers root1Node27Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node27Domains0 root1Node27Domains1 f hf root1Node27Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node27Domains1 (.output 12)
    root1Node27Leaf_checked f h1
theorem root1Node26_cover : Covers root1Node26Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node26Domains0 root1Node26Domains1 f hf root1Node26Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node26Domains1 (.output 11)
    root1Node26Leaf_checked f h1
theorem root1Node25_cover : Covers root1Node25Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node25Domains0 root1Node25Domains1 f hf root1Node25Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node25Domains1 (.output 10)
    root1Node25Leaf_checked f h1
theorem root1Node24_cover : Covers root1Node24Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node24Domains0 root1Node24Domains1 f hf root1Node24Step1_checked
  have hb : Covers root1Node24Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node24Domains1 root1Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node25_cover
    · exact root1Node26_cover
  exact hb f h1
theorem root1Node23_cover : Covers root1Node23Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node23Domains0 root1Node23Domains1 f hf root1Node23Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root1Node23Domains1 root1Node23Domains2 f h1 root1Node23Step2_checked
  have hb : Covers root1Node23Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node23Domains2 root1Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node24_cover
    · exact root1Node27_cover
  exact hb f h2
theorem root1Node22_cover : Covers root1Node22Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table41 table41_member
    root1Node22Domains0 root1Node22Domains1 f hf root1Node22Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root1Node22Domains1 root1Node22Domains2 f h1 root1Node22Step2_checked
  have hb : Covers root1Node22Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node22Domains2 root1Outputs 28
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node23_cover
    · exact root1Node28_cover
  exact hb f h2
theorem root1Node21_cover : Covers root1Node21Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node21Domains0 root1Node21Domains1 f hf root1Node21Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node21Domains1 (.output 9)
    root1Node21Leaf_checked f h1
theorem root1Node20_cover : Covers root1Node20Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node20Domains0 root1Node20Domains1 f hf root1Node20Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node20Domains1 (.output 8)
    root1Node20Leaf_checked f h1
theorem root1Node19_cover : Covers root1Node19Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node19Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node19Domains0 root1Outputs 84
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node20_cover
    · exact root1Node21_cover
  exact hb f hf
theorem root1Node18_cover : Covers root1Node18Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node18Domains0 root1Node18Domains1 f hf root1Node18Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node18Domains1 (.output 7)
    root1Node18Leaf_checked f h1
theorem root1Node17_cover : Covers root1Node17Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node17Domains0 root1Node17Domains1 f hf root1Node17Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node17Domains1 (.output 6)
    root1Node17Leaf_checked f h1
theorem root1Node16_cover : Covers root1Node16Domains0 constraints root1Outputs := by
  intro f hf
  have hb : Covers root1Node16Domains0 constraints root1Outputs := by
    apply covers_of_branches root1Node16Domains0 root1Outputs 84
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node17_cover
    · exact root1Node18_cover
  exact hb f hf
theorem root1Node15_cover : Covers root1Node15Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root1Node15Domains0 root1Node15Domains1 f hf root1Node15Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root1Node15Domains1 root1Node15Domains2 f h1 root1Node15Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root1Node15Domains2 root1Node15Domains3 f h2 root1Node15Step3_checked
  have hb : Covers root1Node15Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node15Domains3 root1Outputs 20
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node16_cover
    · exact root1Node19_cover
  exact hb f h3
theorem root1Node14_cover : Covers root1Node14Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node14Domains0 root1Node14Domains1 f hf root1Node14Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node14Domains1 (.output 5)
    root1Node14Leaf_checked f h1
theorem root1Node13_cover : Covers root1Node13Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root1Node13Domains0 root1Node13Domains1 f hf root1Node13Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node13Domains1 (.output 4)
    root1Node13Leaf_checked f h1
theorem root1Node12_cover : Covers root1Node12Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node12Domains0 root1Node12Domains1 f hf root1Node12Step1_checked
  have hb : Covers root1Node12Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node12Domains1 root1Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node13_cover
    · exact root1Node14_cover
  exact hb f h1
theorem root1Node11_cover : Covers root1Node11Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node11Domains0 root1Node11Domains1 f hf root1Node11Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node11Domains1 (.output 3)
    root1Node11Leaf_checked f h1
theorem root1Node10_cover : Covers root1Node10Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node10Domains0 root1Node10Domains1 f hf root1Node10Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node10Domains1 (.output 2)
    root1Node10Leaf_checked f h1
theorem root1Node9_cover : Covers root1Node9Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root1Node9Domains0 root1Node9Domains1 f hf root1Node9Step1_checked
  have hb : Covers root1Node9Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node9Domains1 root1Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node10_cover
    · exact root1Node11_cover
  exact hb f h1
theorem root1Node8_cover : Covers root1Node8Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root1Node8Domains0 root1Node8Domains1 f hf root1Node8Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root1Node8Domains1 root1Node8Domains2 f h1 root1Node8Step2_checked
  have hb : Covers root1Node8Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node8Domains2 root1Outputs 54
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node9_cover
    · exact root1Node12_cover
  exact hb f h2
theorem root1Node7_cover : Covers root1Node7Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node7Domains0 root1Node7Domains1 f hf root1Node7Step1_checked
  have hb : Covers root1Node7Domains1 constraints root1Outputs := by
    apply covers_of_branches root1Node7Domains1 root1Outputs 28
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node8_cover
    · exact root1Node15_cover
  exact hb f h1
theorem root1Node6_cover : Covers root1Node6Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root1Node6Domains0 root1Node6Domains1 f hf root1Node6Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root1Node6Domains1 root1Node6Domains2 f h1 root1Node6Step2_checked
  have hb : Covers root1Node6Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node6Domains2 root1Outputs 6
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node7_cover
    · exact root1Node22_cover
  exact hb f h2
theorem root1Node5_cover : Covers root1Node5Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node5Domains0 root1Node5Domains1 f hf root1Node5Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node5Domains1 (.output 1)
    root1Node5Leaf_checked f h1
theorem root1Node4_cover : Covers root1Node4Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root1Node4Domains0 root1Node4Domains1 f hf root1Node4Step1_checked
  exact checkCover_sound 1 constraints root1Outputs root1Node4Domains1 (.output 0)
    root1Node4Leaf_checked f h1
theorem root1Node3_cover : Covers root1Node3Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root1Node3Domains0 root1Node3Domains1 f hf root1Node3Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root1Node3Domains1 root1Node3Domains2 f h1 root1Node3Step2_checked
  have hb : Covers root1Node3Domains2 constraints root1Outputs := by
    apply covers_of_branches root1Node3Domains2 root1Outputs 6
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node4_cover
    · exact root1Node5_cover
  exact hb f h2
theorem root1Node2_cover : Covers root1Node2Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root1Node2Domains0 root1Node2Domains1 f hf root1Node2Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root1Node2Domains1 root1Node2Domains2 f h1 root1Node2Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root1Node2Domains2 root1Node2Domains3 f h2 root1Node2Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root1Node2Domains3 root1Node2Domains4 f h3 root1Node2Step4_checked
  have hb : Covers root1Node2Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node2Domains4 root1Outputs 4
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node3_cover
    · exact root1Node6_cover
  exact hb f h4
theorem root1Node1_cover : Covers root1Node1Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root1Node1Domains0 root1Node1Domains1 f hf root1Node1Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root1Node1Domains1 root1Node1Domains2 f h1 root1Node1Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root1Node1Domains2 root1Node1Domains3 f h2 root1Node1Step3_checked
  have hb : Covers root1Node1Domains3 constraints root1Outputs := by
    apply covers_of_branches root1Node1Domains3 root1Outputs 0
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node2_cover
    · exact root1Node35_cover
  exact hb f h3
theorem root1Node0_cover : Covers root1Node0Domains0 constraints root1Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root1Node0Domains0 root1Node0Domains1 f hf root1Node0Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root1Node0Domains1 root1Node0Domains2 f h1 root1Node0Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root1Node0Domains2 root1Node0Domains3 f h2 root1Node0Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root1Node0Domains3 root1Node0Domains4 f h3 root1Node0Step4_checked
  have hb : Covers root1Node0Domains4 constraints root1Outputs := by
    apply covers_of_branches root1Node0Domains4 root1Outputs 17
    intro s hs
    change s ∈ [(4,1),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root1Node1_cover
    · exact root1Node58_cover
  exact hb f h4
theorem root1_table_cover : Covers (domains (1,0)) constraints root1Outputs := root1Node0_cover
theorem root1Family_count : root1Family.length = 59 := rfl
#print axioms root1_table_cover
end SpectreFinite.HexSearch.RadiusFive
