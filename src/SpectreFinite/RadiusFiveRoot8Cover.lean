module

public import SpectreFinite.RadiusFiveRoot8Part51

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root8Node138_cover : Covers root8Node138Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node138Domains0 root8Node138Domains1 f hf root8Node138Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node138Domains1 (.output 69)
    root8Node138Leaf_checked f h1
theorem root8Node137_cover : Covers root8Node137Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node137Domains0 root8Node137Domains1 f hf root8Node137Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node137Domains1 (.output 68)
    root8Node137Leaf_checked f h1
theorem root8Node136_cover : Covers root8Node136Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node136Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node136Domains0 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node137_cover
    · exact root8Node138_cover
  exact hb f hf
theorem root8Node135_cover : Covers root8Node135Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node135Domains0 root8Node135Domains1 f hf root8Node135Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node135Domains1 (.output 67)
    root8Node135Leaf_checked f h1
theorem root8Node134_cover : Covers root8Node134Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node134Domains0 root8Node134Domains1 f hf root8Node134Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node134Domains1 (.output 66)
    root8Node134Leaf_checked f h1
theorem root8Node133_cover : Covers root8Node133Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node133Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node133Domains0 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node134_cover
    · exact root8Node135_cover
  exact hb f hf
theorem root8Node132_cover : Covers root8Node132Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node132Domains0 root8Node132Domains1 f hf root8Node132Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root8Node132Domains1 root8Node132Domains2 f h1 root8Node132Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root8Node132Domains2 root8Node132Domains3 f h2 root8Node132Step3_checked
  have hb : Covers root8Node132Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node132Domains3 root8Outputs 12
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node133_cover
    · exact root8Node136_cover
  exact hb f h3
theorem root8Node131_cover : Covers root8Node131Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node131Domains0 root8Node131Domains1 f hf root8Node131Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node131Domains1 (.output 65)
    root8Node131Leaf_checked f h1
theorem root8Node130_cover : Covers root8Node130Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node130Domains0 root8Node130Domains1 f hf root8Node130Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node130Domains1 (.output 64)
    root8Node130Leaf_checked f h1
theorem root8Node129_cover : Covers root8Node129Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node129Domains0 root8Node129Domains1 f hf root8Node129Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root8Node129Domains1 root8Node129Domains2 f h1 root8Node129Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root8Node129Domains2 root8Node129Domains3 f h2 root8Node129Step3_checked
  have hb : Covers root8Node129Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node129Domains3 root8Outputs 62
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node130_cover
    · exact root8Node131_cover
  exact hb f h3
theorem root8Node128_cover : Covers root8Node128Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root8Node128Domains0 root8Node128Domains1 f hf root8Node128Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node128Domains1 root8Node128Domains2 f h1 root8Node128Step2_checked
  have h3 := solution_checkReplacement constraints table27 table27_member
    root8Node128Domains2 root8Node128Domains3 f h2 root8Node128Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root8Node128Domains3 root8Node128Domains4 f h3 root8Node128Step4_checked
  have hb : Covers root8Node128Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node128Domains4 root8Outputs 19
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node129_cover
    · exact root8Node132_cover
  exact hb f h4
theorem root8Node127_cover : Covers root8Node127Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node127Domains0 root8Node127Domains1 f hf root8Node127Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root8Node127Domains1 root8Node127Domains2 f h1 root8Node127Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node127Domains2 (.output 63)
    root8Node127Leaf_checked f h2
theorem root8Node126_cover : Covers root8Node126Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node126Domains0 root8Node126Domains1 f hf root8Node126Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node126Domains1 (.output 62)
    root8Node126Leaf_checked f h1
theorem root8Node125_cover : Covers root8Node125Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node125Domains0 root8Node125Domains1 f hf root8Node125Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node125Domains1 (.output 61)
    root8Node125Leaf_checked f h1
theorem root8Node124_cover : Covers root8Node124Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node124Domains0 root8Node124Domains1 f hf root8Node124Step1_checked
  have hb : Covers root8Node124Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node124Domains1 root8Outputs 70
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node125_cover
    · exact root8Node126_cover
  exact hb f h1
theorem root8Node123_cover : Covers root8Node123Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node123Domains0 root8Node123Domains1 f hf root8Node123Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root8Node123Domains1 root8Node123Domains2 f h1 root8Node123Step2_checked
  have hb : Covers root8Node123Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node123Domains2 root8Outputs 20
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node124_cover
    · exact root8Node127_cover
  exact hb f h2
theorem root8Node122_cover : Covers root8Node122Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node122Domains0 root8Node122Domains1 f hf root8Node122Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node122Domains1 (.output 60)
    root8Node122Leaf_checked f h1
theorem root8Node121_cover : Covers root8Node121Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node121Domains0 root8Node121Domains1 f hf root8Node121Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node121Domains1 (.output 59)
    root8Node121Leaf_checked f h1
theorem root8Node120_cover : Covers root8Node120Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node120Domains0 root8Node120Domains1 f hf root8Node120Step1_checked
  have hb : Covers root8Node120Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node120Domains1 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node121_cover
    · exact root8Node122_cover
  exact hb f h1
theorem root8Node119_cover : Covers root8Node119Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node119Domains0 root8Node119Domains1 f hf root8Node119Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node119Domains1 (.output 58)
    root8Node119Leaf_checked f h1
theorem root8Node118_cover : Covers root8Node118Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node118Domains0 root8Node118Domains1 f hf root8Node118Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node118Domains1 (.output 57)
    root8Node118Leaf_checked f h1
theorem root8Node117_cover : Covers root8Node117Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node117Domains0 root8Node117Domains1 f hf root8Node117Step1_checked
  have hb : Covers root8Node117Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node117Domains1 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node118_cover
    · exact root8Node119_cover
  exact hb f h1
theorem root8Node116_cover : Covers root8Node116Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node116Domains0 root8Node116Domains1 f hf root8Node116Step1_checked
  have hb : Covers root8Node116Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node116Domains1 root8Outputs 20
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node117_cover
    · exact root8Node120_cover
  exact hb f h1
theorem root8Node115_cover : Covers root8Node115Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root8Node115Domains0 root8Node115Domains1 f hf root8Node115Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root8Node115Domains1 root8Node115Domains2 f h1 root8Node115Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root8Node115Domains2 root8Node115Domains3 f h2 root8Node115Step3_checked
  have hb : Covers root8Node115Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node115Domains3 root8Outputs 13
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node116_cover
    · exact root8Node123_cover
  exact hb f h3
theorem root8Node114_cover : Covers root8Node114Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node114Domains0 root8Node114Domains1 f hf root8Node114Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node114Domains1 (.output 56)
    root8Node114Leaf_checked f h1
theorem root8Node113_cover : Covers root8Node113Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node113Domains0 root8Node113Domains1 f hf root8Node113Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node113Domains1 (.output 55)
    root8Node113Leaf_checked f h1
theorem root8Node112_cover : Covers root8Node112Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node112Domains0 root8Node112Domains1 f hf root8Node112Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root8Node112Domains1 root8Node112Domains2 f h1 root8Node112Step2_checked
  have hb : Covers root8Node112Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node112Domains2 root8Outputs 62
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node113_cover
    · exact root8Node114_cover
  exact hb f h2
theorem root8Node111_cover : Covers root8Node111Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node111Domains0 root8Node111Domains1 f hf root8Node111Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node111Domains1 (.output 54)
    root8Node111Leaf_checked f h1
theorem root8Node110_cover : Covers root8Node110Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node110Domains0 root8Node110Domains1 f hf root8Node110Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node110Domains1 (.output 53)
    root8Node110Leaf_checked f h1
theorem root8Node109_cover : Covers root8Node109Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node109Domains0 root8Node109Domains1 f hf root8Node109Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root8Node109Domains1 root8Node109Domains2 f h1 root8Node109Step2_checked
  have hb : Covers root8Node109Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node109Domains2 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node110_cover
    · exact root8Node111_cover
  exact hb f h2
theorem root8Node108_cover : Covers root8Node108Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node108Domains0 root8Node108Domains1 f hf root8Node108Step1_checked
  have hb : Covers root8Node108Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node108Domains1 root8Outputs 59
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node109_cover
    · exact root8Node112_cover
  exact hb f h1
theorem root8Node107_cover : Covers root8Node107Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node107Domains0 root8Node107Domains1 f hf root8Node107Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node107Domains1 (.output 52)
    root8Node107Leaf_checked f h1
theorem root8Node106_cover : Covers root8Node106Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node106Domains0 root8Node106Domains1 f hf root8Node106Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node106Domains1 (.output 51)
    root8Node106Leaf_checked f h1
theorem root8Node105_cover : Covers root8Node105Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node105Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node105Domains0 root8Outputs 70
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node106_cover
    · exact root8Node107_cover
  exact hb f hf
theorem root8Node104_cover : Covers root8Node104Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node104Domains0 root8Node104Domains1 f hf root8Node104Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node104Domains1 (.output 50)
    root8Node104Leaf_checked f h1
theorem root8Node103_cover : Covers root8Node103Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node103Domains0 root8Node103Domains1 f hf root8Node103Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node103Domains1 (.output 49)
    root8Node103Leaf_checked f h1
theorem root8Node102_cover : Covers root8Node102Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node102Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node102Domains0 root8Outputs 70
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node103_cover
    · exact root8Node104_cover
  exact hb f hf
theorem root8Node101_cover : Covers root8Node101Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node101Domains0 root8Node101Domains1 f hf root8Node101Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root8Node101Domains1 root8Node101Domains2 f h1 root8Node101Step2_checked
  have hb : Covers root8Node101Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node101Domains2 root8Outputs 13
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node102_cover
    · exact root8Node105_cover
  exact hb f h2
theorem root8Node100_cover : Covers root8Node100Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table27 table27_member
    root8Node100Domains0 root8Node100Domains1 f hf root8Node100Step1_checked
  have hb : Covers root8Node100Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node100Domains1 root8Outputs 21
    intro s hs
    change s ∈ [(0,1),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node101_cover
    · exact root8Node108_cover
  exact hb f h1
theorem root8Node99_cover : Covers root8Node99Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node99Domains0 root8Node99Domains1 f hf root8Node99Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root8Node99Domains1 root8Node99Domains2 f h1 root8Node99Step2_checked
  have hb : Covers root8Node99Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node99Domains2 root8Outputs 5
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node100_cover
    · exact root8Node115_cover
  exact hb f h2
theorem root8Node98_cover : Covers root8Node98Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root8Node98Domains0 root8Node98Domains1 f hf root8Node98Step1_checked
  have hb : Covers root8Node98Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node98Domains1 root8Outputs 4
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node99_cover
    · exact root8Node128_cover
  exact hb f h1
theorem root8Node97_cover : Covers root8Node97Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node97Domains0 root8Node97Domains1 f hf root8Node97Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node97Domains1 (.output 48)
    root8Node97Leaf_checked f h1
theorem root8Node96_cover : Covers root8Node96Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node96Domains0 root8Node96Domains1 f hf root8Node96Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node96Domains1 (.output 47)
    root8Node96Leaf_checked f h1
theorem root8Node95_cover : Covers root8Node95Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node95Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node95Domains0 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node96_cover
    · exact root8Node97_cover
  exact hb f hf
theorem root8Node94_cover : Covers root8Node94Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node94Domains0 root8Node94Domains1 f hf root8Node94Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node94Domains1 (.output 46)
    root8Node94Leaf_checked f h1
theorem root8Node93_cover : Covers root8Node93Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node93Domains0 root8Node93Domains1 f hf root8Node93Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node93Domains1 (.output 45)
    root8Node93Leaf_checked f h1
theorem root8Node92_cover : Covers root8Node92Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node92Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node92Domains0 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node93_cover
    · exact root8Node94_cover
  exact hb f hf
theorem root8Node91_cover : Covers root8Node91Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node91Domains0 root8Node91Domains1 f hf root8Node91Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root8Node91Domains1 root8Node91Domains2 f h1 root8Node91Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root8Node91Domains2 root8Node91Domains3 f h2 root8Node91Step3_checked
  have hb : Covers root8Node91Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node91Domains3 root8Outputs 12
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node92_cover
    · exact root8Node95_cover
  exact hb f h3
theorem root8Node90_cover : Covers root8Node90Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node90Domains0 root8Node90Domains1 f hf root8Node90Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node90Domains1 (.output 44)
    root8Node90Leaf_checked f h1
theorem root8Node89_cover : Covers root8Node89Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node89Domains0 root8Node89Domains1 f hf root8Node89Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node89Domains1 (.output 43)
    root8Node89Leaf_checked f h1
theorem root8Node88_cover : Covers root8Node88Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node88Domains0 root8Node88Domains1 f hf root8Node88Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root8Node88Domains1 root8Node88Domains2 f h1 root8Node88Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root8Node88Domains2 root8Node88Domains3 f h2 root8Node88Step3_checked
  have hb : Covers root8Node88Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node88Domains3 root8Outputs 62
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node89_cover
    · exact root8Node90_cover
  exact hb f h3
theorem root8Node87_cover : Covers root8Node87Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node87Domains0 root8Node87Domains1 f hf root8Node87Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node87Domains1 root8Node87Domains2 f h1 root8Node87Step2_checked
  have h3 := solution_checkReplacement constraints table27 table27_member
    root8Node87Domains2 root8Node87Domains3 f h2 root8Node87Step3_checked
  have hb : Covers root8Node87Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node87Domains3 root8Outputs 19
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node88_cover
    · exact root8Node91_cover
  exact hb f h3
theorem root8Node86_cover : Covers root8Node86Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root8Node86Domains0 root8Node86Domains1 f hf root8Node86Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root8Node86Domains1 root8Node86Domains2 f h1 root8Node86Step2_checked
  have hb : Covers root8Node86Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node86Domains2 root8Outputs 0
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node87_cover
    · exact root8Node98_cover
  exact hb f h2
theorem root8Node85_cover : Covers root8Node85Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node85Domains0 root8Node85Domains1 f hf root8Node85Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root8Node85Domains1 root8Node85Domains2 f h1 root8Node85Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node85Domains2 (.output 42)
    root8Node85Leaf_checked f h2
theorem root8Node84_cover : Covers root8Node84Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node84Domains0 root8Node84Domains1 f hf root8Node84Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node84Domains1 (.output 41)
    root8Node84Leaf_checked f h1
theorem root8Node83_cover : Covers root8Node83Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node83Domains0 (.output 40)
    root8Node83Leaf_checked f hf
theorem root8Node82_cover : Covers root8Node82Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node82Domains0 (.output 39)
    root8Node82Leaf_checked f hf
theorem root8Node81_cover : Covers root8Node81Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node81Domains0 root8Node81Domains1 f hf root8Node81Step1_checked
  have hb : Covers root8Node81Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node81Domains1 root8Outputs 86
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node82_cover
    · exact root8Node83_cover
  exact hb f h1
theorem root8Node80_cover : Covers root8Node80Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node80Domains0 root8Node80Domains1 f hf root8Node80Step1_checked
  have hb : Covers root8Node80Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node80Domains1 root8Outputs 70
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node81_cover
    · exact root8Node84_cover
  exact hb f h1
theorem root8Node79_cover : Covers root8Node79Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table27 table27_member
    root8Node79Domains0 root8Node79Domains1 f hf root8Node79Step1_checked
  have hb : Covers root8Node79Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node79Domains1 root8Outputs 20
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node80_cover
    · exact root8Node85_cover
  exact hb f h1
theorem root8Node78_cover : Covers root8Node78Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node78Domains0 root8Node78Domains1 f hf root8Node78Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node78Domains1 (.output 38)
    root8Node78Leaf_checked f h1
theorem root8Node77_cover : Covers root8Node77Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node77Domains0 (.output 37)
    root8Node77Leaf_checked f hf
theorem root8Node76_cover : Covers root8Node76Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node76Domains0 (.output 36)
    root8Node76Leaf_checked f hf
theorem root8Node75_cover : Covers root8Node75Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node75Domains0 root8Node75Domains1 f hf root8Node75Step1_checked
  have hb : Covers root8Node75Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node75Domains1 root8Outputs 86
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node76_cover
    · exact root8Node77_cover
  exact hb f h1
theorem root8Node74_cover : Covers root8Node74Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table27 table27_member
    root8Node74Domains0 root8Node74Domains1 f hf root8Node74Step1_checked
  have hb : Covers root8Node74Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node74Domains1 root8Outputs 70
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node75_cover
    · exact root8Node78_cover
  exact hb f h1
theorem root8Node73_cover : Covers root8Node73Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root8Node73Domains0 root8Node73Domains1 f hf root8Node73Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root8Node73Domains1 root8Node73Domains2 f h1 root8Node73Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root8Node73Domains2 root8Node73Domains3 f h2 root8Node73Step3_checked
  have h4 := solution_checkReplacement constraints table13 table13_member
    root8Node73Domains3 root8Node73Domains4 f h3 root8Node73Step4_checked
  have hb : Covers root8Node73Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node73Domains4 root8Outputs 5
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node74_cover
    · exact root8Node79_cover
  exact hb f h4
theorem root8Node72_cover : Covers root8Node72Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node72Domains0 root8Node72Domains1 f hf root8Node72Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root8Node72Domains1 root8Node72Domains2 f h1 root8Node72Step2_checked
  have hb : Covers root8Node72Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node72Domains2 root8Outputs 1
    intro s hs
    change s ∈ [(0,0),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node73_cover
    · exact root8Node86_cover
  exact hb f h2
theorem root8Node71_cover : Covers root8Node71Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node71Domains0 root8Node71Domains1 f hf root8Node71Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node71Domains1 (.output 35)
    root8Node71Leaf_checked f h1
theorem root8Node70_cover : Covers root8Node70Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node70Domains0 root8Node70Domains1 f hf root8Node70Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node70Domains1 (.output 34)
    root8Node70Leaf_checked f h1
theorem root8Node69_cover : Covers root8Node69Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root8Node69Domains0 root8Node69Domains1 f hf root8Node69Step1_checked
  have hb : Covers root8Node69Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node69Domains1 root8Outputs 62
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node70_cover
    · exact root8Node71_cover
  exact hb f h1
theorem root8Node68_cover : Covers root8Node68Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node68Domains0 root8Node68Domains1 f hf root8Node68Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node68Domains1 (.output 33)
    root8Node68Leaf_checked f h1
theorem root8Node67_cover : Covers root8Node67Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root8Node67Domains0 root8Node67Domains1 f hf root8Node67Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node67Domains1 (.output 32)
    root8Node67Leaf_checked f h1
theorem root8Node66_cover : Covers root8Node66Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root8Node66Domains0 root8Node66Domains1 f hf root8Node66Step1_checked
  have hb : Covers root8Node66Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node66Domains1 root8Outputs 62
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node67_cover
    · exact root8Node68_cover
  exact hb f h1
theorem root8Node65_cover : Covers root8Node65Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node65Domains0 root8Node65Domains1 f hf root8Node65Step1_checked
  have hb : Covers root8Node65Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node65Domains1 root8Outputs 20
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node66_cover
    · exact root8Node69_cover
  exact hb f h1
theorem root8Node64_cover : Covers root8Node64Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root8Node64Domains0 root8Node64Domains1 f hf root8Node64Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node64Domains1 (.output 31)
    root8Node64Leaf_checked f h1
theorem root8Node63_cover : Covers root8Node63Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root8Node63Domains0 root8Node63Domains1 f hf root8Node63Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node63Domains1 (.output 30)
    root8Node63Leaf_checked f h1
theorem root8Node62_cover : Covers root8Node62Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root8Node62Domains0 root8Node62Domains1 f hf root8Node62Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root8Node62Domains1 root8Node62Domains2 f h1 root8Node62Step2_checked
  have hb : Covers root8Node62Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node62Domains2 root8Outputs 20
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node63_cover
    · exact root8Node64_cover
  exact hb f h2
theorem root8Node61_cover : Covers root8Node61Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node61Domains0 root8Node61Domains1 f hf root8Node61Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root8Node61Domains1 root8Node61Domains2 f h1 root8Node61Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root8Node61Domains2 root8Node61Domains3 f h2 root8Node61Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root8Node61Domains3 root8Node61Domains4 f h3 root8Node61Step4_checked
  have hb : Covers root8Node61Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node61Domains4 root8Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node62_cover
    · exact root8Node65_cover
  exact hb f h4
theorem root8Node60_cover : Covers root8Node60Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root8Node60Domains0 root8Node60Domains1 f hf root8Node60Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node60Domains1 root8Node60Domains2 f h1 root8Node60Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root8Node60Domains2 root8Node60Domains3 f h2 root8Node60Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root8Node60Domains3 root8Node60Domains4 f h3 root8Node60Step4_checked
  have hb : Covers root8Node60Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node60Domains4 root8Outputs 3
    intro s hs
    change s ∈ [(1,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node61_cover
    · exact root8Node72_cover
  exact hb f h4
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
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node57Domains0 root8Node57Domains1 f hf root8Node57Step1_checked
  have hb : Covers root8Node57Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node57Domains1 root8Outputs 50
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
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
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node54Domains0 root8Node54Domains1 f hf root8Node54Step1_checked
  have hb : Covers root8Node54Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node54Domains1 root8Outputs 50
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node55_cover
    · exact root8Node56_cover
  exact hb f h1
theorem root8Node53_cover : Covers root8Node53Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root8Node53Domains0 root8Node53Domains1 f hf root8Node53Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root8Node53Domains1 root8Node53Domains2 f h1 root8Node53Step2_checked
  have hb : Covers root8Node53Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node53Domains2 root8Outputs 31
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node54_cover
    · exact root8Node57_cover
  exact hb f h2
theorem root8Node52_cover : Covers root8Node52Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root8Node52Domains0 root8Node52Domains1 f hf root8Node52Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root8Node52Domains1 root8Node52Domains2 f h1 root8Node52Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root8Node52Domains2 root8Node52Domains3 f h2 root8Node52Step3_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node52Domains3 (.output 25)
    root8Node52Leaf_checked f h3
theorem root8Node51_cover : Covers root8Node51Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node51Domains0 root8Node51Domains1 f hf root8Node51Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node51Domains1 (.output 24)
    root8Node51Leaf_checked f h1
theorem root8Node50_cover : Covers root8Node50Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node50Domains0 root8Node50Domains1 f hf root8Node50Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node50Domains1 (.output 23)
    root8Node50Leaf_checked f h1
theorem root8Node49_cover : Covers root8Node49Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node49Domains0 root8Node49Domains1 f hf root8Node49Step1_checked
  have hb : Covers root8Node49Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node49Domains1 root8Outputs 76
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node50_cover
    · exact root8Node51_cover
  exact hb f h1
theorem root8Node48_cover : Covers root8Node48Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node48Domains0 root8Node48Domains1 f hf root8Node48Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root8Node48Domains1 root8Node48Domains2 f h1 root8Node48Step2_checked
  have hb : Covers root8Node48Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node48Domains2 root8Outputs 31
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node49_cover
    · exact root8Node52_cover
  exact hb f h2
theorem root8Node47_cover : Covers root8Node47Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node47Domains0 root8Node47Domains1 f hf root8Node47Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node47Domains1 (.output 22)
    root8Node47Leaf_checked f h1
theorem root8Node46_cover : Covers root8Node46Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node46Domains0 root8Node46Domains1 f hf root8Node46Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node46Domains1 (.output 21)
    root8Node46Leaf_checked f h1
theorem root8Node45_cover : Covers root8Node45Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node45Domains0 root8Node45Domains1 f hf root8Node45Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root8Node45Domains1 root8Node45Domains2 f h1 root8Node45Step2_checked
  have hb : Covers root8Node45Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node45Domains2 root8Outputs 39
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node46_cover
    · exact root8Node47_cover
  exact hb f h2
theorem root8Node44_cover : Covers root8Node44Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root8Node44Domains0 root8Node44Domains1 f hf root8Node44Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node44Domains1 (.output 20)
    root8Node44Leaf_checked f h1
theorem root8Node43_cover : Covers root8Node43Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root8Node43Domains0 root8Node43Domains1 f hf root8Node43Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node43Domains1 (.output 19)
    root8Node43Leaf_checked f h1
theorem root8Node42_cover : Covers root8Node42Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node42Domains0 root8Node42Domains1 f hf root8Node42Step1_checked
  have hb : Covers root8Node42Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node42Domains1 root8Outputs 86
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node43_cover
    · exact root8Node44_cover
  exact hb f h1
theorem root8Node41_cover : Covers root8Node41Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node41Domains0 root8Node41Domains1 f hf root8Node41Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node41Domains1 root8Node41Domains2 f h1 root8Node41Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node41Domains2 (.output 18)
    root8Node41Leaf_checked f h2
theorem root8Node40_cover : Covers root8Node40Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node40Domains0 root8Node40Domains1 f hf root8Node40Step1_checked
  have hb : Covers root8Node40Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node40Domains1 root8Outputs 39
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node41_cover
    · exact root8Node42_cover
  exact hb f h1
theorem root8Node39_cover : Covers root8Node39Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node39Domains0 root8Node39Domains1 f hf root8Node39Step1_checked
  have hb : Covers root8Node39Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node39Domains1 root8Outputs 31
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node40_cover
    · exact root8Node45_cover
  exact hb f h1
theorem root8Node38_cover : Covers root8Node38Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root8Node38Domains0 root8Node38Domains1 f hf root8Node38Step1_checked
  have hb : Covers root8Node38Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node38Domains1 root8Outputs 28
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node39_cover
    · exact root8Node48_cover
  exact hb f h1
theorem root8Node37_cover : Covers root8Node37Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root8Node37Domains0 root8Node37Domains1 f hf root8Node37Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root8Node37Domains1 root8Node37Domains2 f h1 root8Node37Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root8Node37Domains2 root8Node37Domains3 f h2 root8Node37Step3_checked
  have h4 := solution_checkReplacement constraints table51 table51_member
    root8Node37Domains3 root8Node37Domains4 f h3 root8Node37Step4_checked
  have hb : Covers root8Node37Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node37Domains4 root8Outputs 3
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node38_cover
    · exact root8Node53_cover
  exact hb f h4
theorem root8Node36_cover : Covers root8Node36Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node36Domains0 root8Node36Domains1 f hf root8Node36Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node36Domains1 (.output 17)
    root8Node36Leaf_checked f h1
theorem root8Node35_cover : Covers root8Node35Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node35Domains0 (.output 16)
    root8Node35Leaf_checked f hf
theorem root8Node34_cover : Covers root8Node34Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node34Domains0 (.output 15)
    root8Node34Leaf_checked f hf
theorem root8Node33_cover : Covers root8Node33Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node33Domains0 root8Node33Domains1 f hf root8Node33Step1_checked
  have hb : Covers root8Node33Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node33Domains1 root8Outputs 86
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node34_cover
    · exact root8Node35_cover
  exact hb f h1
theorem root8Node32_cover : Covers root8Node32Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node32Domains0 root8Node32Domains1 f hf root8Node32Step1_checked
  have hb : Covers root8Node32Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node32Domains1 root8Outputs 70
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node33_cover
    · exact root8Node36_cover
  exact hb f h1
theorem root8Node31_cover : Covers root8Node31Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node31Domains0 root8Node31Domains1 f hf root8Node31Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root8Node31Domains1 root8Node31Domains2 f h1 root8Node31Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root8Node31Domains2 root8Node31Domains3 f h2 root8Node31Step3_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node31Domains3 (.output 14)
    root8Node31Leaf_checked f h3
theorem root8Node30_cover : Covers root8Node30Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root8Node30Domains0 root8Node30Domains1 f hf root8Node30Step1_checked
  have hb : Covers root8Node30Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node30Domains1 root8Outputs 28
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node31_cover
    · exact root8Node32_cover
  exact hb f h1
theorem root8Node29_cover : Covers root8Node29Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node29Domains0 root8Node29Domains1 f hf root8Node29Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node29Domains1 (.output 13)
    root8Node29Leaf_checked f h1
theorem root8Node28_cover : Covers root8Node28Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node28Domains0 (.output 12)
    root8Node28Leaf_checked f hf
theorem root8Node27_cover : Covers root8Node27Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node27Domains0 (.output 11)
    root8Node27Leaf_checked f hf
theorem root8Node26_cover : Covers root8Node26Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node26Domains0 root8Node26Domains1 f hf root8Node26Step1_checked
  have hb : Covers root8Node26Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node26Domains1 root8Outputs 86
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node27_cover
    · exact root8Node28_cover
  exact hb f h1
theorem root8Node25_cover : Covers root8Node25Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node25Domains0 root8Node25Domains1 f hf root8Node25Step1_checked
  have hb : Covers root8Node25Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node25Domains1 root8Outputs 70
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node26_cover
    · exact root8Node29_cover
  exact hb f h1
theorem root8Node24_cover : Covers root8Node24Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node24Domains0 root8Node24Domains1 f hf root8Node24Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root8Node24Domains1 root8Node24Domains2 f h1 root8Node24Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root8Node24Domains2 root8Node24Domains3 f h2 root8Node24Step3_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node24Domains3 (.output 10)
    root8Node24Leaf_checked f h3
theorem root8Node23_cover : Covers root8Node23Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root8Node23Domains0 root8Node23Domains1 f hf root8Node23Step1_checked
  have hb : Covers root8Node23Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node23Domains1 root8Outputs 28
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node24_cover
    · exact root8Node25_cover
  exact hb f h1
theorem root8Node22_cover : Covers root8Node22Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root8Node22Domains0 root8Node22Domains1 f hf root8Node22Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root8Node22Domains1 root8Node22Domains2 f h1 root8Node22Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root8Node22Domains2 root8Node22Domains3 f h2 root8Node22Step3_checked
  have hb : Covers root8Node22Domains3 constraints root8Outputs := by
    apply covers_of_branches root8Node22Domains3 root8Outputs 21
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node23_cover
    · exact root8Node30_cover
  exact hb f h3
theorem root8Node21_cover : Covers root8Node21Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node21Domains0 root8Node21Domains1 f hf root8Node21Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root8Node21Domains1 root8Node21Domains2 f h1 root8Node21Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node21Domains2 (.output 9)
    root8Node21Leaf_checked f h2
theorem root8Node20_cover : Covers root8Node20Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node20Domains0 root8Node20Domains1 f hf root8Node20Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node20Domains1 (.output 8)
    root8Node20Leaf_checked f h1
theorem root8Node19_cover : Covers root8Node19Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node19Domains0 root8Node19Domains1 f hf root8Node19Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node19Domains1 (.output 7)
    root8Node19Leaf_checked f h1
theorem root8Node18_cover : Covers root8Node18Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root8Node18Domains0 root8Node18Domains1 f hf root8Node18Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root8Node18Domains1 root8Node18Domains2 f h1 root8Node18Step2_checked
  have hb : Covers root8Node18Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node18Domains2 root8Outputs 39
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node19_cover
    · exact root8Node20_cover
  exact hb f h2
theorem root8Node17_cover : Covers root8Node17Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table43 table43_member
    root8Node17Domains0 root8Node17Domains1 f hf root8Node17Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node17Domains1 root8Node17Domains2 f h1 root8Node17Step2_checked
  have hb : Covers root8Node17Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node17Domains2 root8Outputs 28
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node18_cover
    · exact root8Node21_cover
  exact hb f h2
theorem root8Node16_cover : Covers root8Node16Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root8Node16Domains0 root8Node16Domains1 f hf root8Node16Step1_checked
  have hb : Covers root8Node16Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node16Domains1 root8Outputs 6
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node17_cover
    · exact root8Node22_cover
  exact hb f h1
theorem root8Node15_cover : Covers root8Node15Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root8Node15Domains0 root8Node15Domains1 f hf root8Node15Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node15Domains1 (.output 6)
    root8Node15Leaf_checked f h1
theorem root8Node14_cover : Covers root8Node14Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root8Node14Domains0 root8Node14Domains1 f hf root8Node14Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node14Domains1 (.output 5)
    root8Node14Leaf_checked f h1
theorem root8Node13_cover : Covers root8Node13Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table43 table43_member
    root8Node13Domains0 root8Node13Domains1 f hf root8Node13Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node13Domains1 root8Node13Domains2 f h1 root8Node13Step2_checked
  have hb : Covers root8Node13Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node13Domains2 root8Outputs 21
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node14_cover
    · exact root8Node15_cover
  exact hb f h2
theorem root8Node12_cover : Covers root8Node12Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table43 table43_member
    root8Node12Domains0 root8Node12Domains1 f hf root8Node12Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node12Domains1 root8Node12Domains2 f h1 root8Node12Step2_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node12Domains2 (.output 4)
    root8Node12Leaf_checked f h2
theorem root8Node11_cover : Covers root8Node11Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root8Node11Domains0 root8Node11Domains1 f hf root8Node11Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root8Node11Domains1 root8Node11Domains2 f h1 root8Node11Step2_checked
  have hb : Covers root8Node11Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node11Domains2 root8Outputs 6
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node12_cover
    · exact root8Node13_cover
  exact hb f h2
theorem root8Node10_cover : Covers root8Node10Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root8Node10Domains0 root8Node10Domains1 f hf root8Node10Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root8Node10Domains1 root8Node10Domains2 f h1 root8Node10Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root8Node10Domains2 root8Node10Domains3 f h2 root8Node10Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root8Node10Domains3 root8Node10Domains4 f h3 root8Node10Step4_checked
  have hb : Covers root8Node10Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node10Domains4 root8Outputs 3
    intro s hs
    change s ∈ [(4,0),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node11_cover
    · exact root8Node16_cover
  exact hb f h4
theorem root8Node9_cover : Covers root8Node9Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root8Node9Domains0 root8Node9Domains1 f hf root8Node9Step1_checked
  have hb : Covers root8Node9Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node9Domains1 root8Outputs 1
    intro s hs
    change s ∈ [(0,0),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node10_cover
    · exact root8Node37_cover
  exact hb f h1
theorem root8Node8_cover : Covers root8Node8Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node8Domains0 root8Node8Domains1 f hf root8Node8Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node8Domains1 (.output 3)
    root8Node8Leaf_checked f h1
theorem root8Node7_cover : Covers root8Node7Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root8Node7Domains0 root8Node7Domains1 f hf root8Node7Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node7Domains1 (.output 2)
    root8Node7Leaf_checked f h1
theorem root8Node6_cover : Covers root8Node6Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root8Node6Domains0 root8Node6Domains1 f hf root8Node6Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root8Node6Domains1 root8Node6Domains2 f h1 root8Node6Step2_checked
  have hb : Covers root8Node6Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node6Domains2 root8Outputs 31
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node7_cover
    · exact root8Node8_cover
  exact hb f h2
theorem root8Node5_cover : Covers root8Node5Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root8Node5Domains0 root8Node5Domains1 f hf root8Node5Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node5Domains1 (.output 1)
    root8Node5Leaf_checked f h1
theorem root8Node4_cover : Covers root8Node4Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root8Node4Domains0 root8Node4Domains1 f hf root8Node4Step1_checked
  exact checkCover_sound 1 constraints root8Outputs root8Node4Domains1 (.output 0)
    root8Node4Leaf_checked f h1
theorem root8Node3_cover : Covers root8Node3Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root8Node3Domains0 root8Node3Domains1 f hf root8Node3Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root8Node3Domains1 root8Node3Domains2 f h1 root8Node3Step2_checked
  have hb : Covers root8Node3Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node3Domains2 root8Outputs 2
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node4_cover
    · exact root8Node5_cover
  exact hb f h2
theorem root8Node2_cover : Covers root8Node2Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root8Node2Domains0 root8Node2Domains1 f hf root8Node2Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root8Node2Domains1 root8Node2Domains2 f h1 root8Node2Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root8Node2Domains2 root8Node2Domains3 f h2 root8Node2Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root8Node2Domains3 root8Node2Domains4 f h3 root8Node2Step4_checked
  have hb : Covers root8Node2Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node2Domains4 root8Outputs 1
    intro s hs
    change s ∈ [(0,0),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node3_cover
    · exact root8Node6_cover
  exact hb f h4
theorem root8Node1_cover : Covers root8Node1Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root8Node1Domains0 root8Node1Domains1 f hf root8Node1Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root8Node1Domains1 root8Node1Domains2 f h1 root8Node1Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root8Node1Domains2 root8Node1Domains3 f h2 root8Node1Step3_checked
  have h4 := solution_checkReplacement constraints table19 table19_member
    root8Node1Domains3 root8Node1Domains4 f h3 root8Node1Step4_checked
  have hb : Covers root8Node1Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node1Domains4 root8Outputs 0
    intro s hs
    change s ∈ [(4,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node2_cover
    · exact root8Node9_cover
  exact hb f h4
theorem root8Node0_cover : Covers root8Node0Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root8Node0Domains0 root8Node0Domains1 f hf root8Node0Step1_checked
  have h2 := solution_checkReplacement constraints table33 table33_member
    root8Node0Domains1 root8Node0Domains2 f h1 root8Node0Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root8Node0Domains2 root8Node0Domains3 f h2 root8Node0Step3_checked
  have h4 := solution_checkReplacement constraints table51 table51_member
    root8Node0Domains3 root8Node0Domains4 f h3 root8Node0Step4_checked
  have hb : Covers root8Node0Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node0Domains4 root8Outputs 35
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node1_cover
    · exact root8Node60_cover
  exact hb f h4
theorem root8_table_cover : Covers (domains (8,0)) constraints root8Outputs := root8Node0_cover
theorem root8Family_count : root8Family.length = 70 := rfl
#print axioms root8_table_cover
end SpectreFinite.HexSearch.RadiusFive
