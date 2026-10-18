module

public import SpectreFinite.RadiusFourRoot7Part52

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node158_cover : Covers root7Node158Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node158Domains0 root7Node158Domains1 f hf root7Node158Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root7Node158Domains1 root7Node158Domains2 f h1 root7Node158Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node158Domains2 (.output 79)
    root7Node158Leaf_checked f h2
theorem root7Node157_cover : Covers root7Node157Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node157Domains0 (.output 78)
    root7Node157Leaf_checked f hf
theorem root7Node156_cover : Covers root7Node156Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node156Domains0 (.output 77)
    root7Node156Leaf_checked f hf
theorem root7Node155_cover : Covers root7Node155Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node155Domains0 root7Node155Domains1 f hf root7Node155Step1_checked
  have hb : Covers root7Node155Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node155Domains1 root7Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node156_cover
    · exact root7Node157_cover
  exact hb f h1
theorem root7Node154_cover : Covers root7Node154Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root7Node154Domains0 root7Node154Domains1 f hf root7Node154Step1_checked
  have hb : Covers root7Node154Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node154Domains1 root7Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node155_cover
    · exact root7Node158_cover
  exact hb f h1
theorem root7Node153_cover : Covers root7Node153Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root7Node153Domains0 root7Node153Domains1 f hf root7Node153Step1_checked
  have h2 := solution_checkReplacement constraints table35 table35_member
    root7Node153Domains1 root7Node153Domains2 f h1 root7Node153Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root7Node153Domains2 root7Node153Domains3 f h2 root7Node153Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node153Domains3 (.output 76)
    root7Node153Leaf_checked f h3
theorem root7Node152_cover : Covers root7Node152Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node152Domains0 root7Node152Domains1 f hf root7Node152Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root7Node152Domains1 root7Node152Domains2 f h1 root7Node152Step2_checked
  have h3 := solution_checkReplacement constraints table11 table11_member
    root7Node152Domains2 root7Node152Domains3 f h2 root7Node152Step3_checked
  have hb : Covers root7Node152Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node152Domains3 root7Outputs 5
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node153_cover
    · exact root7Node154_cover
  exact hb f h3
theorem root7Node151_cover : Covers root7Node151Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node151Domains0 root7Node151Domains1 f hf root7Node151Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node151Domains1 (.output 75)
    root7Node151Leaf_checked f h1
theorem root7Node150_cover : Covers root7Node150Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node150Domains0 root7Node150Domains1 f hf root7Node150Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node150Domains1 (.output 74)
    root7Node150Leaf_checked f h1
theorem root7Node149_cover : Covers root7Node149Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node149Domains0 root7Node149Domains1 f hf root7Node149Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node149Domains1 root7Node149Domains2 f h1 root7Node149Step2_checked
  have hb : Covers root7Node149Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node149Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node150_cover
    · exact root7Node151_cover
  exact hb f h2
theorem root7Node148_cover : Covers root7Node148Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node148Domains0 root7Node148Domains1 f hf root7Node148Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node148Domains1 root7Node148Domains2 f h1 root7Node148Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node148Domains2 (.output 73)
    root7Node148Leaf_checked f h2
theorem root7Node147_cover : Covers root7Node147Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node147Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node147Domains0 root7Outputs 34
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node148_cover
    · exact root7Node149_cover
  exact hb f hf
theorem root7Node146_cover : Covers root7Node146Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node146Domains0 root7Node146Domains1 f hf root7Node146Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node146Domains1 (.output 72)
    root7Node146Leaf_checked f h1
theorem root7Node145_cover : Covers root7Node145Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node145Domains0 root7Node145Domains1 f hf root7Node145Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node145Domains1 (.output 71)
    root7Node145Leaf_checked f h1
theorem root7Node144_cover : Covers root7Node144Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node144Domains0 root7Node144Domains1 f hf root7Node144Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node144Domains1 root7Node144Domains2 f h1 root7Node144Step2_checked
  have hb : Covers root7Node144Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node144Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node145_cover
    · exact root7Node146_cover
  exact hb f h2
theorem root7Node143_cover : Covers root7Node143Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node143Domains0 root7Node143Domains1 f hf root7Node143Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node143Domains1 root7Node143Domains2 f h1 root7Node143Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node143Domains2 (.output 70)
    root7Node143Leaf_checked f h2
theorem root7Node142_cover : Covers root7Node142Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node142Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node142Domains0 root7Outputs 34
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node143_cover
    · exact root7Node144_cover
  exact hb f hf
theorem root7Node141_cover : Covers root7Node141Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node141Domains0 root7Node141Domains1 f hf root7Node141Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node141Domains1 root7Node141Domains2 f h1 root7Node141Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root7Node141Domains2 root7Node141Domains3 f h2 root7Node141Step3_checked
  have hb : Covers root7Node141Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node141Domains3 root7Outputs 26
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node142_cover
    · exact root7Node147_cover
  exact hb f h3
theorem root7Node140_cover : Covers root7Node140Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node140Domains0 root7Node140Domains1 f hf root7Node140Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node140Domains1 root7Node140Domains2 f h1 root7Node140Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root7Node140Domains2 root7Node140Domains3 f h2 root7Node140Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node140Domains3 (.output 69)
    root7Node140Leaf_checked f h3
theorem root7Node139_cover : Covers root7Node139Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node139Domains0 root7Node139Domains1 f hf root7Node139Step1_checked
  have hb : Covers root7Node139Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node139Domains1 root7Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node140_cover
    · exact root7Node141_cover
  exact hb f h1
theorem root7Node138_cover : Covers root7Node138Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node138Domains0 root7Node138Domains1 f hf root7Node138Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node138Domains1 root7Node138Domains2 f h1 root7Node138Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root7Node138Domains2 root7Node138Domains3 f h2 root7Node138Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node138Domains3 (.output 68)
    root7Node138Leaf_checked f h3
theorem root7Node137_cover : Covers root7Node137Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root7Node137Domains0 root7Node137Domains1 f hf root7Node137Step1_checked
  have h2 := solution_checkReplacement constraints table29 table29_member
    root7Node137Domains1 root7Node137Domains2 f h1 root7Node137Step2_checked
  have h3 := solution_checkReplacement constraints table39 table39_member
    root7Node137Domains2 root7Node137Domains3 f h2 root7Node137Step3_checked
  have h4 := solution_checkReplacement constraints table35 table35_member
    root7Node137Domains3 root7Node137Domains4 f h3 root7Node137Step4_checked
  have hb : Covers root7Node137Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node137Domains4 root7Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node138_cover
    · exact root7Node139_cover
  exact hb f h4
theorem root7Node136_cover : Covers root7Node136Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table20 table20_member
    root7Node136Domains0 root7Node136Domains1 f hf root7Node136Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root7Node136Domains1 root7Node136Domains2 f h1 root7Node136Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root7Node136Domains2 root7Node136Domains3 f h2 root7Node136Step3_checked
  have hb : Covers root7Node136Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node136Domains3 root7Outputs 3
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node137_cover
    · exact root7Node152_cover
  exact hb f h3
theorem root7Node135_cover : Covers root7Node135Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node135Domains0 (.output 67)
    root7Node135Leaf_checked f hf
theorem root7Node134_cover : Covers root7Node134Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node134Domains0 (.output 66)
    root7Node134Leaf_checked f hf
theorem root7Node133_cover : Covers root7Node133Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node133Domains0 root7Node133Domains1 f hf root7Node133Step1_checked
  have hb : Covers root7Node133Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node133Domains1 root7Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node134_cover
    · exact root7Node135_cover
  exact hb f h1
theorem root7Node132_cover : Covers root7Node132Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node132Domains0 (.output 65)
    root7Node132Leaf_checked f hf
theorem root7Node131_cover : Covers root7Node131Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node131Domains0 (.output 64)
    root7Node131Leaf_checked f hf
theorem root7Node130_cover : Covers root7Node130Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node130Domains0 root7Node130Domains1 f hf root7Node130Step1_checked
  have hb : Covers root7Node130Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node130Domains1 root7Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node131_cover
    · exact root7Node132_cover
  exact hb f h1
theorem root7Node129_cover : Covers root7Node129Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node129Domains0 root7Node129Domains1 f hf root7Node129Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node129Domains1 root7Node129Domains2 f h1 root7Node129Step2_checked
  have hb : Covers root7Node129Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node129Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node130_cover
    · exact root7Node133_cover
  exact hb f h2
theorem root7Node128_cover : Covers root7Node128Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node128Domains0 root7Node128Domains1 f hf root7Node128Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node128Domains1 (.output 63)
    root7Node128Leaf_checked f h1
theorem root7Node127_cover : Covers root7Node127Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node127Domains0 (.output 62)
    root7Node127Leaf_checked f hf
theorem root7Node126_cover : Covers root7Node126Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node126Domains0 (.output 61)
    root7Node126Leaf_checked f hf
theorem root7Node125_cover : Covers root7Node125Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node125Domains0 root7Node125Domains1 f hf root7Node125Step1_checked
  have hb : Covers root7Node125Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node125Domains1 root7Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node126_cover
    · exact root7Node127_cover
  exact hb f h1
theorem root7Node124_cover : Covers root7Node124Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node124Domains0 root7Node124Domains1 f hf root7Node124Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node124Domains1 root7Node124Domains2 f h1 root7Node124Step2_checked
  have hb : Covers root7Node124Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node124Domains2 root7Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node125_cover
    · exact root7Node128_cover
  exact hb f h2
theorem root7Node123_cover : Covers root7Node123Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node123Domains0 root7Node123Domains1 f hf root7Node123Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node123Domains1 root7Node123Domains2 f h1 root7Node123Step2_checked
  have hb : Covers root7Node123Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node123Domains2 root7Outputs 34
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node124_cover
    · exact root7Node129_cover
  exact hb f h2
theorem root7Node122_cover : Covers root7Node122Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node122Domains0 root7Node122Domains1 f hf root7Node122Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node122Domains1 root7Node122Domains2 f h1 root7Node122Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node122Domains2 (.output 60)
    root7Node122Leaf_checked f h2
theorem root7Node121_cover : Covers root7Node121Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node121Domains0 root7Node121Domains1 f hf root7Node121Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node121Domains1 root7Node121Domains2 f h1 root7Node121Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node121Domains2 (.output 59)
    root7Node121Leaf_checked f h2
theorem root7Node120_cover : Covers root7Node120Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node120Domains0 root7Node120Domains1 f hf root7Node120Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node120Domains1 root7Node120Domains2 f h1 root7Node120Step2_checked
  have hb : Covers root7Node120Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node120Domains2 root7Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node121_cover
    · exact root7Node122_cover
  exact hb f h2
theorem root7Node119_cover : Covers root7Node119Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node119Domains0 root7Node119Domains1 f hf root7Node119Step1_checked
  have hb : Covers root7Node119Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node119Domains1 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node120_cover
    · exact root7Node123_cover
  exact hb f h1
theorem root7Node118_cover : Covers root7Node118Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node118Domains0 root7Node118Domains1 f hf root7Node118Step1_checked
  have h2 := solution_checkReplacement constraints table35 table35_member
    root7Node118Domains1 root7Node118Domains2 f h1 root7Node118Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root7Node118Domains2 root7Node118Domains3 f h2 root7Node118Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node118Domains3 (.output 58)
    root7Node118Leaf_checked f h3
theorem root7Node117_cover : Covers root7Node117Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node117Domains0 root7Node117Domains1 f hf root7Node117Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node117Domains1 root7Node117Domains2 f h1 root7Node117Step2_checked
  have hb : Covers root7Node117Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node117Domains2 root7Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node118_cover
    · exact root7Node119_cover
  exact hb f h2
theorem root7Node116_cover : Covers root7Node116Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node116Domains0 root7Node116Domains1 f hf root7Node116Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node116Domains1 (.output 57)
    root7Node116Leaf_checked f h1
theorem root7Node115_cover : Covers root7Node115Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node115Domains0 root7Node115Domains1 f hf root7Node115Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node115Domains1 (.output 56)
    root7Node115Leaf_checked f h1
theorem root7Node114_cover : Covers root7Node114Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node114Domains0 root7Node114Domains1 f hf root7Node114Step1_checked
  have hb : Covers root7Node114Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node114Domains1 root7Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node115_cover
    · exact root7Node116_cover
  exact hb f h1
theorem root7Node113_cover : Covers root7Node113Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node113Domains0 root7Node113Domains1 f hf root7Node113Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node113Domains1 (.output 55)
    root7Node113Leaf_checked f h1
theorem root7Node112_cover : Covers root7Node112Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node112Domains0 root7Node112Domains1 f hf root7Node112Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node112Domains1 (.output 54)
    root7Node112Leaf_checked f h1
theorem root7Node111_cover : Covers root7Node111Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node111Domains0 root7Node111Domains1 f hf root7Node111Step1_checked
  have hb : Covers root7Node111Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node111Domains1 root7Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node112_cover
    · exact root7Node113_cover
  exact hb f h1
theorem root7Node110_cover : Covers root7Node110Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node110Domains0 root7Node110Domains1 f hf root7Node110Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node110Domains1 root7Node110Domains2 f h1 root7Node110Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root7Node110Domains2 root7Node110Domains3 f h2 root7Node110Step3_checked
  have hb : Covers root7Node110Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node110Domains3 root7Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node111_cover
    · exact root7Node114_cover
  exact hb f h3
theorem root7Node109_cover : Covers root7Node109Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node109Domains0 root7Node109Domains1 f hf root7Node109Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node109Domains1 (.output 53)
    root7Node109Leaf_checked f h1
theorem root7Node108_cover : Covers root7Node108Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node108Domains0 root7Node108Domains1 f hf root7Node108Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node108Domains1 (.output 52)
    root7Node108Leaf_checked f h1
theorem root7Node107_cover : Covers root7Node107Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node107Domains0 root7Node107Domains1 f hf root7Node107Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node107Domains1 root7Node107Domains2 f h1 root7Node107Step2_checked
  have hb : Covers root7Node107Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node107Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node108_cover
    · exact root7Node109_cover
  exact hb f h2
theorem root7Node106_cover : Covers root7Node106Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node106Domains0 root7Node106Domains1 f hf root7Node106Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node106Domains1 root7Node106Domains2 f h1 root7Node106Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node106Domains2 (.output 51)
    root7Node106Leaf_checked f h2
theorem root7Node105_cover : Covers root7Node105Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node105Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node105Domains0 root7Outputs 34
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node106_cover
    · exact root7Node107_cover
  exact hb f hf
theorem root7Node104_cover : Covers root7Node104Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node104Domains0 root7Node104Domains1 f hf root7Node104Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node104Domains1 (.output 50)
    root7Node104Leaf_checked f h1
theorem root7Node103_cover : Covers root7Node103Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node103Domains0 root7Node103Domains1 f hf root7Node103Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node103Domains1 (.output 49)
    root7Node103Leaf_checked f h1
theorem root7Node102_cover : Covers root7Node102Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node102Domains0 root7Node102Domains1 f hf root7Node102Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node102Domains1 root7Node102Domains2 f h1 root7Node102Step2_checked
  have hb : Covers root7Node102Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node102Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node103_cover
    · exact root7Node104_cover
  exact hb f h2
theorem root7Node101_cover : Covers root7Node101Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node101Domains0 root7Node101Domains1 f hf root7Node101Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node101Domains1 root7Node101Domains2 f h1 root7Node101Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node101Domains2 (.output 48)
    root7Node101Leaf_checked f h2
theorem root7Node100_cover : Covers root7Node100Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node100Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node100Domains0 root7Outputs 34
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node101_cover
    · exact root7Node102_cover
  exact hb f hf
theorem root7Node99_cover : Covers root7Node99Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node99Domains0 root7Node99Domains1 f hf root7Node99Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node99Domains1 root7Node99Domains2 f h1 root7Node99Step2_checked
  have h3 := solution_checkReplacement constraints table5 table5_member
    root7Node99Domains2 root7Node99Domains3 f h2 root7Node99Step3_checked
  have hb : Covers root7Node99Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node99Domains3 root7Outputs 26
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node100_cover
    · exact root7Node105_cover
  exact hb f h3
theorem root7Node98_cover : Covers root7Node98Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node98Domains0 root7Node98Domains1 f hf root7Node98Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node98Domains1 root7Node98Domains2 f h1 root7Node98Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root7Node98Domains2 root7Node98Domains3 f h2 root7Node98Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node98Domains3 (.output 47)
    root7Node98Leaf_checked f h3
theorem root7Node97_cover : Covers root7Node97Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node97Domains0 root7Node97Domains1 f hf root7Node97Step1_checked
  have hb : Covers root7Node97Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node97Domains1 root7Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node98_cover
    · exact root7Node99_cover
  exact hb f h1
theorem root7Node96_cover : Covers root7Node96Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node96Domains0 root7Node96Domains1 f hf root7Node96Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root7Node96Domains1 root7Node96Domains2 f h1 root7Node96Step2_checked
  have h3 := solution_checkReplacement constraints table10 table10_member
    root7Node96Domains2 root7Node96Domains3 f h2 root7Node96Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node96Domains3 (.output 46)
    root7Node96Leaf_checked f h3
theorem root7Node95_cover : Covers root7Node95Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root7Node95Domains0 root7Node95Domains1 f hf root7Node95Step1_checked
  have h2 := solution_checkReplacement constraints table35 table35_member
    root7Node95Domains1 root7Node95Domains2 f h1 root7Node95Step2_checked
  have hb : Covers root7Node95Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node95Domains2 root7Outputs 16
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node96_cover
    · exact root7Node97_cover
  exact hb f h2
theorem root7Node94_cover : Covers root7Node94Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root7Node94Domains0 root7Node94Domains1 f hf root7Node94Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root7Node94Domains1 root7Node94Domains2 f h1 root7Node94Step2_checked
  have hb : Covers root7Node94Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node94Domains2 root7Outputs 5
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node95_cover
    · exact root7Node110_cover
  exact hb f h2
theorem root7Node93_cover : Covers root7Node93Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table22 table22_member
    root7Node93Domains0 root7Node93Domains1 f hf root7Node93Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node93Domains1 root7Node93Domains2 f h1 root7Node93Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root7Node93Domains2 root7Node93Domains3 f h2 root7Node93Step3_checked
  have hb : Covers root7Node93Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node93Domains3 root7Outputs 0
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node94_cover
    · exact root7Node117_cover
  exact hb f h3
theorem root7Node92_cover : Covers root7Node92Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node92Domains0 root7Node92Domains1 f hf root7Node92Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node92Domains1 root7Node92Domains2 f h1 root7Node92Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root7Node92Domains2 root7Node92Domains3 f h2 root7Node92Step3_checked
  have h4 := solution_checkReplacement constraints table39 table39_member
    root7Node92Domains3 root7Node92Domains4 f h3 root7Node92Step4_checked
  have hb : Covers root7Node92Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node92Domains4 root7Outputs 2
    intro s hs
    change s ∈ [(5,1),(5,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node93_cover
    · exact root7Node136_cover
  exact hb f h4
theorem root7Node91_cover : Covers root7Node91Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node91Domains0 root7Node91Domains1 f hf root7Node91Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node91Domains1 root7Node91Domains2 f h1 root7Node91Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node91Domains2 (.output 45)
    root7Node91Leaf_checked f h2
theorem root7Node90_cover : Covers root7Node90Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node90Domains0 root7Node90Domains1 f hf root7Node90Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node90Domains1 (.output 44)
    root7Node90Leaf_checked f h1
theorem root7Node89_cover : Covers root7Node89Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node89Domains0 root7Node89Domains1 f hf root7Node89Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node89Domains1 (.output 43)
    root7Node89Leaf_checked f h1
theorem root7Node88_cover : Covers root7Node88Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node88Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node88Domains0 root7Outputs 50
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node89_cover
    · exact root7Node90_cover
  exact hb f hf
theorem root7Node87_cover : Covers root7Node87Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node87Domains0 root7Node87Domains1 f hf root7Node87Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node87Domains1 root7Node87Domains2 f h1 root7Node87Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node87Domains2 (.output 42)
    root7Node87Leaf_checked f h2
theorem root7Node86_cover : Covers root7Node86Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node86Domains0 root7Node86Domains1 f hf root7Node86Step1_checked
  have hb : Covers root7Node86Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node86Domains1 root7Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node87_cover
    · exact root7Node88_cover
  exact hb f h1
theorem root7Node85_cover : Covers root7Node85Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node85Domains0 root7Node85Domains1 f hf root7Node85Step1_checked
  have hb : Covers root7Node85Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node85Domains1 root7Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node86_cover
    · exact root7Node91_cover
  exact hb f h1
theorem root7Node84_cover : Covers root7Node84Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node84Domains0 root7Node84Domains1 f hf root7Node84Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node84Domains1 (.output 41)
    root7Node84Leaf_checked f h1
theorem root7Node83_cover : Covers root7Node83Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node83Domains0 root7Node83Domains1 f hf root7Node83Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node83Domains1 (.output 40)
    root7Node83Leaf_checked f h1
theorem root7Node82_cover : Covers root7Node82Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node82Domains0 root7Node82Domains1 f hf root7Node82Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root7Node82Domains1 root7Node82Domains2 f h1 root7Node82Step2_checked
  have hb : Covers root7Node82Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node82Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node83_cover
    · exact root7Node84_cover
  exact hb f h2
theorem root7Node81_cover : Covers root7Node81Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node81Domains0 root7Node81Domains1 f hf root7Node81Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node81Domains1 root7Node81Domains2 f h1 root7Node81Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root7Node81Domains2 root7Node81Domains3 f h2 root7Node81Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root7Node81Domains3 root7Node81Domains4 f h3 root7Node81Step4_checked
  have hb : Covers root7Node81Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node81Domains4 root7Outputs 17
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node82_cover
    · exact root7Node85_cover
  exact hb f h4
theorem root7Node80_cover : Covers root7Node80Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node80Domains0 root7Node80Domains1 f hf root7Node80Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node80Domains1 root7Node80Domains2 f h1 root7Node80Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root7Node80Domains2 root7Node80Domains3 f h2 root7Node80Step3_checked
  have hb : Covers root7Node80Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node80Domains3 root7Outputs 13
    intro s hs
    change s ∈ [(2,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node81_cover
    · exact root7Node92_cover
  exact hb f h3
theorem root7Node79_cover : Covers root7Node79Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node79Domains0 root7Node79Domains1 f hf root7Node79Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node79Domains1 root7Node79Domains2 f h1 root7Node79Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node79Domains2 (.output 39)
    root7Node79Leaf_checked f h2
theorem root7Node78_cover : Covers root7Node78Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node78Domains0 root7Node78Domains1 f hf root7Node78Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node78Domains1 (.output 38)
    root7Node78Leaf_checked f h1
theorem root7Node77_cover : Covers root7Node77Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node77Domains0 root7Node77Domains1 f hf root7Node77Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node77Domains1 (.output 37)
    root7Node77Leaf_checked f h1
theorem root7Node76_cover : Covers root7Node76Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node76Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node76Domains0 root7Outputs 50
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node77_cover
    · exact root7Node78_cover
  exact hb f hf
theorem root7Node75_cover : Covers root7Node75Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node75Domains0 root7Node75Domains1 f hf root7Node75Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node75Domains1 root7Node75Domains2 f h1 root7Node75Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node75Domains2 (.output 36)
    root7Node75Leaf_checked f h2
theorem root7Node74_cover : Covers root7Node74Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node74Domains0 root7Node74Domains1 f hf root7Node74Step1_checked
  have hb : Covers root7Node74Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node74Domains1 root7Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node75_cover
    · exact root7Node76_cover
  exact hb f h1
theorem root7Node73_cover : Covers root7Node73Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node73Domains0 root7Node73Domains1 f hf root7Node73Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node73Domains1 root7Node73Domains2 f h1 root7Node73Step2_checked
  have hb : Covers root7Node73Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node73Domains2 root7Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node74_cover
    · exact root7Node79_cover
  exact hb f h2
theorem root7Node72_cover : Covers root7Node72Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node72Domains0 root7Node72Domains1 f hf root7Node72Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node72Domains1 root7Node72Domains2 f h1 root7Node72Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node72Domains2 (.output 35)
    root7Node72Leaf_checked f h2
theorem root7Node71_cover : Covers root7Node71Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root7Node71Domains0 root7Node71Domains1 f hf root7Node71Step1_checked
  have hb : Covers root7Node71Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node71Domains1 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node72_cover
    · exact root7Node73_cover
  exact hb f h1
theorem root7Node70_cover : Covers root7Node70Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node70Domains0 root7Node70Domains1 f hf root7Node70Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node70Domains1 root7Node70Domains2 f h1 root7Node70Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node70Domains2 (.output 34)
    root7Node70Leaf_checked f h2
theorem root7Node69_cover : Covers root7Node69Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node69Domains0 root7Node69Domains1 f hf root7Node69Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node69Domains1 (.output 33)
    root7Node69Leaf_checked f h1
theorem root7Node68_cover : Covers root7Node68Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node68Domains0 root7Node68Domains1 f hf root7Node68Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node68Domains1 (.output 32)
    root7Node68Leaf_checked f h1
theorem root7Node67_cover : Covers root7Node67Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node67Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node67Domains0 root7Outputs 50
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node68_cover
    · exact root7Node69_cover
  exact hb f hf
theorem root7Node66_cover : Covers root7Node66Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node66Domains0 root7Node66Domains1 f hf root7Node66Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node66Domains1 root7Node66Domains2 f h1 root7Node66Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node66Domains2 (.output 31)
    root7Node66Leaf_checked f h2
theorem root7Node65_cover : Covers root7Node65Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node65Domains0 root7Node65Domains1 f hf root7Node65Step1_checked
  have hb : Covers root7Node65Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node65Domains1 root7Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node66_cover
    · exact root7Node67_cover
  exact hb f h1
theorem root7Node64_cover : Covers root7Node64Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node64Domains0 root7Node64Domains1 f hf root7Node64Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node64Domains1 root7Node64Domains2 f h1 root7Node64Step2_checked
  have hb : Covers root7Node64Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node64Domains2 root7Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node65_cover
    · exact root7Node70_cover
  exact hb f h2
theorem root7Node63_cover : Covers root7Node63Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node63Domains0 root7Node63Domains1 f hf root7Node63Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node63Domains1 root7Node63Domains2 f h1 root7Node63Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node63Domains2 (.output 30)
    root7Node63Leaf_checked f h2
theorem root7Node62_cover : Covers root7Node62Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root7Node62Domains0 root7Node62Domains1 f hf root7Node62Step1_checked
  have hb : Covers root7Node62Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node62Domains1 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node63_cover
    · exact root7Node64_cover
  exact hb f h1
theorem root7Node61_cover : Covers root7Node61Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root7Node61Domains0 root7Node61Domains1 f hf root7Node61Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root7Node61Domains1 root7Node61Domains2 f h1 root7Node61Step2_checked
  have h3 := solution_checkReplacement constraints table16 table16_member
    root7Node61Domains2 root7Node61Domains3 f h2 root7Node61Step3_checked
  have hb : Covers root7Node61Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node61Domains3 root7Outputs 0
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node62_cover
    · exact root7Node71_cover
  exact hb f h3
theorem root7Node60_cover : Covers root7Node60Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node60Domains0 root7Node60Domains1 f hf root7Node60Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node60Domains1 (.output 29)
    root7Node60Leaf_checked f h1
theorem root7Node59_cover : Covers root7Node59Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node59Domains0 root7Node59Domains1 f hf root7Node59Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node59Domains1 (.output 28)
    root7Node59Leaf_checked f h1
theorem root7Node58_cover : Covers root7Node58Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node58Domains0 root7Node58Domains1 f hf root7Node58Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node58Domains1 root7Node58Domains2 f h1 root7Node58Step2_checked
  have hb : Covers root7Node58Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node58Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node59_cover
    · exact root7Node60_cover
  exact hb f h2
theorem root7Node57_cover : Covers root7Node57Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node57Domains0 root7Node57Domains1 f hf root7Node57Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node57Domains1 (.output 27)
    root7Node57Leaf_checked f h1
theorem root7Node56_cover : Covers root7Node56Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node56Domains0 root7Node56Domains1 f hf root7Node56Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node56Domains1 (.output 26)
    root7Node56Leaf_checked f h1
theorem root7Node55_cover : Covers root7Node55Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node55Domains0 root7Node55Domains1 f hf root7Node55Step1_checked
  have h2 := solution_checkReplacement constraints table10 table10_member
    root7Node55Domains1 root7Node55Domains2 f h1 root7Node55Step2_checked
  have h3 := solution_checkReplacement constraints table26 table26_member
    root7Node55Domains2 root7Node55Domains3 f h2 root7Node55Step3_checked
  have hb : Covers root7Node55Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node55Domains3 root7Outputs 49
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node56_cover
    · exact root7Node57_cover
  exact hb f h3
theorem root7Node54_cover : Covers root7Node54Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root7Node54Domains0 root7Node54Domains1 f hf root7Node54Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node54Domains1 (.output 25)
    root7Node54Leaf_checked f h1
theorem root7Node53_cover : Covers root7Node53Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table16 table16_member
    root7Node53Domains0 root7Node53Domains1 f hf root7Node53Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node53Domains1 (.output 24)
    root7Node53Leaf_checked f h1
theorem root7Node52_cover : Covers root7Node52Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node52Domains0 root7Node52Domains1 f hf root7Node52Step1_checked
  have hb : Covers root7Node52Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node52Domains1 root7Outputs 34
    intro s hs
    change s ∈ [(2,3),(4,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node53_cover
    · exact root7Node54_cover
  exact hb f h1
theorem root7Node51_cover : Covers root7Node51Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table40 table40_member
    root7Node51Domains0 root7Node51Domains1 f hf root7Node51Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node51Domains1 (.output 23)
    root7Node51Leaf_checked f h1
theorem root7Node50_cover : Covers root7Node50Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node50Domains0 root7Node50Domains1 f hf root7Node50Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node50Domains1 root7Node50Domains2 f h1 root7Node50Step2_checked
  have hb : Covers root7Node50Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node50Domains2 root7Outputs 33
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node51_cover
    · exact root7Node52_cover
  exact hb f h2
theorem root7Node49_cover : Covers root7Node49Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node49Domains0 root7Node49Domains1 f hf root7Node49Step1_checked
  have hb : Covers root7Node49Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node49Domains1 root7Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node50_cover
    · exact root7Node55_cover
  exact hb f h1
theorem root7Node48_cover : Covers root7Node48Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node48Domains0 root7Node48Domains1 f hf root7Node48Step1_checked
  have hb : Covers root7Node48Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node48Domains1 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node49_cover
    · exact root7Node58_cover
  exact hb f h1
theorem root7Node47_cover : Covers root7Node47Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node47Domains0 root7Node47Domains1 f hf root7Node47Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node47Domains1 (.output 22)
    root7Node47Leaf_checked f h1
theorem root7Node46_cover : Covers root7Node46Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node46Domains0 root7Node46Domains1 f hf root7Node46Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node46Domains1 (.output 21)
    root7Node46Leaf_checked f h1
theorem root7Node45_cover : Covers root7Node45Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node45Domains0 root7Node45Domains1 f hf root7Node45Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node45Domains1 root7Node45Domains2 f h1 root7Node45Step2_checked
  have h3 := solution_checkReplacement constraints table35 table35_member
    root7Node45Domains2 root7Node45Domains3 f h2 root7Node45Step3_checked
  have hb : Covers root7Node45Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node45Domains3 root7Outputs 49
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node46_cover
    · exact root7Node47_cover
  exact hb f h3
theorem root7Node44_cover : Covers root7Node44Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root7Node44Domains0 root7Node44Domains1 f hf root7Node44Step1_checked
  have hb : Covers root7Node44Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node44Domains1 root7Outputs 11
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node45_cover
    · exact root7Node48_cover
  exact hb f h1
theorem root7Node43_cover : Covers root7Node43Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node43Domains0 root7Node43Domains1 f hf root7Node43Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node43Domains1 (.output 20)
    root7Node43Leaf_checked f h1
theorem root7Node42_cover : Covers root7Node42Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node42Domains0 root7Node42Domains1 f hf root7Node42Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node42Domains1 (.output 19)
    root7Node42Leaf_checked f h1
theorem root7Node41_cover : Covers root7Node41Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node41Domains0 root7Node41Domains1 f hf root7Node41Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node41Domains1 root7Node41Domains2 f h1 root7Node41Step2_checked
  have hb : Covers root7Node41Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node41Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node42_cover
    · exact root7Node43_cover
  exact hb f h2
theorem root7Node40_cover : Covers root7Node40Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node40Domains0 root7Node40Domains1 f hf root7Node40Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node40Domains1 root7Node40Domains2 f h1 root7Node40Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node40Domains2 (.output 18)
    root7Node40Leaf_checked f h2
theorem root7Node39_cover : Covers root7Node39Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node39Domains0 root7Node39Domains1 f hf root7Node39Step1_checked
  have hb : Covers root7Node39Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node39Domains1 root7Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node40_cover
    · exact root7Node41_cover
  exact hb f h1
theorem root7Node38_cover : Covers root7Node38Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node38Domains0 root7Node38Domains1 f hf root7Node38Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node38Domains1 (.output 17)
    root7Node38Leaf_checked f h1
theorem root7Node37_cover : Covers root7Node37Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table39 table39_member
    root7Node37Domains0 root7Node37Domains1 f hf root7Node37Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node37Domains1 (.output 16)
    root7Node37Leaf_checked f h1
theorem root7Node36_cover : Covers root7Node36Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node36Domains0 root7Node36Domains1 f hf root7Node36Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root7Node36Domains1 root7Node36Domains2 f h1 root7Node36Step2_checked
  have h3 := solution_checkReplacement constraints table35 table35_member
    root7Node36Domains2 root7Node36Domains3 f h2 root7Node36Step3_checked
  have hb : Covers root7Node36Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node36Domains3 root7Outputs 49
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node37_cover
    · exact root7Node38_cover
  exact hb f h3
theorem root7Node35_cover : Covers root7Node35Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node35Domains0 root7Node35Domains1 f hf root7Node35Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node35Domains1 root7Node35Domains2 f h1 root7Node35Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root7Node35Domains2 root7Node35Domains3 f h2 root7Node35Step3_checked
  have h4 := solution_checkReplacement constraints table26 table26_member
    root7Node35Domains3 root7Node35Domains4 f h3 root7Node35Step4_checked
  have hb : Covers root7Node35Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node35Domains4 root7Outputs 11
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node36_cover
    · exact root7Node39_cover
  exact hb f h4
theorem root7Node34_cover : Covers root7Node34Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node34Domains0 root7Node34Domains1 f hf root7Node34Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root7Node34Domains1 root7Node34Domains2 f h1 root7Node34Step2_checked
  have h3 := solution_checkReplacement constraints table31 table31_member
    root7Node34Domains2 root7Node34Domains3 f h2 root7Node34Step3_checked
  have hb : Covers root7Node34Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node34Domains3 root7Outputs 3
    intro s hs
    change s ∈ [(1,5),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node35_cover
    · exact root7Node44_cover
  exact hb f h3
theorem root7Node33_cover : Covers root7Node33Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node33Domains0 root7Node33Domains1 f hf root7Node33Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root7Node33Domains1 root7Node33Domains2 f h1 root7Node33Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node33Domains2 (.output 15)
    root7Node33Leaf_checked f h2
theorem root7Node32_cover : Covers root7Node32Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node32Domains0 (.output 14)
    root7Node32Leaf_checked f hf
theorem root7Node31_cover : Covers root7Node31Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node31Domains0 (.output 13)
    root7Node31Leaf_checked f hf
theorem root7Node30_cover : Covers root7Node30Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node30Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node30Domains0 root7Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node31_cover
    · exact root7Node32_cover
  exact hb f hf
theorem root7Node29_cover : Covers root7Node29Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node29Domains0 (.output 12)
    root7Node29Leaf_checked f hf
theorem root7Node28_cover : Covers root7Node28Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node28Domains0 (.output 11)
    root7Node28Leaf_checked f hf
theorem root7Node27_cover : Covers root7Node27Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node27Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node27Domains0 root7Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node28_cover
    · exact root7Node29_cover
  exact hb f hf
theorem root7Node26_cover : Covers root7Node26Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node26Domains0 root7Node26Domains1 f hf root7Node26Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root7Node26Domains1 root7Node26Domains2 f h1 root7Node26Step2_checked
  have hb : Covers root7Node26Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node26Domains2 root7Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node27_cover
    · exact root7Node30_cover
  exact hb f h2
theorem root7Node25_cover : Covers root7Node25Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node25Domains0 root7Node25Domains1 f hf root7Node25Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node25Domains1 root7Node25Domains2 f h1 root7Node25Step2_checked
  have hb : Covers root7Node25Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node25Domains2 root7Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node26_cover
    · exact root7Node33_cover
  exact hb f h2
theorem root7Node24_cover : Covers root7Node24Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node24Domains0 root7Node24Domains1 f hf root7Node24Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node24Domains1 root7Node24Domains2 f h1 root7Node24Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node24Domains2 (.output 10)
    root7Node24Leaf_checked f h2
theorem root7Node23_cover : Covers root7Node23Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node23Domains0 root7Node23Domains1 f hf root7Node23Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node23Domains1 root7Node23Domains2 f h1 root7Node23Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node23Domains2 (.output 9)
    root7Node23Leaf_checked f h2
theorem root7Node22_cover : Covers root7Node22Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node22Domains0 root7Node22Domains1 f hf root7Node22Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node22Domains1 root7Node22Domains2 f h1 root7Node22Step2_checked
  have hb : Covers root7Node22Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node22Domains2 root7Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node23_cover
    · exact root7Node24_cover
  exact hb f h2
theorem root7Node21_cover : Covers root7Node21Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node21Domains0 root7Node21Domains1 f hf root7Node21Step1_checked
  have hb : Covers root7Node21Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node21Domains1 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node22_cover
    · exact root7Node25_cover
  exact hb f h1
theorem root7Node20_cover : Covers root7Node20Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node20Domains0 root7Node20Domains1 f hf root7Node20Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node20Domains1 root7Node20Domains2 f h1 root7Node20Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node20Domains2 (.output 8)
    root7Node20Leaf_checked f h2
theorem root7Node19_cover : Covers root7Node19Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root7Node19Domains0 root7Node19Domains1 f hf root7Node19Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node19Domains1 root7Node19Domains2 f h1 root7Node19Step2_checked
  have hb : Covers root7Node19Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node19Domains2 root7Outputs 11
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node20_cover
    · exact root7Node21_cover
  exact hb f h2
theorem root7Node18_cover : Covers root7Node18Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root7Node18Domains0 root7Node18Domains1 f hf root7Node18Step1_checked
  have hb : Covers root7Node18Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node18Domains1 root7Outputs 2
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node19_cover
    · exact root7Node34_cover
  exact hb f h1
theorem root7Node17_cover : Covers root7Node17Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node17Domains0 root7Node17Domains1 f hf root7Node17Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root7Node17Domains1 root7Node17Domains2 f h1 root7Node17Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node17Domains2 (.output 7)
    root7Node17Leaf_checked f h2
theorem root7Node16_cover : Covers root7Node16Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node16Domains0 (.output 6)
    root7Node16Leaf_checked f hf
theorem root7Node15_cover : Covers root7Node15Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node15Domains0 (.output 5)
    root7Node15Leaf_checked f hf
theorem root7Node14_cover : Covers root7Node14Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node14Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node14Domains0 root7Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node15_cover
    · exact root7Node16_cover
  exact hb f hf
theorem root7Node13_cover : Covers root7Node13Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node13Domains0 (.output 4)
    root7Node13Leaf_checked f hf
theorem root7Node12_cover : Covers root7Node12Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node12Domains0 (.output 3)
    root7Node12Leaf_checked f hf
theorem root7Node11_cover : Covers root7Node11Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node11Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node11Domains0 root7Outputs 56
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node12_cover
    · exact root7Node13_cover
  exact hb f hf
theorem root7Node10_cover : Covers root7Node10Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table38 table38_member
    root7Node10Domains0 root7Node10Domains1 f hf root7Node10Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root7Node10Domains1 root7Node10Domains2 f h1 root7Node10Step2_checked
  have hb : Covers root7Node10Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node10Domains2 root7Outputs 42
    intro s hs
    change s ∈ [(5,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node11_cover
    · exact root7Node14_cover
  exact hb f h2
theorem root7Node9_cover : Covers root7Node9Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table29 table29_member
    root7Node9Domains0 root7Node9Domains1 f hf root7Node9Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node9Domains1 root7Node9Domains2 f h1 root7Node9Step2_checked
  have hb : Covers root7Node9Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node9Domains2 root7Outputs 35
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node10_cover
    · exact root7Node17_cover
  exact hb f h2
theorem root7Node8_cover : Covers root7Node8Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node8Domains0 root7Node8Domains1 f hf root7Node8Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node8Domains1 root7Node8Domains2 f h1 root7Node8Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node8Domains2 (.output 2)
    root7Node8Leaf_checked f h2
theorem root7Node7_cover : Covers root7Node7Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node7Domains0 root7Node7Domains1 f hf root7Node7Step1_checked
  have h2 := solution_checkReplacement constraints table16 table16_member
    root7Node7Domains1 root7Node7Domains2 f h1 root7Node7Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node7Domains2 (.output 1)
    root7Node7Leaf_checked f h2
theorem root7Node6_cover : Covers root7Node6Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node6Domains0 root7Node6Domains1 f hf root7Node6Step1_checked
  have h2 := solution_checkReplacement constraints table39 table39_member
    root7Node6Domains1 root7Node6Domains2 f h1 root7Node6Step2_checked
  have hb : Covers root7Node6Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node6Domains2 root7Outputs 29
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node7_cover
    · exact root7Node8_cover
  exact hb f h2
theorem root7Node5_cover : Covers root7Node5Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node5Domains0 root7Node5Domains1 f hf root7Node5Step1_checked
  have hb : Covers root7Node5Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node5Domains1 root7Outputs 26
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node6_cover
    · exact root7Node9_cover
  exact hb f h1
theorem root7Node4_cover : Covers root7Node4Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table37 table37_member
    root7Node4Domains0 root7Node4Domains1 f hf root7Node4Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node4Domains1 root7Node4Domains2 f h1 root7Node4Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node4Domains2 (.output 0)
    root7Node4Leaf_checked f h2
theorem root7Node3_cover : Covers root7Node3Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root7Node3Domains0 root7Node3Domains1 f hf root7Node3Step1_checked
  have h2 := solution_checkReplacement constraints table40 table40_member
    root7Node3Domains1 root7Node3Domains2 f h1 root7Node3Step2_checked
  have hb : Covers root7Node3Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node3Domains2 root7Outputs 11
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node4_cover
    · exact root7Node5_cover
  exact hb f h2
theorem root7Node2_cover : Covers root7Node2Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root7Node2Domains0 root7Node2Domains1 f hf root7Node2Step1_checked
  have h2 := solution_checkReplacement constraints table38 table38_member
    root7Node2Domains1 root7Node2Domains2 f h1 root7Node2Step2_checked
  have h3 := solution_checkReplacement constraints table39 table39_member
    root7Node2Domains2 root7Node2Domains3 f h2 root7Node2Step3_checked
  have hb : Covers root7Node2Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node2Domains3 root7Outputs 0
    intro s hs
    change s ∈ [(4,1),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node3_cover
    · exact root7Node18_cover
  exact hb f h3
theorem root7Node1_cover : Covers root7Node1Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root7Node1Domains0 root7Node1Domains1 f hf root7Node1Step1_checked
  have h2 := solution_checkReplacement constraints table20 table20_member
    root7Node1Domains1 root7Node1Domains2 f h1 root7Node1Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root7Node1Domains2 root7Node1Domains3 f h2 root7Node1Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root7Node1Domains3 root7Node1Domains4 f h3 root7Node1Step4_checked
  have hb : Covers root7Node1Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node1Domains4 root7Outputs 5
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node2_cover
    · exact root7Node61_cover
  exact hb f h4
theorem root7Node0_cover : Covers root7Node0Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root7Node0Domains0 root7Node0Domains1 f hf root7Node0Step1_checked
  have h2 := solution_checkReplacement constraints table37 table37_member
    root7Node0Domains1 root7Node0Domains2 f h1 root7Node0Step2_checked
  have h3 := solution_checkReplacement constraints table23 table23_member
    root7Node0Domains2 root7Node0Domains3 f h2 root7Node0Step3_checked
  have h4 := solution_checkReplacement constraints table39 table39_member
    root7Node0Domains3 root7Node0Domains4 f h3 root7Node0Step4_checked
  have h5 := solution_checkReplacement constraints table0 table0_member
    root7Node0Domains4 root7Node0Domains5 f h4 root7Node0Step5_checked
  have hb : Covers root7Node0Domains5 constraints root7Outputs := by
    apply covers_of_branches root7Node0Domains5 root7Outputs 14
    intro s hs
    change s ∈ [(0,0),(1,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node1_cover
    · exact root7Node80_cover
  exact hb f h5
theorem root7_table_cover : Covers (domains (7,0)) constraints root7Outputs := root7Node0_cover
theorem root7Family_count : root7Family.length = 80 := rfl
#print axioms root7_table_cover
end SpectreFinite.HexSearch.RadiusFour
