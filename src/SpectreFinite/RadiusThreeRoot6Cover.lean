module

public import SpectreFinite.RadiusThreeRoot6Part23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root6Node44_cover : Covers root6Node44Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node44Domains0 root6Node44Domains1 f hf root6Node44Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node44Domains1 (.output 22)
    root6Node44Leaf_checked f h1
theorem root6Node43_cover : Covers root6Node43Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node43Domains0 root6Node43Domains1 f hf root6Node43Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node43Domains1 (.output 21)
    root6Node43Leaf_checked f h1
theorem root6Node42_cover : Covers root6Node42Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node42Domains0 root6Node42Domains1 f hf root6Node42Step1_checked
  have hb : Covers root6Node42Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node42Domains1 root6Outputs 22
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node43_cover
    · exact root6Node44_cover
  exact hb f h1
theorem root6Node41_cover : Covers root6Node41Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node41Domains0 root6Node41Domains1 f hf root6Node41Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node41Domains1 (.output 20)
    root6Node41Leaf_checked f h1
theorem root6Node40_cover : Covers root6Node40Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node40Domains0 root6Node40Domains1 f hf root6Node40Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node40Domains1 (.output 19)
    root6Node40Leaf_checked f h1
theorem root6Node39_cover : Covers root6Node39Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node39Domains0 root6Node39Domains1 f hf root6Node39Step1_checked
  have hb : Covers root6Node39Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node39Domains1 root6Outputs 22
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node40_cover
    · exact root6Node41_cover
  exact hb f h1
theorem root6Node38_cover : Covers root6Node38Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root6Node38Domains0 root6Node38Domains1 f hf root6Node38Step1_checked
  have h2 := solution_checkReplacement constraints table26 table26_member
    root6Node38Domains1 root6Node38Domains2 f h1 root6Node38Step2_checked
  have hb : Covers root6Node38Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node38Domains2 root6Outputs 3
    intro s hs
    change s ∈ [(0,0),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node39_cover
    · exact root6Node42_cover
  exact hb f h2
theorem root6Node37_cover : Covers root6Node37Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node37Domains0 root6Node37Domains1 f hf root6Node37Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node37Domains1 (.output 18)
    root6Node37Leaf_checked f h1
theorem root6Node36_cover : Covers root6Node36Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node36Domains0 root6Node36Domains1 f hf root6Node36Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node36Domains1 (.output 17)
    root6Node36Leaf_checked f h1
theorem root6Node35_cover : Covers root6Node35Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root6Node35Domains0 root6Node35Domains1 f hf root6Node35Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root6Node35Domains1 root6Node35Domains2 f h1 root6Node35Step2_checked
  have hb : Covers root6Node35Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node35Domains2 root6Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node36_cover
    · exact root6Node37_cover
  exact hb f h2
theorem root6Node34_cover : Covers root6Node34Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root6Node34Domains0 root6Node34Domains1 f hf root6Node34Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root6Node34Domains1 root6Node34Domains2 f h1 root6Node34Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node34Domains2 (.output 16)
    root6Node34Leaf_checked f h2
theorem root6Node33_cover : Covers root6Node33Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root6Node33Domains0 root6Node33Domains1 f hf root6Node33Step1_checked
  have hb : Covers root6Node33Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node33Domains1 root6Outputs 8
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node34_cover
    · exact root6Node35_cover
  exact hb f h1
theorem root6Node32_cover : Covers root6Node32Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node32Domains0 root6Node32Domains1 f hf root6Node32Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root6Node32Domains1 root6Node32Domains2 f h1 root6Node32Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node32Domains2 (.output 15)
    root6Node32Leaf_checked f h2
theorem root6Node31_cover : Covers root6Node31Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root6Node31Domains0 root6Node31Domains1 f hf root6Node31Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node31Domains1 root6Node31Domains2 f h1 root6Node31Step2_checked
  have h3 := solution_checkReplacement constraints table17 table17_member
    root6Node31Domains2 root6Node31Domains3 f h2 root6Node31Step3_checked
  have h4 := solution_checkReplacement constraints table23 table23_member
    root6Node31Domains3 root6Node31Domains4 f h3 root6Node31Step4_checked
  have hb : Covers root6Node31Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node31Domains4 root6Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node32_cover
    · exact root6Node33_cover
  exact hb f h4
theorem root6Node30_cover : Covers root6Node30Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table17 table17_member
    root6Node30Domains0 root6Node30Domains1 f hf root6Node30Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root6Node30Domains1 root6Node30Domains2 f h1 root6Node30Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root6Node30Domains2 root6Node30Domains3 f h2 root6Node30Step3_checked
  have hb : Covers root6Node30Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node30Domains3 root6Outputs 0
    intro s hs
    change s ∈ [(1,5),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node31_cover
    · exact root6Node38_cover
  exact hb f h3
theorem root6Node29_cover : Covers root6Node29Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node29Domains0 root6Node29Domains1 f hf root6Node29Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node29Domains1 (.output 14)
    root6Node29Leaf_checked f h1
theorem root6Node28_cover : Covers root6Node28Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node28Domains0 root6Node28Domains1 f hf root6Node28Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node28Domains1 (.output 13)
    root6Node28Leaf_checked f h1
theorem root6Node27_cover : Covers root6Node27Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node27Domains0 root6Node27Domains1 f hf root6Node27Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root6Node27Domains1 root6Node27Domains2 f h1 root6Node27Step2_checked
  have hb : Covers root6Node27Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node27Domains2 root6Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node28_cover
    · exact root6Node29_cover
  exact hb f h2
theorem root6Node26_cover : Covers root6Node26Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
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
  have h1 := solution_checkReplacement constraints table30 table30_member
    root6Node23Domains0 root6Node23Domains1 f hf root6Node23Step1_checked
  have hb : Covers root6Node23Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node23Domains1 root6Outputs 35
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node24_cover
    · exact root6Node25_cover
  exact hb f h1
theorem root6Node22_cover : Covers root6Node22Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node22Domains0 root6Node22Domains1 f hf root6Node22Step1_checked
  have hb : Covers root6Node22Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node22Domains1 root6Outputs 23
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node23_cover
    · exact root6Node26_cover
  exact hb f h1
theorem root6Node21_cover : Covers root6Node21Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root6Node21Domains0 root6Node21Domains1 f hf root6Node21Step1_checked
  have h2 := solution_checkReplacement constraints table23 table23_member
    root6Node21Domains1 root6Node21Domains2 f h1 root6Node21Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node21Domains2 (.output 9)
    root6Node21Leaf_checked f h2
theorem root6Node20_cover : Covers root6Node20Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node20Domains0 root6Node20Domains1 f hf root6Node20Step1_checked
  have hb : Covers root6Node20Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node20Domains1 root6Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node21_cover
    · exact root6Node22_cover
  exact hb f h1
theorem root6Node19_cover : Covers root6Node19Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root6Node19Domains0 root6Node19Domains1 f hf root6Node19Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root6Node19Domains1 root6Node19Domains2 f h1 root6Node19Step2_checked
  have h3 := solution_checkReplacement constraints table25 table25_member
    root6Node19Domains2 root6Node19Domains3 f h2 root6Node19Step3_checked
  have hb : Covers root6Node19Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node19Domains3 root6Outputs 9
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node20_cover
    · exact root6Node27_cover
  exact hb f h3
theorem root6Node18_cover : Covers root6Node18Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node18Domains0 root6Node18Domains1 f hf root6Node18Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node18Domains1 (.output 8)
    root6Node18Leaf_checked f h1
theorem root6Node17_cover : Covers root6Node17Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node17Domains0 root6Node17Domains1 f hf root6Node17Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node17Domains1 (.output 7)
    root6Node17Leaf_checked f h1
theorem root6Node16_cover : Covers root6Node16Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node16Domains0 root6Node16Domains1 f hf root6Node16Step1_checked
  have hb : Covers root6Node16Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node16Domains1 root6Outputs 22
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node17_cover
    · exact root6Node18_cover
  exact hb f h1
theorem root6Node15_cover : Covers root6Node15Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node15Domains0 root6Node15Domains1 f hf root6Node15Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node15Domains1 (.output 6)
    root6Node15Leaf_checked f h1
theorem root6Node14_cover : Covers root6Node14Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table19 table19_member
    root6Node14Domains0 root6Node14Domains1 f hf root6Node14Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root6Node14Domains1 root6Node14Domains2 f h1 root6Node14Step2_checked
  have hb : Covers root6Node14Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node14Domains2 root6Outputs 9
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node15_cover
    · exact root6Node16_cover
  exact hb f h2
theorem root6Node13_cover : Covers root6Node13Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root6Node13Domains0 root6Node13Domains1 f hf root6Node13Step1_checked
  have hb : Covers root6Node13Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node13Domains1 root6Outputs 8
    intro s hs
    change s ∈ [(3,0),(7,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node14_cover
    · exact root6Node19_cover
  exact hb f h1
theorem root6Node12_cover : Covers root6Node12Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node12Domains0 root6Node12Domains1 f hf root6Node12Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node12Domains1 (.output 5)
    root6Node12Leaf_checked f h1
theorem root6Node11_cover : Covers root6Node11Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node11Domains0 root6Node11Domains1 f hf root6Node11Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node11Domains1 (.output 4)
    root6Node11Leaf_checked f h1
theorem root6Node10_cover : Covers root6Node10Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node10Domains0 root6Node10Domains1 f hf root6Node10Step1_checked
  have hb : Covers root6Node10Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node10Domains1 root6Outputs 22
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node11_cover
    · exact root6Node12_cover
  exact hb f h1
theorem root6Node9_cover : Covers root6Node9Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table23 table23_member
    root6Node9Domains0 root6Node9Domains1 f hf root6Node9Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node9Domains1 (.output 3)
    root6Node9Leaf_checked f h1
theorem root6Node8_cover : Covers root6Node8Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node8Domains0 root6Node8Domains1 f hf root6Node8Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root6Node8Domains1 root6Node8Domains2 f h1 root6Node8Step2_checked
  have hb : Covers root6Node8Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node8Domains2 root6Outputs 9
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node9_cover
    · exact root6Node10_cover
  exact hb f h2
theorem root6Node7_cover : Covers root6Node7Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root6Node7Domains0 root6Node7Domains1 f hf root6Node7Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node7Domains1 root6Node7Domains2 f h1 root6Node7Step2_checked
  have h3 := solution_checkReplacement constraints table4 table4_member
    root6Node7Domains2 root6Node7Domains3 f h2 root6Node7Step3_checked
  have hb : Covers root6Node7Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node7Domains3 root6Outputs 2
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node8_cover
    · exact root6Node13_cover
  exact hb f h3
theorem root6Node6_cover : Covers root6Node6Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root6Node6Domains0 root6Node6Domains1 f hf root6Node6Step1_checked
  have h2 := solution_checkReplacement constraints table24 table24_member
    root6Node6Domains1 root6Node6Domains2 f h1 root6Node6Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root6Node6Domains2 root6Node6Domains3 f h2 root6Node6Step3_checked
  have hb : Covers root6Node6Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node6Domains3 root6Outputs 4
    intro s hs
    change s ∈ [(5,2),(5,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node7_cover
    · exact root6Node30_cover
  exact hb f h3
theorem root6Node5_cover : Covers root6Node5Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node5Domains0 root6Node5Domains1 f hf root6Node5Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node5Domains1 (.output 2)
    root6Node5Leaf_checked f h1
theorem root6Node4_cover : Covers root6Node4Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node4Domains0 root6Node4Domains1 f hf root6Node4Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node4Domains1 (.output 1)
    root6Node4Leaf_checked f h1
theorem root6Node3_cover : Covers root6Node3Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node3Domains0 root6Node3Domains1 f hf root6Node3Step1_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node3Domains1 (.output 0)
    root6Node3Leaf_checked f h1
theorem root6Node2_cover : Covers root6Node2Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node2Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node2Domains0 root6Outputs 14
    intro s hs
    change s ∈ [(1,4),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node3_cover
    · exact root6Node4_cover
  exact hb f hf
theorem root6Node1_cover : Covers root6Node1Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table24 table24_member
    root6Node1Domains0 root6Node1Domains1 f hf root6Node1Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root6Node1Domains1 root6Node1Domains2 f h1 root6Node1Step2_checked
  have h3 := solution_checkReplacement constraints table4 table4_member
    root6Node1Domains2 root6Node1Domains3 f h2 root6Node1Step3_checked
  have h4 := solution_checkReplacement constraints table26 table26_member
    root6Node1Domains3 root6Node1Domains4 f h3 root6Node1Step4_checked
  have hb : Covers root6Node1Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node1Domains4 root6Outputs 3
    intro s hs
    change s ∈ [(1,5),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node2_cover
    · exact root6Node5_cover
  exact hb f h4
theorem root6Node0_cover : Covers root6Node0Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table18 table18_member
    root6Node0Domains0 root6Node0Domains1 f hf root6Node0Step1_checked
  have h2 := solution_checkReplacement constraints table10 table10_member
    root6Node0Domains1 root6Node0Domains2 f h1 root6Node0Step2_checked
  have h3 := solution_checkReplacement constraints table30 table30_member
    root6Node0Domains2 root6Node0Domains3 f h2 root6Node0Step3_checked
  have h4 := solution_checkReplacement constraints table13 table13_member
    root6Node0Domains3 root6Node0Domains4 f h3 root6Node0Step4_checked
  have hb : Covers root6Node0Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node0Domains4 root6Outputs 17
    intro s hs
    change s ∈ [(2,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node1_cover
    · exact root6Node6_cover
  exact hb f h4
theorem root6_table_cover : Covers (domains (6,0)) constraints root6Outputs := root6Node0_cover
theorem root6Family_count : root6Family.length = 23 := rfl
#print axioms root6_table_cover
end SpectreFinite.HexSearch.RadiusThree
