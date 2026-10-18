module

public import SpectreFinite.RadiusTwoRoot8Part6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root8Node42_cover : Covers root8Node42Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node42Domains0 (.output 21)
    root8Node42Leaf_checked f hf
theorem root8Node41_cover : Covers root8Node41Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node41Domains0 (.output 20)
    root8Node41Leaf_checked f hf
theorem root8Node40_cover : Covers root8Node40Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node40Domains0 root8Node40Domains1 f hf root8Node40Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root8Node40Domains1 root8Node40Domains2 f h1 root8Node40Step2_checked
  have hb : Covers root8Node40Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node40Domains2 root8Outputs 11
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node41_cover
    · exact root8Node42_cover
  exact hb f h2
theorem root8Node39_cover : Covers root8Node39Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node39Domains0 (.output 19)
    root8Node39Leaf_checked f hf
theorem root8Node38_cover : Covers root8Node38Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node38Domains0 (.output 18)
    root8Node38Leaf_checked f hf
theorem root8Node37_cover : Covers root8Node37Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node37Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node37Domains0 root8Outputs 17
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node38_cover
    · exact root8Node39_cover
  exact hb f hf
theorem root8Node36_cover : Covers root8Node36Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node36Domains0 (.output 17)
    root8Node36Leaf_checked f hf
theorem root8Node35_cover : Covers root8Node35Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node35Domains0 (.output 16)
    root8Node35Leaf_checked f hf
theorem root8Node34_cover : Covers root8Node34Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node34Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node34Domains0 root8Outputs 17
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node35_cover
    · exact root8Node36_cover
  exact hb f hf
theorem root8Node33_cover : Covers root8Node33Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node33Domains0 root8Node33Domains1 f hf root8Node33Step1_checked
  have hb : Covers root8Node33Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node33Domains1 root8Outputs 11
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node34_cover
    · exact root8Node37_cover
  exact hb f h1
theorem root8Node32_cover : Covers root8Node32Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root8Node32Domains0 root8Node32Domains1 f hf root8Node32Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root8Node32Domains1 root8Node32Domains2 f h1 root8Node32Step2_checked
  have hb : Covers root8Node32Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node32Domains2 root8Outputs 7
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node33_cover
    · exact root8Node40_cover
  exact hb f h2
theorem root8Node31_cover : Covers root8Node31Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node31Domains0 (.output 15)
    root8Node31Leaf_checked f hf
theorem root8Node30_cover : Covers root8Node30Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node30Domains0 (.output 14)
    root8Node30Leaf_checked f hf
theorem root8Node29_cover : Covers root8Node29Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node29Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node29Domains0 root8Outputs 17
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node30_cover
    · exact root8Node31_cover
  exact hb f hf
theorem root8Node28_cover : Covers root8Node28Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node28Domains0 (.output 13)
    root8Node28Leaf_checked f hf
theorem root8Node27_cover : Covers root8Node27Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node27Domains0 (.output 12)
    root8Node27Leaf_checked f hf
theorem root8Node26_cover : Covers root8Node26Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node26Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node26Domains0 root8Outputs 17
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node27_cover
    · exact root8Node28_cover
  exact hb f hf
theorem root8Node25_cover : Covers root8Node25Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root8Node25Domains0 root8Node25Domains1 f hf root8Node25Step1_checked
  have h2 := solution_checkReplacement constraints table8 table8_member
    root8Node25Domains1 root8Node25Domains2 f h1 root8Node25Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root8Node25Domains2 root8Node25Domains3 f h2 root8Node25Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root8Node25Domains3 root8Node25Domains4 f h3 root8Node25Step4_checked
  have hb : Covers root8Node25Domains4 constraints root8Outputs := by
    apply covers_of_branches root8Node25Domains4 root8Outputs 11
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node26_cover
    · exact root8Node29_cover
  exact hb f h4
theorem root8Node24_cover : Covers root8Node24Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node24Domains0 root8Node24Domains1 f hf root8Node24Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root8Node24Domains1 root8Node24Domains2 f h1 root8Node24Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root8Node24Domains2 root8Node24Domains3 f h2 root8Node24Step3_checked
  have h4 := solution_checkReplacement constraints table3 table3_member
    root8Node24Domains3 root8Node24Domains4 f h3 root8Node24Step4_checked
  have h5 := solution_checkReplacement constraints table14 table14_member
    root8Node24Domains4 root8Node24Domains5 f h4 root8Node24Step5_checked
  have hb : Covers root8Node24Domains5 constraints root8Outputs := by
    apply covers_of_branches root8Node24Domains5 root8Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node25_cover
    · exact root8Node32_cover
  exact hb f h5
theorem root8Node23_cover : Covers root8Node23Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node23Domains0 (.output 11)
    root8Node23Leaf_checked f hf
theorem root8Node22_cover : Covers root8Node22Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node22Domains0 (.output 10)
    root8Node22Leaf_checked f hf
theorem root8Node21_cover : Covers root8Node21Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node21Domains0 root8Node21Domains1 f hf root8Node21Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root8Node21Domains1 root8Node21Domains2 f h1 root8Node21Step2_checked
  have hb : Covers root8Node21Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node21Domains2 root8Outputs 7
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node22_cover
    · exact root8Node23_cover
  exact hb f h2
theorem root8Node20_cover : Covers root8Node20Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node20Domains0 (.output 9)
    root8Node20Leaf_checked f hf
theorem root8Node19_cover : Covers root8Node19Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node19Domains0 (.output 8)
    root8Node19Leaf_checked f hf
theorem root8Node18_cover : Covers root8Node18Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node18Domains0 root8Node18Domains1 f hf root8Node18Step1_checked
  have hb : Covers root8Node18Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node18Domains1 root8Outputs 17
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node19_cover
    · exact root8Node20_cover
  exact hb f h1
theorem root8Node17_cover : Covers root8Node17Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node17Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node17Domains0 root8Outputs 12
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node18_cover
    · exact root8Node21_cover
  exact hb f hf
theorem root8Node16_cover : Covers root8Node16Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node16Domains0 (.output 7)
    root8Node16Leaf_checked f hf
theorem root8Node15_cover : Covers root8Node15Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node15Domains0 (.output 6)
    root8Node15Leaf_checked f hf
theorem root8Node14_cover : Covers root8Node14Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node14Domains0 root8Node14Domains1 f hf root8Node14Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root8Node14Domains1 root8Node14Domains2 f h1 root8Node14Step2_checked
  have hb : Covers root8Node14Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node14Domains2 root8Outputs 7
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node15_cover
    · exact root8Node16_cover
  exact hb f h2
theorem root8Node13_cover : Covers root8Node13Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node13Domains0 (.output 5)
    root8Node13Leaf_checked f hf
theorem root8Node12_cover : Covers root8Node12Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node12Domains0 (.output 4)
    root8Node12Leaf_checked f hf
theorem root8Node11_cover : Covers root8Node11Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node11Domains0 root8Node11Domains1 f hf root8Node11Step1_checked
  have hb : Covers root8Node11Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node11Domains1 root8Outputs 17
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node12_cover
    · exact root8Node13_cover
  exact hb f h1
theorem root8Node10_cover : Covers root8Node10Domains0 constraints root8Outputs := by
  intro f hf
  have hb : Covers root8Node10Domains0 constraints root8Outputs := by
    apply covers_of_branches root8Node10Domains0 root8Outputs 12
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node11_cover
    · exact root8Node14_cover
  exact hb f hf
theorem root8Node9_cover : Covers root8Node9Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node9Domains0 root8Node9Domains1 f hf root8Node9Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root8Node9Domains1 root8Node9Domains2 f h1 root8Node9Step2_checked
  have hb : Covers root8Node9Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node9Domains2 root8Outputs 6
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node10_cover
    · exact root8Node17_cover
  exact hb f h2
theorem root8Node8_cover : Covers root8Node8Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node8Domains0 (.output 3)
    root8Node8Leaf_checked f hf
theorem root8Node7_cover : Covers root8Node7Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node7Domains0 (.output 2)
    root8Node7Leaf_checked f hf
theorem root8Node6_cover : Covers root8Node6Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node6Domains0 root8Node6Domains1 f hf root8Node6Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root8Node6Domains1 root8Node6Domains2 f h1 root8Node6Step2_checked
  have hb : Covers root8Node6Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node6Domains2 root8Outputs 7
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node7_cover
    · exact root8Node8_cover
  exact hb f h2
theorem root8Node5_cover : Covers root8Node5Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node5Domains0 (.output 1)
    root8Node5Leaf_checked f hf
theorem root8Node4_cover : Covers root8Node4Domains0 constraints root8Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root8Outputs root8Node4Domains0 (.output 0)
    root8Node4Leaf_checked f hf
theorem root8Node3_cover : Covers root8Node3Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root8Node3Domains0 root8Node3Domains1 f hf root8Node3Step1_checked
  have hb : Covers root8Node3Domains1 constraints root8Outputs := by
    apply covers_of_branches root8Node3Domains1 root8Outputs 17
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node4_cover
    · exact root8Node5_cover
  exact hb f h1
theorem root8Node2_cover : Covers root8Node2Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table10 table10_member
    root8Node2Domains0 root8Node2Domains1 f hf root8Node2Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root8Node2Domains1 root8Node2Domains2 f h1 root8Node2Step2_checked
  have hb : Covers root8Node2Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node2Domains2 root8Outputs 12
    intro s hs
    change s ∈ [(0,4),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node3_cover
    · exact root8Node6_cover
  exact hb f h2
theorem root8Node1_cover : Covers root8Node1Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root8Node1Domains0 root8Node1Domains1 f hf root8Node1Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root8Node1Domains1 root8Node1Domains2 f h1 root8Node1Step2_checked
  have hb : Covers root8Node1Domains2 constraints root8Outputs := by
    apply covers_of_branches root8Node1Domains2 root8Outputs 10
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node2_cover
    · exact root8Node9_cover
  exact hb f h2
theorem root8Node0_cover : Covers root8Node0Domains0 constraints root8Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root8Node0Domains0 root8Node0Domains1 f hf root8Node0Step1_checked
  have h2 := solution_checkReplacement constraints table5 table5_member
    root8Node0Domains1 root8Node0Domains2 f h1 root8Node0Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root8Node0Domains2 root8Node0Domains3 f h2 root8Node0Step3_checked
  have h4 := solution_checkReplacement constraints table3 table3_member
    root8Node0Domains3 root8Node0Domains4 f h3 root8Node0Step4_checked
  have h5 := solution_checkReplacement constraints table1 table1_member
    root8Node0Domains4 root8Node0Domains5 f h4 root8Node0Step5_checked
  have hb : Covers root8Node0Domains5 constraints root8Outputs := by
    apply covers_of_branches root8Node0Domains5 root8Outputs 5
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root8Node1_cover
    · exact root8Node24_cover
  exact hb f h5
theorem root8_table_cover : Covers (domains (8,0)) constraints root8Outputs :=
  root8Node0_cover

theorem root8Family_count : root8Family.length = 22 := rfl

theorem extract_mem_root8Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (8,0)) :
    extract f center (hexRegion 2) ∈ root8Family := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (8,0) (hexRegion 2) root8Outputs
    root8_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root8Family] using h
#print axioms extract_mem_root8Family
end SpectreFinite.HexSearch.RadiusTwo
