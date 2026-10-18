module

public import SpectreFinite.RadiusTwoRoot6Part6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root6Node33_cover : Covers root6Node33Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root6Node33Domains0 root6Node33Domains1 f hf root6Node33Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node33Domains1 root6Node33Domains2 f h1 root6Node33Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node33Domains2 (.output 17)
    root6Node33Leaf_checked f h2
theorem root6Node32_cover : Covers root6Node32Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node32Domains0 (.output 16)
    root6Node32Leaf_checked f hf
theorem root6Node31_cover : Covers root6Node31Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node31Domains0 (.output 15)
    root6Node31Leaf_checked f hf
theorem root6Node30_cover : Covers root6Node30Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root6Node30Domains0 root6Node30Domains1 f hf root6Node30Step1_checked
  have hb : Covers root6Node30Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node30Domains1 root6Outputs 16
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node31_cover
    · exact root6Node32_cover
  exact hb f h1
theorem root6Node29_cover : Covers root6Node29Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table8 table8_member
    root6Node29Domains0 root6Node29Domains1 f hf root6Node29Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node29Domains1 root6Node29Domains2 f h1 root6Node29Step2_checked
  have h3 := solution_checkReplacement constraints table14 table14_member
    root6Node29Domains2 root6Node29Domains3 f h2 root6Node29Step3_checked
  have hb : Covers root6Node29Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node29Domains3 root6Outputs 11
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node30_cover
    · exact root6Node33_cover
  exact hb f h3
theorem root6Node28_cover : Covers root6Node28Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node28Domains0 root6Node28Domains1 f hf root6Node28Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root6Node28Domains1 root6Node28Domains2 f h1 root6Node28Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node28Domains2 (.output 14)
    root6Node28Leaf_checked f h2
theorem root6Node27_cover : Covers root6Node27Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table13 table13_member
    root6Node27Domains0 root6Node27Domains1 f hf root6Node27Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root6Node27Domains1 root6Node27Domains2 f h1 root6Node27Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node27Domains2 (.output 13)
    root6Node27Leaf_checked f h2
theorem root6Node26_cover : Covers root6Node26Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root6Node26Domains0 root6Node26Domains1 f hf root6Node26Step1_checked
  have hb : Covers root6Node26Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node26Domains1 root6Outputs 12
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node27_cover
    · exact root6Node28_cover
  exact hb f h1
theorem root6Node25_cover : Covers root6Node25Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root6Node25Domains0 root6Node25Domains1 f hf root6Node25Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node25Domains1 root6Node25Domains2 f h1 root6Node25Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node25Domains2 (.output 12)
    root6Node25Leaf_checked f h2
theorem root6Node24_cover : Covers root6Node24Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root6Node24Domains0 root6Node24Domains1 f hf root6Node24Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node24Domains1 root6Node24Domains2 f h1 root6Node24Step2_checked
  have hb : Covers root6Node24Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node24Domains2 root6Outputs 11
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node25_cover
    · exact root6Node26_cover
  exact hb f h2
theorem root6Node23_cover : Covers root6Node23Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root6Node23Domains0 root6Node23Domains1 f hf root6Node23Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root6Node23Domains1 root6Node23Domains2 f h1 root6Node23Step2_checked
  have h3 := solution_checkReplacement constraints table14 table14_member
    root6Node23Domains2 root6Node23Domains3 f h2 root6Node23Step3_checked
  have h4 := solution_checkReplacement constraints table3 table3_member
    root6Node23Domains3 root6Node23Domains4 f h3 root6Node23Step4_checked
  have h5 := solution_checkReplacement constraints table12 table12_member
    root6Node23Domains4 root6Node23Domains5 f h4 root6Node23Step5_checked
  have hb : Covers root6Node23Domains5 constraints root6Outputs := by
    apply covers_of_branches root6Node23Domains5 root6Outputs 3
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node24_cover
    · exact root6Node29_cover
  exact hb f h5
theorem root6Node22_cover : Covers root6Node22Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root6Node22Domains0 root6Node22Domains1 f hf root6Node22Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node22Domains1 root6Node22Domains2 f h1 root6Node22Step2_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node22Domains2 (.output 11)
    root6Node22Leaf_checked f h2
theorem root6Node21_cover : Covers root6Node21Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node21Domains0 (.output 10)
    root6Node21Leaf_checked f hf
theorem root6Node20_cover : Covers root6Node20Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node20Domains0 (.output 9)
    root6Node20Leaf_checked f hf
theorem root6Node19_cover : Covers root6Node19Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table15 table15_member
    root6Node19Domains0 root6Node19Domains1 f hf root6Node19Step1_checked
  have hb : Covers root6Node19Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node19Domains1 root6Outputs 16
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node20_cover
    · exact root6Node21_cover
  exact hb f h1
theorem root6Node18_cover : Covers root6Node18Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table5 table5_member
    root6Node18Domains0 root6Node18Domains1 f hf root6Node18Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root6Node18Domains1 root6Node18Domains2 f h1 root6Node18Step2_checked
  have hb : Covers root6Node18Domains2 constraints root6Outputs := by
    apply covers_of_branches root6Node18Domains2 root6Outputs 11
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node19_cover
    · exact root6Node22_cover
  exact hb f h2
theorem root6Node17_cover : Covers root6Node17Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node17Domains0 (.output 8)
    root6Node17Leaf_checked f hf
theorem root6Node16_cover : Covers root6Node16Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node16Domains0 (.output 7)
    root6Node16Leaf_checked f hf
theorem root6Node15_cover : Covers root6Node15Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root6Node15Domains0 root6Node15Domains1 f hf root6Node15Step1_checked
  have hb : Covers root6Node15Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node15Domains1 root6Outputs 16
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node16_cover
    · exact root6Node17_cover
  exact hb f h1
theorem root6Node14_cover : Covers root6Node14Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node14Domains0 (.output 6)
    root6Node14Leaf_checked f hf
theorem root6Node13_cover : Covers root6Node13Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node13Domains0 (.output 5)
    root6Node13Leaf_checked f hf
theorem root6Node12_cover : Covers root6Node12Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root6Node12Domains0 root6Node12Domains1 f hf root6Node12Step1_checked
  have hb : Covers root6Node12Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node12Domains1 root6Outputs 16
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node13_cover
    · exact root6Node14_cover
  exact hb f h1
theorem root6Node11_cover : Covers root6Node11Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root6Node11Domains0 root6Node11Domains1 f hf root6Node11Step1_checked
  have hb : Covers root6Node11Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node11Domains1 root6Outputs 6
    intro s hs
    change s ∈ [(2,4),(4,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node12_cover
    · exact root6Node15_cover
  exact hb f h1
theorem root6Node10_cover : Covers root6Node10Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node10Domains0 (.output 4)
    root6Node10Leaf_checked f hf
theorem root6Node9_cover : Covers root6Node9Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node9Domains0 (.output 3)
    root6Node9Leaf_checked f hf
theorem root6Node8_cover : Covers root6Node8Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node8Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node8Domains0 root6Outputs 16
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node9_cover
    · exact root6Node10_cover
  exact hb f hf
theorem root6Node7_cover : Covers root6Node7Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node7Domains0 (.output 2)
    root6Node7Leaf_checked f hf
theorem root6Node6_cover : Covers root6Node6Domains0 constraints root6Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root6Outputs root6Node6Domains0 (.output 1)
    root6Node6Leaf_checked f hf
theorem root6Node5_cover : Covers root6Node5Domains0 constraints root6Outputs := by
  intro f hf
  have hb : Covers root6Node5Domains0 constraints root6Outputs := by
    apply covers_of_branches root6Node5Domains0 root6Outputs 16
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node6_cover
    · exact root6Node7_cover
  exact hb f hf
theorem root6Node4_cover : Covers root6Node4Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root6Node4Domains0 root6Node4Domains1 f hf root6Node4Step1_checked
  have hb : Covers root6Node4Domains1 constraints root6Outputs := by
    apply covers_of_branches root6Node4Domains1 root6Outputs 2
    intro s hs
    change s ∈ [(1,5),(6,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node5_cover
    · exact root6Node8_cover
  exact hb f h1
theorem root6Node3_cover : Covers root6Node3Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root6Node3Domains0 root6Node3Domains1 f hf root6Node3Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root6Node3Domains1 root6Node3Domains2 f h1 root6Node3Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root6Node3Domains2 root6Node3Domains3 f h2 root6Node3Step3_checked
  have hb : Covers root6Node3Domains3 constraints root6Outputs := by
    apply covers_of_branches root6Node3Domains3 root6Outputs 10
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node4_cover
    · exact root6Node11_cover
  exact hb f h3
theorem root6Node2_cover : Covers root6Node2Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root6Node2Domains0 root6Node2Domains1 f hf root6Node2Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root6Node2Domains1 root6Node2Domains2 f h1 root6Node2Step2_checked
  have h3 := solution_checkReplacement constraints table14 table14_member
    root6Node2Domains2 root6Node2Domains3 f h2 root6Node2Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root6Node2Domains3 root6Node2Domains4 f h3 root6Node2Step4_checked
  have h5 := solution_checkReplacement constraints table6 table6_member
    root6Node2Domains4 root6Node2Domains5 f h4 root6Node2Step5_checked
  have h6 := solution_checkReplacement constraints table13 table13_member
    root6Node2Domains5 root6Node2Domains6 f h5 root6Node2Step6_checked
  have hb : Covers root6Node2Domains6 constraints root6Outputs := by
    apply covers_of_branches root6Node2Domains6 root6Outputs 1
    intro s hs
    change s ∈ [(4,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root6Node3_cover
    · exact root6Node18_cover
  exact hb f h6
theorem root6Node1_cover : Covers root6Node1Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root6Node1Domains0 root6Node1Domains1 f hf root6Node1Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root6Node1Domains1 root6Node1Domains2 f h1 root6Node1Step2_checked
  have h3 := solution_checkReplacement constraints table15 table15_member
    root6Node1Domains2 root6Node1Domains3 f h2 root6Node1Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root6Node1Domains3 root6Node1Domains4 f h3 root6Node1Step4_checked
  have h5 := solution_checkReplacement constraints table2 table2_member
    root6Node1Domains4 root6Node1Domains5 f h4 root6Node1Step5_checked
  exact checkCover_sound 1 constraints root6Outputs root6Node1Domains5 (.output 0)
    root6Node1Leaf_checked f h5
theorem root6Node0_cover : Covers root6Node0Domains0 constraints root6Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root6Node0Domains0 root6Node0Domains1 f hf root6Node0Step1_checked
  have h2 := solution_checkReplacement constraints table14 table14_member
    root6Node0Domains1 root6Node0Domains2 f h1 root6Node0Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root6Node0Domains2 root6Node0Domains3 f h2 root6Node0Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root6Node0Domains3 root6Node0Domains4 f h3 root6Node0Step4_checked
  have hb : Covers root6Node0Domains4 constraints root6Outputs := by
    apply covers_of_branches root6Node0Domains4 root6Outputs 0
    intro s hs
    change s ∈ [(4,2),(7,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact root6Node1_cover
    · exact root6Node2_cover
    · exact root6Node23_cover
  exact hb f h4
theorem root6_table_cover : Covers (domains (6,0)) constraints root6Outputs :=
  root6Node0_cover

theorem root6Family_count : root6Family.length = 18 := rfl

theorem extract_mem_root6Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (6,0)) :
    extract f center (hexRegion 2) ∈ root6Family := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (6,0) (hexRegion 2) root6Outputs
    root6_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root6Family] using h
#print axioms extract_mem_root6Family
end SpectreFinite.HexSearch.RadiusTwo
