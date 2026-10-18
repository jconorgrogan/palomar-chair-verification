module

public import SpectreFinite.RadiusTwoRoot4Part5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root4Node34_cover : Covers root4Node34Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node34Domains0 (.output 17)
    root4Node34Leaf_checked f hf
theorem root4Node33_cover : Covers root4Node33Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node33Domains0 (.output 16)
    root4Node33Leaf_checked f hf
theorem root4Node32_cover : Covers root4Node32Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root4Node32Domains0 root4Node32Domains1 f hf root4Node32Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node32Domains1 root4Node32Domains2 f h1 root4Node32Step2_checked
  have hb : Covers root4Node32Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node32Domains2 root4Outputs 11
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node33_cover
    · exact root4Node34_cover
  exact hb f h2
theorem root4Node31_cover : Covers root4Node31Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node31Domains0 (.output 15)
    root4Node31Leaf_checked f hf
theorem root4Node30_cover : Covers root4Node30Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node30Domains0 (.output 14)
    root4Node30Leaf_checked f hf
theorem root4Node29_cover : Covers root4Node29Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node29Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node29Domains0 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node30_cover
    · exact root4Node31_cover
  exact hb f hf
theorem root4Node28_cover : Covers root4Node28Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node28Domains0 (.output 13)
    root4Node28Leaf_checked f hf
theorem root4Node27_cover : Covers root4Node27Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node27Domains0 (.output 12)
    root4Node27Leaf_checked f hf
theorem root4Node26_cover : Covers root4Node26Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node26Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node26Domains0 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node27_cover
    · exact root4Node28_cover
  exact hb f hf
theorem root4Node25_cover : Covers root4Node25Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root4Node25Domains0 root4Node25Domains1 f hf root4Node25Step1_checked
  have hb : Covers root4Node25Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node25Domains1 root4Outputs 11
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node26_cover
    · exact root4Node29_cover
  exact hb f h1
theorem root4Node24_cover : Covers root4Node24Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root4Node24Domains0 root4Node24Domains1 f hf root4Node24Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root4Node24Domains1 root4Node24Domains2 f h1 root4Node24Step2_checked
  have hb : Covers root4Node24Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node24Domains2 root4Outputs 3
    intro s hs
    change s ∈ [(2,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node25_cover
    · exact root4Node32_cover
  exact hb f h2
theorem root4Node23_cover : Covers root4Node23Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node23Domains0 (.output 11)
    root4Node23Leaf_checked f hf
theorem root4Node22_cover : Covers root4Node22Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node22Domains0 (.output 10)
    root4Node22Leaf_checked f hf
theorem root4Node21_cover : Covers root4Node21Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root4Node21Domains0 root4Node21Domains1 f hf root4Node21Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node21Domains1 root4Node21Domains2 f h1 root4Node21Step2_checked
  have hb : Covers root4Node21Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node21Domains2 root4Outputs 11
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node22_cover
    · exact root4Node23_cover
  exact hb f h2
theorem root4Node20_cover : Covers root4Node20Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node20Domains0 (.output 9)
    root4Node20Leaf_checked f hf
theorem root4Node19_cover : Covers root4Node19Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node19Domains0 (.output 8)
    root4Node19Leaf_checked f hf
theorem root4Node18_cover : Covers root4Node18Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node18Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node18Domains0 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node19_cover
    · exact root4Node20_cover
  exact hb f hf
theorem root4Node17_cover : Covers root4Node17Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node17Domains0 (.output 7)
    root4Node17Leaf_checked f hf
theorem root4Node16_cover : Covers root4Node16Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node16Domains0 (.output 6)
    root4Node16Leaf_checked f hf
theorem root4Node15_cover : Covers root4Node15Domains0 constraints root4Outputs := by
  intro f hf
  have hb : Covers root4Node15Domains0 constraints root4Outputs := by
    apply covers_of_branches root4Node15Domains0 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node16_cover
    · exact root4Node17_cover
  exact hb f hf
theorem root4Node14_cover : Covers root4Node14Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root4Node14Domains0 root4Node14Domains1 f hf root4Node14Step1_checked
  have hb : Covers root4Node14Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node14Domains1 root4Outputs 11
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node15_cover
    · exact root4Node18_cover
  exact hb f h1
theorem root4Node13_cover : Covers root4Node13Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root4Node13Domains0 root4Node13Domains1 f hf root4Node13Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root4Node13Domains1 root4Node13Domains2 f h1 root4Node13Step2_checked
  have hb : Covers root4Node13Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node13Domains2 root4Outputs 3
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node14_cover
    · exact root4Node21_cover
  exact hb f h2
theorem root4Node12_cover : Covers root4Node12Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root4Node12Domains0 root4Node12Domains1 f hf root4Node12Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root4Node12Domains1 root4Node12Domains2 f h1 root4Node12Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root4Node12Domains2 root4Node12Domains3 f h2 root4Node12Step3_checked
  have h4 := solution_checkReplacement constraints table13 table13_member
    root4Node12Domains3 root4Node12Domains4 f h3 root4Node12Step4_checked
  have hb : Covers root4Node12Domains4 constraints root4Outputs := by
    apply covers_of_branches root4Node12Domains4 root4Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node13_cover
    · exact root4Node24_cover
  exact hb f h4
theorem root4Node11_cover : Covers root4Node11Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root4Node11Domains0 root4Node11Domains1 f hf root4Node11Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node11Domains1 root4Node11Domains2 f h1 root4Node11Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node11Domains2 (.output 5)
    root4Node11Leaf_checked f h2
theorem root4Node10_cover : Covers root4Node10Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node10Domains0 (.output 4)
    root4Node10Leaf_checked f hf
theorem root4Node9_cover : Covers root4Node9Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node9Domains0 (.output 3)
    root4Node9Leaf_checked f hf
theorem root4Node8_cover : Covers root4Node8Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table7 table7_member
    root4Node8Domains0 root4Node8Domains1 f hf root4Node8Step1_checked
  have hb : Covers root4Node8Domains1 constraints root4Outputs := by
    apply covers_of_branches root4Node8Domains1 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node9_cover
    · exact root4Node10_cover
  exact hb f h1
theorem root4Node7_cover : Covers root4Node7Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root4Node7Domains0 root4Node7Domains1 f hf root4Node7Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node7Domains1 root4Node7Domains2 f h1 root4Node7Step2_checked
  have hb : Covers root4Node7Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node7Domains2 root4Outputs 3
    intro s hs
    change s ∈ [(2,1),(4,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node8_cover
    · exact root4Node11_cover
  exact hb f h2
theorem root4Node6_cover : Covers root4Node6Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node6Domains0 (.output 2)
    root4Node6Leaf_checked f hf
theorem root4Node5_cover : Covers root4Node5Domains0 constraints root4Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root4Outputs root4Node5Domains0 (.output 1)
    root4Node5Leaf_checked f hf
theorem root4Node4_cover : Covers root4Node4Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root4Node4Domains0 root4Node4Domains1 f hf root4Node4Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node4Domains1 root4Node4Domains2 f h1 root4Node4Step2_checked
  have hb : Covers root4Node4Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node4Domains2 root4Outputs 17
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node5_cover
    · exact root4Node6_cover
  exact hb f h2
theorem root4Node3_cover : Covers root4Node3Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root4Node3Domains0 root4Node3Domains1 f hf root4Node3Step1_checked
  have h2 := solution_checkReplacement constraints table13 table13_member
    root4Node3Domains1 root4Node3Domains2 f h1 root4Node3Step2_checked
  exact checkCover_sound 1 constraints root4Outputs root4Node3Domains2 (.output 0)
    root4Node3Leaf_checked f h2
theorem root4Node2_cover : Covers root4Node2Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root4Node2Domains0 root4Node2Domains1 f hf root4Node2Step1_checked
  have h2 := solution_checkReplacement constraints table12 table12_member
    root4Node2Domains1 root4Node2Domains2 f h1 root4Node2Step2_checked
  have hb : Covers root4Node2Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node2Domains2 root4Outputs 7
    intro s hs
    change s ∈ [(0,1),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node3_cover
    · exact root4Node4_cover
  exact hb f h2
theorem root4Node1_cover : Covers root4Node1Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root4Node1Domains0 root4Node1Domains1 f hf root4Node1Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root4Node1Domains1 root4Node1Domains2 f h1 root4Node1Step2_checked
  have hb : Covers root4Node1Domains2 constraints root4Outputs := by
    apply covers_of_branches root4Node1Domains2 root4Outputs 0
    intro s hs
    change s ∈ [(3,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node2_cover
    · exact root4Node7_cover
  exact hb f h2
theorem root4Node0_cover : Covers root4Node0Domains0 constraints root4Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root4Node0Domains0 root4Node0Domains1 f hf root4Node0Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root4Node0Domains1 root4Node0Domains2 f h1 root4Node0Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root4Node0Domains2 root4Node0Domains3 f h2 root4Node0Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root4Node0Domains3 root4Node0Domains4 f h3 root4Node0Step4_checked
  have h5 := solution_checkReplacement constraints table1 table1_member
    root4Node0Domains4 root4Node0Domains5 f h4 root4Node0Step5_checked
  have hb : Covers root4Node0Domains5 constraints root4Outputs := by
    apply covers_of_branches root4Node0Domains5 root4Outputs 5
    intro s hs
    change s ∈ [(1,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root4Node1_cover
    · exact root4Node12_cover
  exact hb f h5
theorem root4_table_cover : Covers (domains (4,0)) constraints root4Outputs :=
  root4Node0_cover

theorem root4Family_count : root4Family.length = 18 := rfl

theorem extract_mem_root4Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (4,0)) :
    extract f center (hexRegion 2) ∈ root4Family := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (4,0) (hexRegion 2) root4Outputs
    root4_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root4Family] using h
#print axioms extract_mem_root4Family
end SpectreFinite.HexSearch.RadiusTwo
