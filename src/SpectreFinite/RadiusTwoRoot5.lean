module

public import SpectreFinite.RadiusTwoRoot5Part4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root5Node32_cover : Covers root5Node32Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node32Domains0 root5Node32Domains1 f hf root5Node32Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node32Domains1 (.output 16)
    root5Node32Leaf_checked f h1
theorem root5Node31_cover : Covers root5Node31Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node31Domains0 root5Node31Domains1 f hf root5Node31Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node31Domains1 (.output 15)
    root5Node31Leaf_checked f h1
theorem root5Node30_cover : Covers root5Node30Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node30Domains0 root5Node30Domains1 f hf root5Node30Step1_checked
  have hb : Covers root5Node30Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node30Domains1 root5Outputs 12
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node31_cover
    · exact root5Node32_cover
  exact hb f h1
theorem root5Node29_cover : Covers root5Node29Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node29Domains0 root5Node29Domains1 f hf root5Node29Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node29Domains1 (.output 14)
    root5Node29Leaf_checked f h1
theorem root5Node28_cover : Covers root5Node28Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node28Domains0 root5Node28Domains1 f hf root5Node28Step1_checked
  have hb : Covers root5Node28Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node28Domains1 root5Outputs 7
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node29_cover
    · exact root5Node30_cover
  exact hb f h1
theorem root5Node27_cover : Covers root5Node27Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node27Domains0 root5Node27Domains1 f hf root5Node27Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node27Domains1 (.output 13)
    root5Node27Leaf_checked f h1
theorem root5Node26_cover : Covers root5Node26Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node26Domains0 root5Node26Domains1 f hf root5Node26Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node26Domains1 (.output 12)
    root5Node26Leaf_checked f h1
theorem root5Node25_cover : Covers root5Node25Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node25Domains0 root5Node25Domains1 f hf root5Node25Step1_checked
  have hb : Covers root5Node25Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node25Domains1 root5Outputs 12
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node26_cover
    · exact root5Node27_cover
  exact hb f h1
theorem root5Node24_cover : Covers root5Node24Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node24Domains0 root5Node24Domains1 f hf root5Node24Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node24Domains1 (.output 11)
    root5Node24Leaf_checked f h1
theorem root5Node23_cover : Covers root5Node23Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node23Domains0 root5Node23Domains1 f hf root5Node23Step1_checked
  have hb : Covers root5Node23Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node23Domains1 root5Outputs 7
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node24_cover
    · exact root5Node25_cover
  exact hb f h1
theorem root5Node22_cover : Covers root5Node22Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root5Node22Domains0 root5Node22Domains1 f hf root5Node22Step1_checked
  have hb : Covers root5Node22Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node22Domains1 root5Outputs 2
    intro s hs
    change s ∈ [(2,4),(4,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node23_cover
    · exact root5Node28_cover
  exact hb f h1
theorem root5Node21_cover : Covers root5Node21Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node21Domains0 root5Node21Domains1 f hf root5Node21Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node21Domains1 (.output 10)
    root5Node21Leaf_checked f h1
theorem root5Node20_cover : Covers root5Node20Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node20Domains0 root5Node20Domains1 f hf root5Node20Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node20Domains1 (.output 9)
    root5Node20Leaf_checked f h1
theorem root5Node19_cover : Covers root5Node19Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node19Domains0 root5Node19Domains1 f hf root5Node19Step1_checked
  have hb : Covers root5Node19Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node19Domains1 root5Outputs 12
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node20_cover
    · exact root5Node21_cover
  exact hb f h1
theorem root5Node18_cover : Covers root5Node18Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node18Domains0 root5Node18Domains1 f hf root5Node18Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node18Domains1 (.output 8)
    root5Node18Leaf_checked f h1
theorem root5Node17_cover : Covers root5Node17Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root5Node17Domains0 root5Node17Domains1 f hf root5Node17Step1_checked
  have hb : Covers root5Node17Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node17Domains1 root5Outputs 7
    intro s hs
    change s ∈ [(1,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node18_cover
    · exact root5Node19_cover
  exact hb f h1
theorem root5Node16_cover : Covers root5Node16Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root5Node16Domains0 root5Node16Domains1 f hf root5Node16Step1_checked
  have h2 := solution_checkReplacement constraints table0 table0_member
    root5Node16Domains1 root5Node16Domains2 f h1 root5Node16Step2_checked
  have hb : Covers root5Node16Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node16Domains2 root5Outputs 5
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node17_cover
    · exact root5Node22_cover
  exact hb f h2
theorem root5Node15_cover : Covers root5Node15Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node15Domains0 root5Node15Domains1 f hf root5Node15Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node15Domains1 (.output 7)
    root5Node15Leaf_checked f h1
theorem root5Node14_cover : Covers root5Node14Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table2 table2_member
    root5Node14Domains0 root5Node14Domains1 f hf root5Node14Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node14Domains1 (.output 6)
    root5Node14Leaf_checked f h1
theorem root5Node13_cover : Covers root5Node13Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root5Node13Domains0 root5Node13Domains1 f hf root5Node13Step1_checked
  have hb : Covers root5Node13Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node13Domains1 root5Outputs 2
    intro s hs
    change s ∈ [(7,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node14_cover
    · exact root5Node15_cover
  exact hb f h1
theorem root5Node12_cover : Covers root5Node12Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root5Node12Domains0 root5Node12Domains1 f hf root5Node12Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node12Domains1 (.output 5)
    root5Node12Leaf_checked f h1
theorem root5Node11_cover : Covers root5Node11Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root5Node11Domains0 root5Node11Domains1 f hf root5Node11Step1_checked
  have h2 := solution_checkReplacement constraints table8 table8_member
    root5Node11Domains1 root5Node11Domains2 f h1 root5Node11Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root5Node11Domains2 root5Node11Domains3 f h2 root5Node11Step3_checked
  have hb : Covers root5Node11Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node11Domains3 root5Outputs 5
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node12_cover
    · exact root5Node13_cover
  exact hb f h3
theorem root5Node10_cover : Covers root5Node10Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root5Node10Domains0 root5Node10Domains1 f hf root5Node10Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root5Node10Domains1 root5Node10Domains2 f h1 root5Node10Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root5Node10Domains2 root5Node10Domains3 f h2 root5Node10Step3_checked
  have hb : Covers root5Node10Domains3 constraints root5Outputs := by
    apply covers_of_branches root5Node10Domains3 root5Outputs 0
    intro s hs
    change s ∈ [(0,1),(1,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node11_cover
    · exact root5Node16_cover
  exact hb f h3
theorem root5Node9_cover : Covers root5Node9Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node9Domains0 root5Node9Domains1 f hf root5Node9Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node9Domains1 (.output 4)
    root5Node9Leaf_checked f h1
theorem root5Node8_cover : Covers root5Node8Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node8Domains0 root5Node8Domains1 f hf root5Node8Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node8Domains1 (.output 3)
    root5Node8Leaf_checked f h1
theorem root5Node7_cover : Covers root5Node7Domains0 constraints root5Outputs := by
  intro f hf
  have hb : Covers root5Node7Domains0 constraints root5Outputs := by
    apply covers_of_branches root5Node7Domains0 root5Outputs 12
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node8_cover
    · exact root5Node9_cover
  exact hb f hf
theorem root5Node6_cover : Covers root5Node6Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node6Domains0 root5Node6Domains1 f hf root5Node6Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node6Domains1 (.output 2)
    root5Node6Leaf_checked f h1
theorem root5Node5_cover : Covers root5Node5Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node5Domains0 root5Node5Domains1 f hf root5Node5Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node5Domains1 (.output 1)
    root5Node5Leaf_checked f h1
theorem root5Node4_cover : Covers root5Node4Domains0 constraints root5Outputs := by
  intro f hf
  have hb : Covers root5Node4Domains0 constraints root5Outputs := by
    apply covers_of_branches root5Node4Domains0 root5Outputs 12
    intro s hs
    change s ∈ [(1,2),(6,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node5_cover
    · exact root5Node6_cover
  exact hb f hf
theorem root5Node3_cover : Covers root5Node3Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node3Domains0 root5Node3Domains1 f hf root5Node3Step1_checked
  have hb : Covers root5Node3Domains1 constraints root5Outputs := by
    apply covers_of_branches root5Node3Domains1 root5Outputs 7
    intro s hs
    change s ∈ [(3,3),(7,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node4_cover
    · exact root5Node7_cover
  exact hb f h1
theorem root5Node2_cover : Covers root5Node2Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root5Node2Domains0 root5Node2Domains1 f hf root5Node2Step1_checked
  exact checkCover_sound 1 constraints root5Outputs root5Node2Domains1 (.output 0)
    root5Node2Leaf_checked f h1
theorem root5Node1_cover : Covers root5Node1Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root5Node1Domains0 root5Node1Domains1 f hf root5Node1Step1_checked
  have h2 := solution_checkReplacement constraints table6 table6_member
    root5Node1Domains1 root5Node1Domains2 f h1 root5Node1Step2_checked
  have hb : Covers root5Node1Domains2 constraints root5Outputs := by
    apply covers_of_branches root5Node1Domains2 root5Outputs 13
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node2_cover
    · exact root5Node3_cover
  exact hb f h2
theorem root5Node0_cover : Covers root5Node0Domains0 constraints root5Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table14 table14_member
    root5Node0Domains0 root5Node0Domains1 f hf root5Node0Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root5Node0Domains1 root5Node0Domains2 f h1 root5Node0Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root5Node0Domains2 root5Node0Domains3 f h2 root5Node0Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root5Node0Domains3 root5Node0Domains4 f h3 root5Node0Step4_checked
  have hb : Covers root5Node0Domains4 constraints root5Outputs := by
    apply covers_of_branches root5Node0Domains4 root5Outputs 8
    intro s hs
    change s ∈ [(5,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root5Node1_cover
    · exact root5Node10_cover
  exact hb f h4
theorem root5_table_cover : Covers (domains (5,0)) constraints root5Outputs :=
  root5Node0_cover

theorem root5Family_count : root5Family.length = 17 := rfl

theorem extract_mem_root5Family (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (hroot : f center = (5,0)) :
    extract f center (hexRegion 2) ∈ root5Family := by
  have h := extract_mem_of_table_cover positions RadiusOne.positions
    SignaturePruning.certifiedFamily (5,0) (hexRegion 2) root5Outputs
    root5_table_cover f (SignaturePruning.certifiedFamily_occurrenceComplete f hf) center hroot
  simpa only [positions_eq_hexRegion, root5Family] using h
#print axioms extract_mem_root5Family
end SpectreFinite.HexSearch.RadiusTwo
