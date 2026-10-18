module

public import SpectreFinite.RadiusFourRoot3Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root3Node4_cover : Covers root3Node4Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root3Node4Domains0 root3Node4Domains1 f hf root3Node4Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root3Node4Domains1 root3Node4Domains2 f h1 root3Node4Step2_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node4Domains2 (.output 2)
    root3Node4Leaf_checked f h2
theorem root3Node3_cover : Covers root3Node3Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root3Node3Domains0 root3Node3Domains1 f hf root3Node3Step1_checked
  have h2 := solution_checkReplacement constraints table46 table46_member
    root3Node3Domains1 root3Node3Domains2 f h1 root3Node3Step2_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node3Domains2 (.output 1)
    root3Node3Leaf_checked f h2
theorem root3Node2_cover : Covers root3Node2Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root3Node2Domains0 root3Node2Domains1 f hf root3Node2Step1_checked
  have hb : Covers root3Node2Domains1 constraints root3Outputs := by
    apply covers_of_branches root3Node2Domains1 root3Outputs 35
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node3_cover
    · exact root3Node4_cover
  exact hb f h1
theorem root3Node1_cover : Covers root3Node1Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root3Node1Domains0 root3Node1Domains1 f hf root3Node1Step1_checked
  have h2 := solution_checkReplacement constraints table35 table35_member
    root3Node1Domains1 root3Node1Domains2 f h1 root3Node1Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root3Node1Domains2 root3Node1Domains3 f h2 root3Node1Step3_checked
  exact checkCover_sound 1 constraints root3Outputs root3Node1Domains3 (.output 0)
    root3Node1Leaf_checked f h3
theorem root3Node0_cover : Covers root3Node0Domains0 constraints root3Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table31 table31_member
    root3Node0Domains0 root3Node0Domains1 f hf root3Node0Step1_checked
  have h2 := solution_checkReplacement constraints table20 table20_member
    root3Node0Domains1 root3Node0Domains2 f h1 root3Node0Step2_checked
  have h3 := solution_checkReplacement constraints table46 table46_member
    root3Node0Domains2 root3Node0Domains3 f h2 root3Node0Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root3Node0Domains3 root3Node0Domains4 f h3 root3Node0Step4_checked
  have hb : Covers root3Node0Domains4 constraints root3Outputs := by
    apply covers_of_branches root3Node0Domains4 root3Outputs 5
    intro s hs
    change s ∈ [(4,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root3Node1_cover
    · exact root3Node2_cover
  exact hb f h4
theorem root3_table_cover : Covers (domains (3,0)) constraints root3Outputs := root3Node0_cover
theorem root3Family_count : root3Family.length = 3 := rfl
#print axioms root3_table_cover
end SpectreFinite.HexSearch.RadiusFour
