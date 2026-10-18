module

public import SpectreFinite.RadiusThreeRoot2Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root2Node0_cover : Covers root2Node0Domains0 constraints root2Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table11 table11_member
    root2Node0Domains0 root2Node0Domains1 f hf root2Node0Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root2Node0Domains1 root2Node0Domains2 f h1 root2Node0Step2_checked
  have h3 := solution_checkReplacement constraints table13 table13_member
    root2Node0Domains2 root2Node0Domains3 f h2 root2Node0Step3_checked
  have h4 := solution_checkReplacement constraints table22 table22_member
    root2Node0Domains3 root2Node0Domains4 f h3 root2Node0Step4_checked
  exact checkCover_sound 1 constraints root2Outputs root2Node0Domains4 (.output 0)
    root2Node0Leaf_checked f h4
theorem root2_table_cover : Covers (domains (2,0)) constraints root2Outputs := root2Node0_cover
theorem root2Family_count : root2Family.length = 1 := rfl
#print axioms root2_table_cover
end SpectreFinite.HexSearch.RadiusThree
