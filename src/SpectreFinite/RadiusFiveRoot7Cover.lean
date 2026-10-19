module

public import SpectreFinite.RadiusFiveRoot7Part31
public import SpectreFinite.RadiusFiveRoot7Part82

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node210_cover : Covers root7Node210Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node210Domains0 root7Node210Domains1 f hf root7Node210Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node210Domains1 root7Node210Domains2 f h1 root7Node210Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node210Domains2 (.output 105)
    root7Node210Leaf_checked f h2
theorem root7Node209_cover : Covers root7Node209Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node209Domains0 root7Node209Domains1 f hf root7Node209Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node209Domains1 root7Node209Domains2 f h1 root7Node209Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node209Domains2 (.output 104)
    root7Node209Leaf_checked f h2
theorem root7Node208_cover : Covers root7Node208Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node208Domains0 (.output 103)
    root7Node208Leaf_checked f hf
theorem root7Node207_cover : Covers root7Node207Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node207Domains0 (.output 102)
    root7Node207Leaf_checked f hf
theorem root7Node206_cover : Covers root7Node206Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node206Domains0 root7Node206Domains1 f hf root7Node206Step1_checked
  have hb : Covers root7Node206Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node206Domains1 root7Outputs 86
    intro s hs
    change s ∈ [(3,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node207_cover
    · exact root7Node208_cover
  exact hb f h1
theorem root7Node205_cover : Covers root7Node205Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node205Domains0 root7Node205Domains1 f hf root7Node205Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node205Domains1 (.output 101)
    root7Node205Leaf_checked f h1
theorem root7Node204_cover : Covers root7Node204Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node204Domains0 root7Node204Domains1 f hf root7Node204Step1_checked
  have hb : Covers root7Node204Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node204Domains1 root7Outputs 83
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node205_cover
    · exact root7Node206_cover
  exact hb f h1
theorem root7Node203_cover : Covers root7Node203Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table6 table6_member
    root7Node203Domains0 root7Node203Domains1 f hf root7Node203Step1_checked
  have hb : Covers root7Node203Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node203Domains1 root7Outputs 40
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node204_cover
    · exact root7Node209_cover
  exact hb f h1
theorem root7Node202_cover : Covers root7Node202Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root7Node202Domains0 root7Node202Domains1 f hf root7Node202Step1_checked
  have hb : Covers root7Node202Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node202Domains1 root7Outputs 13
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node203_cover
    · exact root7Node210_cover
  exact hb f h1
theorem root7Node201_cover : Covers root7Node201Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table9 table9_member
    root7Node201Domains0 root7Node201Domains1 f hf root7Node201Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root7Node201Domains1 root7Node201Domains2 f h1 root7Node201Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root7Node201Domains2 root7Node201Domains3 f h2 root7Node201Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node201Domains3 (.output 100)
    root7Node201Leaf_checked f h3
theorem root7Node200_cover : Covers root7Node200Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root7Node200Domains0 root7Node200Domains1 f hf root7Node200Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node200Domains1 root7Node200Domains2 f h1 root7Node200Step2_checked
  have h3 := solution_checkReplacement constraints table21 table21_member
    root7Node200Domains2 root7Node200Domains3 f h2 root7Node200Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root7Node200Domains3 root7Node200Domains4 f h3 root7Node200Step4_checked
  have hb : Covers root7Node200Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node200Domains4 root7Outputs 5
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node201_cover
    · exact root7Node202_cover
  exact hb f h4
theorem root7Node199_cover : Covers root7Node199Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node199Domains0 root7Node199Domains1 f hf root7Node199Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node199Domains1 root7Node199Domains2 f h1 root7Node199Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node199Domains2 (.output 99)
    root7Node199Leaf_checked f h2
theorem root7Node198_cover : Covers root7Node198Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node198Domains0 root7Node198Domains1 f hf root7Node198Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node198Domains1 (.output 98)
    root7Node198Leaf_checked f h1
theorem root7Node197_cover : Covers root7Node197Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node197Domains0 root7Node197Domains1 f hf root7Node197Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node197Domains1 (.output 97)
    root7Node197Leaf_checked f h1
theorem root7Node196_cover : Covers root7Node196Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root7Node196Domains0 root7Node196Domains1 f hf root7Node196Step1_checked
  have hb : Covers root7Node196Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node196Domains1 root7Outputs 60
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node197_cover
    · exact root7Node198_cover
  exact hb f h1
theorem root7Node195_cover : Covers root7Node195Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node195Domains0 root7Node195Domains1 f hf root7Node195Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node195Domains1 root7Node195Domains2 f h1 root7Node195Step2_checked
  have hb : Covers root7Node195Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node195Domains2 root7Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node196_cover
    · exact root7Node199_cover
  exact hb f h2
theorem root7Node194_cover : Covers root7Node194Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node194Domains0 root7Node194Domains1 f hf root7Node194Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node194Domains1 (.output 96)
    root7Node194Leaf_checked f h1
theorem root7Node193_cover : Covers root7Node193Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node193Domains0 root7Node193Domains1 f hf root7Node193Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node193Domains1 (.output 95)
    root7Node193Leaf_checked f h1
theorem root7Node192_cover : Covers root7Node192Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root7Node192Domains0 root7Node192Domains1 f hf root7Node192Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node192Domains1 root7Node192Domains2 f h1 root7Node192Step2_checked
  have hb : Covers root7Node192Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node192Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node193_cover
    · exact root7Node194_cover
  exact hb f h2
theorem root7Node191_cover : Covers root7Node191Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root7Node191Domains0 root7Node191Domains1 f hf root7Node191Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node191Domains1 root7Node191Domains2 f h1 root7Node191Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node191Domains2 (.output 94)
    root7Node191Leaf_checked f h2
theorem root7Node190_cover : Covers root7Node190Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node190Domains0 root7Node190Domains1 f hf root7Node190Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node190Domains1 root7Node190Domains2 f h1 root7Node190Step2_checked
  have hb : Covers root7Node190Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node190Domains2 root7Outputs 41
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node191_cover
    · exact root7Node192_cover
  exact hb f h2
theorem root7Node189_cover : Covers root7Node189Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node189Domains0 root7Node189Domains1 f hf root7Node189Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node189Domains1 (.output 93)
    root7Node189Leaf_checked f h1
theorem root7Node188_cover : Covers root7Node188Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node188Domains0 root7Node188Domains1 f hf root7Node188Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node188Domains1 (.output 92)
    root7Node188Leaf_checked f h1
theorem root7Node187_cover : Covers root7Node187Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node187Domains0 root7Node187Domains1 f hf root7Node187Step1_checked
  have hb : Covers root7Node187Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node187Domains1 root7Outputs 60
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node188_cover
    · exact root7Node189_cover
  exact hb f h1
theorem root7Node186_cover : Covers root7Node186Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node186Domains0 root7Node186Domains1 f hf root7Node186Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node186Domains1 (.output 91)
    root7Node186Leaf_checked f h1
theorem root7Node185_cover : Covers root7Node185Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node185Domains0 root7Node185Domains1 f hf root7Node185Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node185Domains1 root7Node185Domains2 f h1 root7Node185Step2_checked
  have hb : Covers root7Node185Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node185Domains2 root7Outputs 49
    intro s hs
    change s ∈ [(4,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node186_cover
    · exact root7Node187_cover
  exact hb f h2
theorem root7Node184_cover : Covers root7Node184Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table12 table12_member
    root7Node184Domains0 root7Node184Domains1 f hf root7Node184Step1_checked
  have hb : Covers root7Node184Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node184Domains1 root7Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node185_cover
    · exact root7Node190_cover
  exact hb f h1
theorem root7Node183_cover : Covers root7Node183Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node183Domains0 root7Node183Domains1 f hf root7Node183Step1_checked
  have hb : Covers root7Node183Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node183Domains1 root7Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node184_cover
    · exact root7Node195_cover
  exact hb f h1
theorem root7Node182_cover : Covers root7Node182Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node182Domains0 root7Node182Domains1 f hf root7Node182Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node182Domains1 root7Node182Domains2 f h1 root7Node182Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node182Domains2 (.output 90)
    root7Node182Leaf_checked f h2
theorem root7Node181_cover : Covers root7Node181Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node181Domains0 root7Node181Domains1 f hf root7Node181Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node181Domains1 root7Node181Domains2 f h1 root7Node181Step2_checked
  have hb : Covers root7Node181Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node181Domains2 root7Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node182_cover
    · exact root7Node183_cover
  exact hb f h2
theorem root7Node180_cover : Covers root7Node180Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node180Domains0 root7Node180Domains1 f hf root7Node180Step1_checked
  have h2 := solution_checkReplacement constraints table55 table55_member
    root7Node180Domains1 root7Node180Domains2 f h1 root7Node180Step2_checked
  have h3 := solution_checkReplacement constraints table56 table56_member
    root7Node180Domains2 root7Node180Domains3 f h2 root7Node180Step3_checked
  have h4 := solution_checkReplacement constraints table6 table6_member
    root7Node180Domains3 root7Node180Domains4 f h3 root7Node180Step4_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node180Domains4 (.output 89)
    root7Node180Leaf_checked f h4
theorem root7Node179_cover : Covers root7Node179Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root7Node179Domains0 root7Node179Domains1 f hf root7Node179Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root7Node179Domains1 root7Node179Domains2 f h1 root7Node179Step2_checked
  have h3 := solution_checkReplacement constraints table3 table3_member
    root7Node179Domains2 root7Node179Domains3 f h2 root7Node179Step3_checked
  have hb : Covers root7Node179Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node179Domains3 root7Outputs 4
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node180_cover
    · exact root7Node181_cover
  exact hb f h3
theorem root7Node178_cover : Covers root7Node178Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root7Node178Domains0 root7Node178Domains1 f hf root7Node178Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root7Node178Domains1 root7Node178Domains2 f h1 root7Node178Step2_checked
  have h3 := solution_checkReplacement constraints table1 table1_member
    root7Node178Domains2 root7Node178Domains3 f h2 root7Node178Step3_checked
  have hb : Covers root7Node178Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node178Domains3 root7Outputs 0
    intro s hs
    change s ∈ [(2,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node179_cover
    · exact root7Node200_cover
  exact hb f h3
theorem root7Node177_cover : Covers root7Node177Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node177Domains0 root7Node177Domains1 f hf root7Node177Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node177Domains1 (.output 88)
    root7Node177Leaf_checked f h1
theorem root7Node176_cover : Covers root7Node176Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node176Domains0 root7Node176Domains1 f hf root7Node176Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node176Domains1 (.output 87)
    root7Node176Leaf_checked f h1
theorem root7Node175_cover : Covers root7Node175Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node175Domains0 root7Node175Domains1 f hf root7Node175Step1_checked
  have hb : Covers root7Node175Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node175Domains1 root7Outputs 40
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node176_cover
    · exact root7Node177_cover
  exact hb f h1
theorem root7Node174_cover : Covers root7Node174Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node174Domains0 root7Node174Domains1 f hf root7Node174Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node174Domains1 (.output 86)
    root7Node174Leaf_checked f h1
theorem root7Node173_cover : Covers root7Node173Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node173Domains0 root7Node173Domains1 f hf root7Node173Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node173Domains1 (.output 85)
    root7Node173Leaf_checked f h1
theorem root7Node172_cover : Covers root7Node172Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node172Domains0 root7Node172Domains1 f hf root7Node172Step1_checked
  have hb : Covers root7Node172Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node172Domains1 root7Outputs 40
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node173_cover
    · exact root7Node174_cover
  exact hb f h1
theorem root7Node171_cover : Covers root7Node171Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table33 table33_member
    root7Node171Domains0 root7Node171Domains1 f hf root7Node171Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node171Domains1 root7Node171Domains2 f h1 root7Node171Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root7Node171Domains2 root7Node171Domains3 f h2 root7Node171Step3_checked
  have h4 := solution_checkReplacement constraints table1 table1_member
    root7Node171Domains3 root7Node171Domains4 f h3 root7Node171Step4_checked
  have hb : Covers root7Node171Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node171Domains4 root7Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node172_cover
    · exact root7Node175_cover
  exact hb f h4
theorem root7Node170_cover : Covers root7Node170Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node170Domains0 root7Node170Domains1 f hf root7Node170Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node170Domains1 (.output 84)
    root7Node170Leaf_checked f h1
theorem root7Node169_cover : Covers root7Node169Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node169Domains0 root7Node169Domains1 f hf root7Node169Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node169Domains1 (.output 83)
    root7Node169Leaf_checked f h1
theorem root7Node168_cover : Covers root7Node168Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node168Domains0 root7Node168Domains1 f hf root7Node168Step1_checked
  have hb : Covers root7Node168Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node168Domains1 root7Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node169_cover
    · exact root7Node170_cover
  exact hb f h1
theorem root7Node167_cover : Covers root7Node167Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node167Domains0 root7Node167Domains1 f hf root7Node167Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node167Domains1 (.output 82)
    root7Node167Leaf_checked f h1
theorem root7Node166_cover : Covers root7Node166Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node166Domains0 root7Node166Domains1 f hf root7Node166Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node166Domains1 (.output 81)
    root7Node166Leaf_checked f h1
theorem root7Node165_cover : Covers root7Node165Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node165Domains0 root7Node165Domains1 f hf root7Node165Step1_checked
  have hb : Covers root7Node165Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node165Domains1 root7Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node166_cover
    · exact root7Node167_cover
  exact hb f h1
theorem root7Node164_cover : Covers root7Node164Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node164Domains0 root7Node164Domains1 f hf root7Node164Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root7Node164Domains1 root7Node164Domains2 f h1 root7Node164Step2_checked
  have hb : Covers root7Node164Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node164Domains2 root7Outputs 60
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node165_cover
    · exact root7Node168_cover
  exact hb f h2
theorem root7Node163_cover : Covers root7Node163Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node163Domains0 root7Node163Domains1 f hf root7Node163Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node163Domains1 (.output 80)
    root7Node163Leaf_checked f h1
theorem root7Node162_cover : Covers root7Node162Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node162Domains0 root7Node162Domains1 f hf root7Node162Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node162Domains1 (.output 79)
    root7Node162Leaf_checked f h1
theorem root7Node161_cover : Covers root7Node161Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node161Domains0 root7Node161Domains1 f hf root7Node161Step1_checked
  have hb : Covers root7Node161Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node161Domains1 root7Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node162_cover
    · exact root7Node163_cover
  exact hb f h1
theorem root7Node160_cover : Covers root7Node160Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node160Domains0 root7Node160Domains1 f hf root7Node160Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node160Domains1 (.output 78)
    root7Node160Leaf_checked f h1
theorem root7Node159_cover : Covers root7Node159Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node159Domains0 root7Node159Domains1 f hf root7Node159Step1_checked
  have hb : Covers root7Node159Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node159Domains1 root7Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node160_cover
    · exact root7Node161_cover
  exact hb f h1
theorem root7Node158_cover : Covers root7Node158Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node158Domains0 root7Node158Domains1 f hf root7Node158Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node158Domains1 root7Node158Domains2 f h1 root7Node158Step2_checked
  have hb : Covers root7Node158Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node158Domains2 root7Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node159_cover
    · exact root7Node164_cover
  exact hb f h2
theorem root7Node157_cover : Covers root7Node157Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node157Domains0 root7Node157Domains1 f hf root7Node157Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node157Domains1 (.output 77)
    root7Node157Leaf_checked f h1
theorem root7Node156_cover : Covers root7Node156Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node156Domains0 root7Node156Domains1 f hf root7Node156Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node156Domains1 (.output 76)
    root7Node156Leaf_checked f h1
theorem root7Node155_cover : Covers root7Node155Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node155Domains0 root7Node155Domains1 f hf root7Node155Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node155Domains1 root7Node155Domains2 f h1 root7Node155Step2_checked
  have hb : Covers root7Node155Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node155Domains2 root7Outputs 44
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node156_cover
    · exact root7Node157_cover
  exact hb f h2
theorem root7Node154_cover : Covers root7Node154Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node154Domains0 root7Node154Domains1 f hf root7Node154Step1_checked
  have hb : Covers root7Node154Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node154Domains1 root7Outputs 21
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node155_cover
    · exact root7Node158_cover
  exact hb f h1
theorem root7Node153_cover : Covers root7Node153Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node153Domains0 root7Node153Domains1 f hf root7Node153Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root7Node153Domains1 root7Node153Domains2 f h1 root7Node153Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node153Domains2 (.output 75)
    root7Node153Leaf_checked f h2
theorem root7Node152_cover : Covers root7Node152Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root7Node152Domains0 root7Node152Domains1 f hf root7Node152Step1_checked
  have h2 := solution_checkReplacement constraints table1 table1_member
    root7Node152Domains1 root7Node152Domains2 f h1 root7Node152Step2_checked
  have hb : Covers root7Node152Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node152Domains2 root7Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node153_cover
    · exact root7Node154_cover
  exact hb f h2
theorem root7Node151_cover : Covers root7Node151Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root7Node151Domains0 root7Node151Domains1 f hf root7Node151Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node151Domains1 root7Node151Domains2 f h1 root7Node151Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node151Domains2 (.output 74)
    root7Node151Leaf_checked f h2
theorem root7Node150_cover : Covers root7Node150Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root7Node150Domains0 root7Node150Domains1 f hf root7Node150Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node150Domains1 root7Node150Domains2 f h1 root7Node150Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node150Domains2 (.output 73)
    root7Node150Leaf_checked f h2
theorem root7Node149_cover : Covers root7Node149Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root7Node149Domains0 root7Node149Domains1 f hf root7Node149Step1_checked
  have hb : Covers root7Node149Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node149Domains1 root7Outputs 41
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node150_cover
    · exact root7Node151_cover
  exact hb f h1
theorem root7Node148_cover : Covers root7Node148Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node148Domains0 root7Node148Domains1 f hf root7Node148Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node148Domains1 root7Node148Domains2 f h1 root7Node148Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node148Domains2 (.output 72)
    root7Node148Leaf_checked f h2
theorem root7Node147_cover : Covers root7Node147Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node147Domains0 root7Node147Domains1 f hf root7Node147Step1_checked
  have hb : Covers root7Node147Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node147Domains1 root7Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node148_cover
    · exact root7Node149_cover
  exact hb f h1
theorem root7Node146_cover : Covers root7Node146Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node146Domains0 root7Node146Domains1 f hf root7Node146Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node146Domains1 root7Node146Domains2 f h1 root7Node146Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node146Domains2 (.output 71)
    root7Node146Leaf_checked f h2
theorem root7Node145_cover : Covers root7Node145Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node145Domains0 root7Node145Domains1 f hf root7Node145Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node145Domains1 root7Node145Domains2 f h1 root7Node145Step2_checked
  have hb : Covers root7Node145Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node145Domains2 root7Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node146_cover
    · exact root7Node147_cover
  exact hb f h2
theorem root7Node144_cover : Covers root7Node144Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node144Domains0 root7Node144Domains1 f hf root7Node144Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node144Domains1 root7Node144Domains2 f h1 root7Node144Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node144Domains2 (.output 70)
    root7Node144Leaf_checked f h2
theorem root7Node143_cover : Covers root7Node143Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node143Domains0 root7Node143Domains1 f hf root7Node143Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node143Domains1 (.output 69)
    root7Node143Leaf_checked f h1
theorem root7Node142_cover : Covers root7Node142Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node142Domains0 root7Node142Domains1 f hf root7Node142Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node142Domains1 (.output 68)
    root7Node142Leaf_checked f h1
theorem root7Node141_cover : Covers root7Node141Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root7Node141Domains0 root7Node141Domains1 f hf root7Node141Step1_checked
  have hb : Covers root7Node141Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node141Domains1 root7Outputs 60
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node142_cover
    · exact root7Node143_cover
  exact hb f h1
theorem root7Node140_cover : Covers root7Node140Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node140Domains0 root7Node140Domains1 f hf root7Node140Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node140Domains1 root7Node140Domains2 f h1 root7Node140Step2_checked
  have hb : Covers root7Node140Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node140Domains2 root7Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node141_cover
    · exact root7Node144_cover
  exact hb f h2
theorem root7Node139_cover : Covers root7Node139Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root7Node139Domains0 root7Node139Domains1 f hf root7Node139Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node139Domains1 root7Node139Domains2 f h1 root7Node139Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node139Domains2 (.output 67)
    root7Node139Leaf_checked f h2
theorem root7Node138_cover : Covers root7Node138Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table55 table55_member
    root7Node138Domains0 root7Node138Domains1 f hf root7Node138Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node138Domains1 root7Node138Domains2 f h1 root7Node138Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node138Domains2 (.output 66)
    root7Node138Leaf_checked f h2
theorem root7Node137_cover : Covers root7Node137Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root7Node137Domains0 root7Node137Domains1 f hf root7Node137Step1_checked
  have hb : Covers root7Node137Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node137Domains1 root7Outputs 41
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node138_cover
    · exact root7Node139_cover
  exact hb f h1
theorem root7Node136_cover : Covers root7Node136Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node136Domains0 root7Node136Domains1 f hf root7Node136Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node136Domains1 root7Node136Domains2 f h1 root7Node136Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node136Domains2 (.output 65)
    root7Node136Leaf_checked f h2
theorem root7Node135_cover : Covers root7Node135Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node135Domains0 root7Node135Domains1 f hf root7Node135Step1_checked
  have hb : Covers root7Node135Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node135Domains1 root7Outputs 30
    intro s hs
    change s ∈ [(7,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node136_cover
    · exact root7Node137_cover
  exact hb f h1
theorem root7Node134_cover : Covers root7Node134Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table26 table26_member
    root7Node134Domains0 root7Node134Domains1 f hf root7Node134Step1_checked
  have hb : Covers root7Node134Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node134Domains1 root7Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node135_cover
    · exact root7Node140_cover
  exact hb f h1
theorem root7Node133_cover : Covers root7Node133Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node133Domains0 root7Node133Domains1 f hf root7Node133Step1_checked
  have h2 := solution_checkReplacement constraints table30 table30_member
    root7Node133Domains1 root7Node133Domains2 f h1 root7Node133Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node133Domains2 (.output 64)
    root7Node133Leaf_checked f h2
theorem root7Node132_cover : Covers root7Node132Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table1 table1_member
    root7Node132Domains0 root7Node132Domains1 f hf root7Node132Step1_checked
  have hb : Covers root7Node132Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node132Domains1 root7Outputs 20
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node133_cover
    · exact root7Node134_cover
  exact hb f h1
theorem root7Node131_cover : Covers root7Node131Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table32 table32_member
    root7Node131Domains0 root7Node131Domains1 f hf root7Node131Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root7Node131Domains1 root7Node131Domains2 f h1 root7Node131Step2_checked
  have hb : Covers root7Node131Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node131Domains2 root7Outputs 2
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node132_cover
    · exact root7Node145_cover
  exact hb f h2
theorem root7Node130_cover : Covers root7Node130Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table21 table21_member
    root7Node130Domains0 root7Node130Domains1 f hf root7Node130Step1_checked
  have hb : Covers root7Node130Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node130Domains1 root7Outputs 1
    intro s hs
    change s ∈ [(0,0),(6,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node131_cover
    · exact root7Node152_cover
  exact hb f h1
theorem root7Node129_cover : Covers root7Node129Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table25 table25_member
    root7Node129Domains0 root7Node129Domains1 f hf root7Node129Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node129Domains1 root7Node129Domains2 f h1 root7Node129Step2_checked
  have h3 := solution_checkReplacement constraints table6 table6_member
    root7Node129Domains2 root7Node129Domains3 f h2 root7Node129Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root7Node129Domains3 root7Node129Domains4 f h3 root7Node129Step4_checked
  have hb : Covers root7Node129Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node129Domains4 root7Outputs 0
    intro s hs
    change s ∈ [(4,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node130_cover
    · exact root7Node171_cover
  exact hb f h4
theorem root7Node128_cover : Covers root7Node128Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node128Domains0 root7Node128Domains1 f hf root7Node128Step1_checked
  have h2 := solution_checkReplacement constraints table25 table25_member
    root7Node128Domains1 root7Node128Domains2 f h1 root7Node128Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root7Node128Domains2 root7Node128Domains3 f h2 root7Node128Step3_checked
  have h4 := solution_checkReplacement constraints table12 table12_member
    root7Node128Domains3 root7Node128Domains4 f h3 root7Node128Step4_checked
  have hb : Covers root7Node128Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node128Domains4 root7Outputs 3
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node129_cover
    · exact root7Node178_cover
  exact hb f h4
theorem root7Node127_cover : Covers root7Node127Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node127Domains0 root7Node127Domains1 f hf root7Node127Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node127Domains1 (.output 63)
    root7Node127Leaf_checked f h1
theorem root7Node126_cover : Covers root7Node126Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node126Domains0 root7Node126Domains1 f hf root7Node126Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node126Domains1 (.output 62)
    root7Node126Leaf_checked f h1
theorem root7Node125_cover : Covers root7Node125Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node125Domains0 root7Node125Domains1 f hf root7Node125Step1_checked
  have hb : Covers root7Node125Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node125Domains1 root7Outputs 84
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node126_cover
    · exact root7Node127_cover
  exact hb f h1
theorem root7Node124_cover : Covers root7Node124Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node124Domains0 root7Node124Domains1 f hf root7Node124Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node124Domains1 (.output 61)
    root7Node124Leaf_checked f h1
theorem root7Node123_cover : Covers root7Node123Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node123Domains0 root7Node123Domains1 f hf root7Node123Step1_checked
  have hb : Covers root7Node123Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node123Domains1 root7Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node124_cover
    · exact root7Node125_cover
  exact hb f h1
theorem root7Node122_cover : Covers root7Node122Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node122Domains0 root7Node122Domains1 f hf root7Node122Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root7Node122Domains1 root7Node122Domains2 f h1 root7Node122Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node122Domains2 (.output 60)
    root7Node122Leaf_checked f h2
theorem root7Node121_cover : Covers root7Node121Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node121Domains0 root7Node121Domains1 f hf root7Node121Step1_checked
  have hb : Covers root7Node121Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node121Domains1 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node122_cover
    · exact root7Node123_cover
  exact hb f h1
theorem root7Node120_cover : Covers root7Node120Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node120Domains0 root7Node120Domains1 f hf root7Node120Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node120Domains1 (.output 59)
    root7Node120Leaf_checked f h1
theorem root7Node119_cover : Covers root7Node119Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node119Domains0 root7Node119Domains1 f hf root7Node119Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node119Domains1 (.output 58)
    root7Node119Leaf_checked f h1
theorem root7Node118_cover : Covers root7Node118Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node118Domains0 root7Node118Domains1 f hf root7Node118Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node118Domains1 root7Node118Domains2 f h1 root7Node118Step2_checked
  have hb : Covers root7Node118Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node118Domains2 root7Outputs 84
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node119_cover
    · exact root7Node120_cover
  exact hb f h2
theorem root7Node117_cover : Covers root7Node117Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node117Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node117Domains0 root7Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node118_cover
    · exact root7Node121_cover
  exact hb f hf
theorem root7Node116_cover : Covers root7Node116Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node116Domains0 root7Node116Domains1 f hf root7Node116Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root7Node116Domains1 root7Node116Domains2 f h1 root7Node116Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node116Domains2 (.output 57)
    root7Node116Leaf_checked f h2
theorem root7Node115_cover : Covers root7Node115Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node115Domains0 root7Node115Domains1 f hf root7Node115Step1_checked
  have hb : Covers root7Node115Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node115Domains1 root7Outputs 20
    intro s hs
    change s ∈ [(5,1),(8,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node116_cover
    · exact root7Node117_cover
  exact hb f h1
theorem root7Node114_cover : Covers root7Node114Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node114Domains0 root7Node114Domains1 f hf root7Node114Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node114Domains1 (.output 56)
    root7Node114Leaf_checked f h1
theorem root7Node113_cover : Covers root7Node113Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node113Domains0 root7Node113Domains1 f hf root7Node113Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node113Domains1 (.output 55)
    root7Node113Leaf_checked f h1
theorem root7Node112_cover : Covers root7Node112Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node112Domains0 root7Node112Domains1 f hf root7Node112Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root7Node112Domains1 root7Node112Domains2 f h1 root7Node112Step2_checked
  have h3 := solution_checkReplacement constraints table12 table12_member
    root7Node112Domains2 root7Node112Domains3 f h2 root7Node112Step3_checked
  have hb : Covers root7Node112Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node112Domains3 root7Outputs 60
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node113_cover
    · exact root7Node114_cover
  exact hb f h3
theorem root7Node111_cover : Covers root7Node111Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node111Domains0 root7Node111Domains1 f hf root7Node111Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node111Domains1 root7Node111Domains2 f h1 root7Node111Step2_checked
  have h3 := solution_checkReplacement constraints table65 table65_member
    root7Node111Domains2 root7Node111Domains3 f h2 root7Node111Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root7Node111Domains3 root7Node111Domains4 f h3 root7Node111Step4_checked
  have hb : Covers root7Node111Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node111Domains4 root7Outputs 28
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node112_cover
    · exact root7Node115_cover
  exact hb f h4
theorem root7Node110_cover : Covers root7Node110Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node110Domains0 root7Node110Domains1 f hf root7Node110Step1_checked
  have h2 := solution_checkReplacement constraints table31 table31_member
    root7Node110Domains1 root7Node110Domains2 f h1 root7Node110Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root7Node110Domains2 root7Node110Domains3 f h2 root7Node110Step3_checked
  have hb : Covers root7Node110Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node110Domains3 root7Outputs 24
    intro s hs
    change s ∈ [(2,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node111_cover
    · exact root7Node128_cover
  exact hb f h3
theorem root7Node109_cover : Covers root7Node109Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node109Domains0 root7Node109Domains1 f hf root7Node109Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root7Node109Domains1 root7Node109Domains2 f h1 root7Node109Step2_checked
  have h3 := solution_checkReplacement constraints table19 table19_member
    root7Node109Domains2 root7Node109Domains3 f h2 root7Node109Step3_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node109Domains3 (.output 54)
    root7Node109Leaf_checked f h3
theorem root7Node108_cover : Covers root7Node108Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node108Domains0 root7Node108Domains1 f hf root7Node108Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node108Domains1 (.output 53)
    root7Node108Leaf_checked f h1
theorem root7Node107_cover : Covers root7Node107Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node107Domains0 root7Node107Domains1 f hf root7Node107Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node107Domains1 (.output 52)
    root7Node107Leaf_checked f h1
theorem root7Node106_cover : Covers root7Node106Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node106Domains0 root7Node106Domains1 f hf root7Node106Step1_checked
  have hb : Covers root7Node106Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node106Domains1 root7Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node107_cover
    · exact root7Node108_cover
  exact hb f h1
theorem root7Node105_cover : Covers root7Node105Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node105Domains0 root7Node105Domains1 f hf root7Node105Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root7Node105Domains1 root7Node105Domains2 f h1 root7Node105Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node105Domains2 (.output 51)
    root7Node105Leaf_checked f h2
theorem root7Node104_cover : Covers root7Node104Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node104Domains0 root7Node104Domains1 f hf root7Node104Step1_checked
  have hb : Covers root7Node104Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node104Domains1 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node105_cover
    · exact root7Node106_cover
  exact hb f h1
theorem root7Node103_cover : Covers root7Node103Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node103Domains0 root7Node103Domains1 f hf root7Node103Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node103Domains1 root7Node103Domains2 f h1 root7Node103Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node103Domains2 (.output 50)
    root7Node103Leaf_checked f h2
theorem root7Node102_cover : Covers root7Node102Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node102Domains0 root7Node102Domains1 f hf root7Node102Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node102Domains1 root7Node102Domains2 f h1 root7Node102Step2_checked
  have hb : Covers root7Node102Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node102Domains2 root7Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node103_cover
    · exact root7Node104_cover
  exact hb f h2
theorem root7Node101_cover : Covers root7Node101Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node101Domains0 root7Node101Domains1 f hf root7Node101Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node101Domains1 root7Node101Domains2 f h1 root7Node101Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node101Domains2 (.output 49)
    root7Node101Leaf_checked f h2
theorem root7Node100_cover : Covers root7Node100Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root7Node100Domains0 root7Node100Domains1 f hf root7Node100Step1_checked
  have hb : Covers root7Node100Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node100Domains1 root7Outputs 21
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node101_cover
    · exact root7Node102_cover
  exact hb f h1
theorem root7Node99_cover : Covers root7Node99Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root7Node99Domains0 root7Node99Domains1 f hf root7Node99Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node99Domains1 root7Node99Domains2 f h1 root7Node99Step2_checked
  have hb : Covers root7Node99Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node99Domains2 root7Outputs 6
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node100_cover
    · exact root7Node109_cover
  exact hb f h2
theorem root7Node98_cover : Covers root7Node98Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node98Domains0 root7Node98Domains1 f hf root7Node98Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node98Domains1 (.output 48)
    root7Node98Leaf_checked f h1
theorem root7Node97_cover : Covers root7Node97Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node97Domains0 root7Node97Domains1 f hf root7Node97Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node97Domains1 (.output 47)
    root7Node97Leaf_checked f h1
theorem root7Node96_cover : Covers root7Node96Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node96Domains0 root7Node96Domains1 f hf root7Node96Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root7Node96Domains1 root7Node96Domains2 f h1 root7Node96Step2_checked
  have h3 := solution_checkReplacement constraints table19 table19_member
    root7Node96Domains2 root7Node96Domains3 f h2 root7Node96Step3_checked
  have hb : Covers root7Node96Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node96Domains3 root7Outputs 84
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node97_cover
    · exact root7Node98_cover
  exact hb f h3
theorem root7Node95_cover : Covers root7Node95Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node95Domains0 root7Node95Domains1 f hf root7Node95Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node95Domains1 (.output 46)
    root7Node95Leaf_checked f h1
theorem root7Node94_cover : Covers root7Node94Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node94Domains0 root7Node94Domains1 f hf root7Node94Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node94Domains1 (.output 45)
    root7Node94Leaf_checked f h1
theorem root7Node93_cover : Covers root7Node93Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node93Domains0 root7Node93Domains1 f hf root7Node93Step1_checked
  have hb : Covers root7Node93Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node93Domains1 root7Outputs 84
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node94_cover
    · exact root7Node95_cover
  exact hb f h1
theorem root7Node92_cover : Covers root7Node92Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node92Domains0 root7Node92Domains1 f hf root7Node92Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node92Domains1 (.output 44)
    root7Node92Leaf_checked f h1
theorem root7Node91_cover : Covers root7Node91Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node91Domains0 root7Node91Domains1 f hf root7Node91Step1_checked
  have hb : Covers root7Node91Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node91Domains1 root7Outputs 71
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node92_cover
    · exact root7Node93_cover
  exact hb f h1
theorem root7Node90_cover : Covers root7Node90Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node90Domains0 root7Node90Domains1 f hf root7Node90Step1_checked
  have h2 := solution_checkReplacement constraints table52 table52_member
    root7Node90Domains1 root7Node90Domains2 f h1 root7Node90Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node90Domains2 (.output 43)
    root7Node90Leaf_checked f h2
theorem root7Node89_cover : Covers root7Node89Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node89Domains0 root7Node89Domains1 f hf root7Node89Step1_checked
  have hb : Covers root7Node89Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node89Domains1 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node90_cover
    · exact root7Node91_cover
  exact hb f h1
theorem root7Node88_cover : Covers root7Node88Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node88Domains0 root7Node88Domains1 f hf root7Node88Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node88Domains1 (.output 42)
    root7Node88Leaf_checked f h1
theorem root7Node87_cover : Covers root7Node87Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node87Domains0 root7Node87Domains1 f hf root7Node87Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node87Domains1 (.output 41)
    root7Node87Leaf_checked f h1
theorem root7Node86_cover : Covers root7Node86Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node86Domains0 root7Node86Domains1 f hf root7Node86Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node86Domains1 root7Node86Domains2 f h1 root7Node86Step2_checked
  have hb : Covers root7Node86Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node86Domains2 root7Outputs 84
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node87_cover
    · exact root7Node88_cover
  exact hb f h2
theorem root7Node85_cover : Covers root7Node85Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node85Domains0 root7Node85Domains1 f hf root7Node85Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node85Domains1 root7Node85Domains2 f h1 root7Node85Step2_checked
  have hb : Covers root7Node85Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node85Domains2 root7Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node86_cover
    · exact root7Node89_cover
  exact hb f h2
theorem root7Node84_cover : Covers root7Node84Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node84Domains0 root7Node84Domains1 f hf root7Node84Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node84Domains1 root7Node84Domains2 f h1 root7Node84Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node84Domains2 (.output 40)
    root7Node84Leaf_checked f h2
theorem root7Node83_cover : Covers root7Node83Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root7Node83Domains0 root7Node83Domains1 f hf root7Node83Step1_checked
  have hb : Covers root7Node83Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node83Domains1 root7Outputs 21
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node84_cover
    · exact root7Node85_cover
  exact hb f h1
theorem root7Node82_cover : Covers root7Node82Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table4 table4_member
    root7Node82Domains0 root7Node82Domains1 f hf root7Node82Step1_checked
  have hb : Covers root7Node82Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node82Domains1 root7Outputs 6
    intro s hs
    change s ∈ [(1,1),(6,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node83_cover
    · exact root7Node96_cover
  exact hb f h1
theorem root7Node81_cover : Covers root7Node81Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node81Domains0 root7Node81Domains1 f hf root7Node81Step1_checked
  have h2 := solution_checkReplacement constraints table65 table65_member
    root7Node81Domains1 root7Node81Domains2 f h1 root7Node81Step2_checked
  have h3 := solution_checkReplacement constraints table19 table19_member
    root7Node81Domains2 root7Node81Domains3 f h2 root7Node81Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root7Node81Domains3 root7Node81Domains4 f h3 root7Node81Step4_checked
  have hb : Covers root7Node81Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node81Domains4 root7Outputs 1
    intro s hs
    change s ∈ [(4,0),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node82_cover
    · exact root7Node99_cover
  exact hb f h4
theorem root7Node80_cover : Covers root7Node80Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node80Domains0 root7Node80Domains1 f hf root7Node80Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node80Domains1 (.output 39)
    root7Node80Leaf_checked f h1
theorem root7Node79_cover : Covers root7Node79Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node79Domains0 root7Node79Domains1 f hf root7Node79Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node79Domains1 (.output 38)
    root7Node79Leaf_checked f h1
theorem root7Node78_cover : Covers root7Node78Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node78Domains0 root7Node78Domains1 f hf root7Node78Step1_checked
  have hb : Covers root7Node78Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node78Domains1 root7Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node79_cover
    · exact root7Node80_cover
  exact hb f h1
theorem root7Node77_cover : Covers root7Node77Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node77Domains0 root7Node77Domains1 f hf root7Node77Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node77Domains1 (.output 37)
    root7Node77Leaf_checked f h1
theorem root7Node76_cover : Covers root7Node76Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node76Domains0 root7Node76Domains1 f hf root7Node76Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node76Domains1 (.output 36)
    root7Node76Leaf_checked f h1
theorem root7Node75_cover : Covers root7Node75Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node75Domains0 root7Node75Domains1 f hf root7Node75Step1_checked
  have hb : Covers root7Node75Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node75Domains1 root7Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node76_cover
    · exact root7Node77_cover
  exact hb f h1
theorem root7Node74_cover : Covers root7Node74Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node74Domains0 root7Node74Domains1 f hf root7Node74Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node74Domains1 root7Node74Domains2 f h1 root7Node74Step2_checked
  have hb : Covers root7Node74Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node74Domains2 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node75_cover
    · exact root7Node78_cover
  exact hb f h2
theorem root7Node73_cover : Covers root7Node73Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node73Domains0 root7Node73Domains1 f hf root7Node73Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node73Domains1 root7Node73Domains2 f h1 root7Node73Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node73Domains2 (.output 35)
    root7Node73Leaf_checked f h2
theorem root7Node72_cover : Covers root7Node72Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node72Domains0 root7Node72Domains1 f hf root7Node72Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node72Domains1 root7Node72Domains2 f h1 root7Node72Step2_checked
  have hb : Covers root7Node72Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node72Domains2 root7Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node73_cover
    · exact root7Node74_cover
  exact hb f h2
theorem root7Node71_cover : Covers root7Node71Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node71Domains0 root7Node71Domains1 f hf root7Node71Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root7Node71Domains1 root7Node71Domains2 f h1 root7Node71Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node71Domains2 (.output 34)
    root7Node71Leaf_checked f h2
theorem root7Node70_cover : Covers root7Node70Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node70Domains0 root7Node70Domains1 f hf root7Node70Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root7Node70Domains1 root7Node70Domains2 f h1 root7Node70Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node70Domains2 (.output 33)
    root7Node70Leaf_checked f h2
theorem root7Node69_cover : Covers root7Node69Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node69Domains0 root7Node69Domains1 f hf root7Node69Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node69Domains1 root7Node69Domains2 f h1 root7Node69Step2_checked
  have hb : Covers root7Node69Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node69Domains2 root7Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node70_cover
    · exact root7Node71_cover
  exact hb f h2
theorem root7Node68_cover : Covers root7Node68Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root7Node68Domains0 root7Node68Domains1 f hf root7Node68Step1_checked
  have hb : Covers root7Node68Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node68Domains1 root7Outputs 21
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node69_cover
    · exact root7Node72_cover
  exact hb f h1
theorem root7Node67_cover : Covers root7Node67Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node67Domains0 (.output 32)
    root7Node67Leaf_checked f hf
theorem root7Node66_cover : Covers root7Node66Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node66Domains0 (.output 31)
    root7Node66Leaf_checked f hf
theorem root7Node65_cover : Covers root7Node65Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node65Domains0 root7Node65Domains1 f hf root7Node65Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node65Domains1 root7Node65Domains2 f h1 root7Node65Step2_checked
  have hb : Covers root7Node65Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node65Domains2 root7Outputs 30
    intro s hs
    change s ∈ [(5,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node66_cover
    · exact root7Node67_cover
  exact hb f h2
theorem root7Node64_cover : Covers root7Node64Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node64Domains0 root7Node64Domains1 f hf root7Node64Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node64Domains1 root7Node64Domains2 f h1 root7Node64Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root7Node64Domains2 root7Node64Domains3 f h2 root7Node64Step3_checked
  have hb : Covers root7Node64Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node64Domains3 root7Outputs 13
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node65_cover
    · exact root7Node68_cover
  exact hb f h3
theorem root7Node63_cover : Covers root7Node63Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node63Domains0 root7Node63Domains1 f hf root7Node63Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node63Domains1 root7Node63Domains2 f h1 root7Node63Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node63Domains2 (.output 30)
    root7Node63Leaf_checked f h2
theorem root7Node62_cover : Covers root7Node62Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node62Domains0 (.output 29)
    root7Node62Leaf_checked f hf
theorem root7Node61_cover : Covers root7Node61Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node61Domains0 (.output 28)
    root7Node61Leaf_checked f hf
theorem root7Node60_cover : Covers root7Node60Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node60Domains0 root7Node60Domains1 f hf root7Node60Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node60Domains1 root7Node60Domains2 f h1 root7Node60Step2_checked
  have hb : Covers root7Node60Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node60Domains2 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node61_cover
    · exact root7Node62_cover
  exact hb f h2
theorem root7Node59_cover : Covers root7Node59Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root7Node59Domains0 root7Node59Domains1 f hf root7Node59Step1_checked
  have hb : Covers root7Node59Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node59Domains1 root7Outputs 44
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node60_cover
    · exact root7Node63_cover
  exact hb f h1
theorem root7Node58_cover : Covers root7Node58Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node58Domains0 root7Node58Domains1 f hf root7Node58Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node58Domains1 root7Node58Domains2 f h1 root7Node58Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node58Domains2 (.output 27)
    root7Node58Leaf_checked f h2
theorem root7Node57_cover : Covers root7Node57Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node57Domains0 root7Node57Domains1 f hf root7Node57Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node57Domains1 root7Node57Domains2 f h1 root7Node57Step2_checked
  have hb : Covers root7Node57Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node57Domains2 root7Outputs 13
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node58_cover
    · exact root7Node59_cover
  exact hb f h2
theorem root7Node56_cover : Covers root7Node56Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node56Domains0 root7Node56Domains1 f hf root7Node56Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node56Domains1 (.output 26)
    root7Node56Leaf_checked f h1
theorem root7Node55_cover : Covers root7Node55Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node55Domains0 root7Node55Domains1 f hf root7Node55Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node55Domains1 (.output 25)
    root7Node55Leaf_checked f h1
theorem root7Node54_cover : Covers root7Node54Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node54Domains0 root7Node54Domains1 f hf root7Node54Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node54Domains1 root7Node54Domains2 f h1 root7Node54Step2_checked
  have hb : Covers root7Node54Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node54Domains2 root7Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node55_cover
    · exact root7Node56_cover
  exact hb f h2
theorem root7Node53_cover : Covers root7Node53Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node53Domains0 (.output 24)
    root7Node53Leaf_checked f hf
theorem root7Node52_cover : Covers root7Node52Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node52Domains0 (.output 23)
    root7Node52Leaf_checked f hf
theorem root7Node51_cover : Covers root7Node51Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node51Domains0 root7Node51Domains1 f hf root7Node51Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node51Domains1 root7Node51Domains2 f h1 root7Node51Step2_checked
  have hb : Covers root7Node51Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node51Domains2 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node52_cover
    · exact root7Node53_cover
  exact hb f h2
theorem root7Node50_cover : Covers root7Node50Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root7Node50Domains0 root7Node50Domains1 f hf root7Node50Step1_checked
  have hb : Covers root7Node50Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node50Domains1 root7Outputs 44
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node51_cover
    · exact root7Node54_cover
  exact hb f h1
theorem root7Node49_cover : Covers root7Node49Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node49Domains0 root7Node49Domains1 f hf root7Node49Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node49Domains1 (.output 22)
    root7Node49Leaf_checked f h1
theorem root7Node48_cover : Covers root7Node48Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node48Domains0 root7Node48Domains1 f hf root7Node48Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node48Domains1 (.output 21)
    root7Node48Leaf_checked f h1
theorem root7Node47_cover : Covers root7Node47Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node47Domains0 root7Node47Domains1 f hf root7Node47Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node47Domains1 root7Node47Domains2 f h1 root7Node47Step2_checked
  have hb : Covers root7Node47Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node47Domains2 root7Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node48_cover
    · exact root7Node49_cover
  exact hb f h2
theorem root7Node46_cover : Covers root7Node46Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node46Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node46Domains0 root7Outputs 13
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node47_cover
    · exact root7Node50_cover
  exact hb f hf
theorem root7Node45_cover : Covers root7Node45Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root7Node45Domains0 root7Node45Domains1 f hf root7Node45Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node45Domains1 root7Node45Domains2 f h1 root7Node45Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root7Node45Domains2 root7Node45Domains3 f h2 root7Node45Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root7Node45Domains3 root7Node45Domains4 f h3 root7Node45Step4_checked
  have hb : Covers root7Node45Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node45Domains4 root7Outputs 5
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node46_cover
    · exact root7Node57_cover
  exact hb f h4
theorem root7Node44_cover : Covers root7Node44Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node44Domains0 root7Node44Domains1 f hf root7Node44Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node44Domains1 root7Node44Domains2 f h1 root7Node44Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node44Domains2 (.output 20)
    root7Node44Leaf_checked f h2
theorem root7Node43_cover : Covers root7Node43Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node43Domains0 root7Node43Domains1 f hf root7Node43Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node43Domains1 (.output 19)
    root7Node43Leaf_checked f h1
theorem root7Node42_cover : Covers root7Node42Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node42Domains0 root7Node42Domains1 f hf root7Node42Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node42Domains1 (.output 18)
    root7Node42Leaf_checked f h1
theorem root7Node41_cover : Covers root7Node41Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node41Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node41Domains0 root7Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node42_cover
    · exact root7Node43_cover
  exact hb f hf
theorem root7Node40_cover : Covers root7Node40Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root7Node40Domains0 root7Node40Domains1 f hf root7Node40Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node40Domains1 root7Node40Domains2 f h1 root7Node40Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root7Node40Domains2 root7Node40Domains3 f h2 root7Node40Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root7Node40Domains3 root7Node40Domains4 f h3 root7Node40Step4_checked
  have hb : Covers root7Node40Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node40Domains4 root7Outputs 5
    intro s hs
    change s ∈ [(3,2),(7,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node41_cover
    · exact root7Node44_cover
  exact hb f h4
theorem root7Node39_cover : Covers root7Node39Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node39Domains0 root7Node39Domains1 f hf root7Node39Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node39Domains1 (.output 17)
    root7Node39Leaf_checked f h1
theorem root7Node38_cover : Covers root7Node38Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node38Domains0 root7Node38Domains1 f hf root7Node38Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node38Domains1 (.output 16)
    root7Node38Leaf_checked f h1
theorem root7Node37_cover : Covers root7Node37Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node37Domains0 root7Node37Domains1 f hf root7Node37Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node37Domains1 root7Node37Domains2 f h1 root7Node37Step2_checked
  have h3 := solution_checkReplacement constraints table51 table51_member
    root7Node37Domains2 root7Node37Domains3 f h2 root7Node37Step3_checked
  have hb : Covers root7Node37Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node37Domains3 root7Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node38_cover
    · exact root7Node39_cover
  exact hb f h3
theorem root7Node36_cover : Covers root7Node36Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node36Domains0 root7Node36Domains1 f hf root7Node36Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node36Domains1 (.output 15)
    root7Node36Leaf_checked f h1
theorem root7Node35_cover : Covers root7Node35Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node35Domains0 root7Node35Domains1 f hf root7Node35Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node35Domains1 (.output 14)
    root7Node35Leaf_checked f h1
theorem root7Node34_cover : Covers root7Node34Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node34Domains0 root7Node34Domains1 f hf root7Node34Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node34Domains1 root7Node34Domains2 f h1 root7Node34Step2_checked
  have hb : Covers root7Node34Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node34Domains2 root7Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node35_cover
    · exact root7Node36_cover
  exact hb f h2
theorem root7Node33_cover : Covers root7Node33Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node33Domains0 (.output 13)
    root7Node33Leaf_checked f hf
theorem root7Node32_cover : Covers root7Node32Domains0 constraints root7Outputs := by
  intro f hf
  exact checkCover_sound 1 constraints root7Outputs root7Node32Domains0 (.output 12)
    root7Node32Leaf_checked f hf
theorem root7Node31_cover : Covers root7Node31Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table65 table65_member
    root7Node31Domains0 root7Node31Domains1 f hf root7Node31Step1_checked
  have h2 := solution_checkReplacement constraints table19 table19_member
    root7Node31Domains1 root7Node31Domains2 f h1 root7Node31Step2_checked
  have hb : Covers root7Node31Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node31Domains2 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(3,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node32_cover
    · exact root7Node33_cover
  exact hb f h2
theorem root7Node30_cover : Covers root7Node30Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node30Domains0 root7Node30Domains1 f hf root7Node30Step1_checked
  have hb : Covers root7Node30Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node30Domains1 root7Outputs 44
    intro s hs
    change s ∈ [(5,5),(8,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node31_cover
    · exact root7Node34_cover
  exact hb f h1
theorem root7Node29_cover : Covers root7Node29Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node29Domains0 root7Node29Domains1 f hf root7Node29Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node29Domains1 (.output 11)
    root7Node29Leaf_checked f h1
theorem root7Node28_cover : Covers root7Node28Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node28Domains0 root7Node28Domains1 f hf root7Node28Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node28Domains1 (.output 10)
    root7Node28Leaf_checked f h1
theorem root7Node27_cover : Covers root7Node27Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node27Domains0 root7Node27Domains1 f hf root7Node27Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root7Node27Domains1 root7Node27Domains2 f h1 root7Node27Step2_checked
  have hb : Covers root7Node27Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node27Domains2 root7Outputs 39
    intro s hs
    change s ∈ [(1,4),(3,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node28_cover
    · exact root7Node29_cover
  exact hb f h2
theorem root7Node26_cover : Covers root7Node26Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table30 table30_member
    root7Node26Domains0 root7Node26Domains1 f hf root7Node26Step1_checked
  have hb : Covers root7Node26Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node26Domains1 root7Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node27_cover
    · exact root7Node30_cover
  exact hb f h1
theorem root7Node25_cover : Covers root7Node25Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root7Node25Domains0 root7Node25Domains1 f hf root7Node25Step1_checked
  have hb : Covers root7Node25Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node25Domains1 root7Outputs 21
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node26_cover
    · exact root7Node37_cover
  exact hb f h1
theorem root7Node24_cover : Covers root7Node24Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node24Domains0 root7Node24Domains1 f hf root7Node24Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node24Domains1 (.output 9)
    root7Node24Leaf_checked f h1
theorem root7Node23_cover : Covers root7Node23Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table56 table56_member
    root7Node23Domains0 root7Node23Domains1 f hf root7Node23Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node23Domains1 (.output 8)
    root7Node23Leaf_checked f h1
theorem root7Node22_cover : Covers root7Node22Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node22Domains0 root7Node22Domains1 f hf root7Node22Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node22Domains1 root7Node22Domains2 f h1 root7Node22Step2_checked
  have hb : Covers root7Node22Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node22Domains2 root7Outputs 60
    intro s hs
    change s ∈ [(1,3),(6,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node23_cover
    · exact root7Node24_cover
  exact hb f h2
theorem root7Node21_cover : Covers root7Node21Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table3 table3_member
    root7Node21Domains0 root7Node21Domains1 f hf root7Node21Step1_checked
  have hb : Covers root7Node21Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node21Domains1 root7Outputs 13
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node22_cover
    · exact root7Node25_cover
  exact hb f h1
theorem root7Node20_cover : Covers root7Node20Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table46 table46_member
    root7Node20Domains0 root7Node20Domains1 f hf root7Node20Step1_checked
  have h2 := solution_checkReplacement constraints table53 table53_member
    root7Node20Domains1 root7Node20Domains2 f h1 root7Node20Step2_checked
  have h3 := solution_checkReplacement constraints table0 table0_member
    root7Node20Domains2 root7Node20Domains3 f h2 root7Node20Step3_checked
  have hb : Covers root7Node20Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node20Domains3 root7Outputs 3
    intro s hs
    change s ∈ [(2,4),(4,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node21_cover
    · exact root7Node40_cover
  exact hb f h3
theorem root7Node19_cover : Covers root7Node19Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node19Domains0 root7Node19Domains1 f hf root7Node19Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node19Domains1 (.output 7)
    root7Node19Leaf_checked f h1
theorem root7Node18_cover : Covers root7Node18Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node18Domains0 root7Node18Domains1 f hf root7Node18Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node18Domains1 (.output 6)
    root7Node18Leaf_checked f h1
theorem root7Node17_cover : Covers root7Node17Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node17Domains0 root7Node17Domains1 f hf root7Node17Step1_checked
  have hb : Covers root7Node17Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node17Domains1 root7Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node18_cover
    · exact root7Node19_cover
  exact hb f h1
theorem root7Node16_cover : Covers root7Node16Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node16Domains0 root7Node16Domains1 f hf root7Node16Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node16Domains1 (.output 5)
    root7Node16Leaf_checked f h1
theorem root7Node15_cover : Covers root7Node15Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table51 table51_member
    root7Node15Domains0 root7Node15Domains1 f hf root7Node15Step1_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node15Domains1 (.output 4)
    root7Node15Leaf_checked f h1
theorem root7Node14_cover : Covers root7Node14Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node14Domains0 root7Node14Domains1 f hf root7Node14Step1_checked
  have hb : Covers root7Node14Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node14Domains1 root7Outputs 70
    intro s hs
    change s ∈ [(1,3),(3,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node15_cover
    · exact root7Node16_cover
  exact hb f h1
theorem root7Node13_cover : Covers root7Node13Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node13Domains0 root7Node13Domains1 f hf root7Node13Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node13Domains1 root7Node13Domains2 f h1 root7Node13Step2_checked
  have hb : Covers root7Node13Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node13Domains2 root7Outputs 50
    intro s hs
    change s ∈ [(1,5),(7,5)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node14_cover
    · exact root7Node17_cover
  exact hb f h2
theorem root7Node12_cover : Covers root7Node12Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node12Domains0 root7Node12Domains1 f hf root7Node12Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node12Domains1 root7Node12Domains2 f h1 root7Node12Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node12Domains2 (.output 3)
    root7Node12Leaf_checked f h2
theorem root7Node11_cover : Covers root7Node11Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node11Domains0 root7Node11Domains1 f hf root7Node11Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node11Domains1 root7Node11Domains2 f h1 root7Node11Step2_checked
  have hb : Covers root7Node11Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node11Domains2 root7Outputs 40
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node12_cover
    · exact root7Node13_cover
  exact hb f h2
theorem root7Node10_cover : Covers root7Node10Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node10Domains0 root7Node10Domains1 f hf root7Node10Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root7Node10Domains1 root7Node10Domains2 f h1 root7Node10Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node10Domains2 (.output 2)
    root7Node10Leaf_checked f h2
theorem root7Node9_cover : Covers root7Node9Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table57 table57_member
    root7Node9Domains0 root7Node9Domains1 f hf root7Node9Step1_checked
  have h2 := solution_checkReplacement constraints table51 table51_member
    root7Node9Domains1 root7Node9Domains2 f h1 root7Node9Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node9Domains2 (.output 1)
    root7Node9Leaf_checked f h2
theorem root7Node8_cover : Covers root7Node8Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node8Domains0 root7Node8Domains1 f hf root7Node8Step1_checked
  have h2 := solution_checkReplacement constraints table36 table36_member
    root7Node8Domains1 root7Node8Domains2 f h1 root7Node8Step2_checked
  have hb : Covers root7Node8Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node8Domains2 root7Outputs 29
    intro s hs
    change s ∈ [(4,2),(8,2)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node9_cover
    · exact root7Node10_cover
  exact hb f h2
theorem root7Node7_cover : Covers root7Node7Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table52 table52_member
    root7Node7Domains0 root7Node7Domains1 f hf root7Node7Step1_checked
  have hb : Covers root7Node7Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node7Domains1 root7Outputs 21
    intro s hs
    change s ∈ [(5,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node8_cover
    · exact root7Node11_cover
  exact hb f h1
theorem root7Node6_cover : Covers root7Node6Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table54 table54_member
    root7Node6Domains0 root7Node6Domains1 f hf root7Node6Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node6Domains1 root7Node6Domains2 f h1 root7Node6Step2_checked
  exact checkCover_sound 1 constraints root7Outputs root7Node6Domains2 (.output 0)
    root7Node6Leaf_checked f h2
theorem root7Node5_cover : Covers root7Node5Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table36 table36_member
    root7Node5Domains0 root7Node5Domains1 f hf root7Node5Step1_checked
  have h2 := solution_checkReplacement constraints table56 table56_member
    root7Node5Domains1 root7Node5Domains2 f h1 root7Node5Step2_checked
  have hb : Covers root7Node5Domains2 constraints root7Outputs := by
    apply covers_of_branches root7Node5Domains2 root7Outputs 13
    intro s hs
    change s ∈ [(4,0),(8,0)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node6_cover
    · exact root7Node7_cover
  exact hb f h2
theorem root7Node4_cover : Covers root7Node4Domains0 constraints root7Outputs := by
  intro f hf
  have hb : Covers root7Node4Domains0 constraints root7Outputs := by
    apply covers_of_branches root7Node4Domains0 root7Outputs 9
    intro s hs
    change s ∈ [(3,1),(7,1)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node5_cover
    · exact root7Node20_cover
  exact hb f hf
theorem root7Node3_cover : Covers root7Node3Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table0 table0_member
    root7Node3Domains0 root7Node3Domains1 f hf root7Node3Step1_checked
  have hb : Covers root7Node3Domains1 constraints root7Outputs := by
    apply covers_of_branches root7Node3Domains1 root7Outputs 0
    intro s hs
    change s ∈ [(4,4),(8,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node4_cover
    · exact root7Node45_cover
  exact hb f h1
theorem root7Node2_cover : Covers root7Node2Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table44 table44_member
    root7Node2Domains0 root7Node2Domains1 f hf root7Node2Step1_checked
  have h2 := solution_checkReplacement constraints table4 table4_member
    root7Node2Domains1 root7Node2Domains2 f h1 root7Node2Step2_checked
  have h3 := solution_checkReplacement constraints table65 table65_member
    root7Node2Domains2 root7Node2Domains3 f h2 root7Node2Step3_checked
  have hb : Covers root7Node2Domains3 constraints root7Outputs := by
    apply covers_of_branches root7Node2Domains3 root7Outputs 1
    intro s hs
    change s ∈ [(1,4),(7,4)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node3_cover
    · exact root7Node64_cover
  exact hb f h3
theorem root7Node1_cover : Covers root7Node1Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table35 table35_member
    root7Node1Domains0 root7Node1Domains1 f hf root7Node1Step1_checked
  have h2 := solution_checkReplacement constraints table54 table54_member
    root7Node1Domains1 root7Node1Domains2 f h1 root7Node1Step2_checked
  have h3 := solution_checkReplacement constraints table57 table57_member
    root7Node1Domains2 root7Node1Domains3 f h2 root7Node1Step3_checked
  have h4 := solution_checkReplacement constraints table0 table0_member
    root7Node1Domains3 root7Node1Domains4 f h3 root7Node1Step4_checked
  have hb : Covers root7Node1Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node1Domains4 root7Outputs 14
    intro s hs
    change s ∈ [(7,3),(8,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node2_cover
    · exact root7Node81_cover
  exact hb f h4
theorem root7Node0_cover : Covers root7Node0Domains0 constraints root7Outputs := by
  intro f hf
  have h1 := solution_checkReplacement constraints table34 table34_member
    root7Node0Domains0 root7Node0Domains1 f hf root7Node0Step1_checked
  have h2 := solution_checkReplacement constraints table57 table57_member
    root7Node0Domains1 root7Node0Domains2 f h1 root7Node0Step2_checked
  have h3 := solution_checkReplacement constraints table52 table52_member
    root7Node0Domains2 root7Node0Domains3 f h2 root7Node0Step3_checked
  have h4 := solution_checkReplacement constraints table2 table2_member
    root7Node0Domains3 root7Node0Domains4 f h3 root7Node0Step4_checked
  have hb : Covers root7Node0Domains4 constraints root7Outputs := by
    apply covers_of_branches root7Node0Domains4 root7Outputs 25
    intro s hs
    change s ∈ [(0,0),(1,3)] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact root7Node1_cover
    · exact root7Node110_cover
  exact hb f h4
theorem root7_table_cover : Covers (domains (7,0)) constraints root7Outputs := root7Node0_cover
theorem root7Family_count : root7Family.length = 106 := rfl
#print axioms root7_table_cover
end SpectreFinite.HexSearch.RadiusFive
