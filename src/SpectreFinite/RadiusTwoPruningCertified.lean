module

public import SpectreFinite.RadiusTwoPruningLiteral
public import SpectreFinite.RadiusTwoPruningBlock0T0
public import SpectreFinite.RadiusTwoPruningBlock0T1
public import SpectreFinite.RadiusTwoPruningBlock0T2
public import SpectreFinite.RadiusTwoPruningBlock0T3
public import SpectreFinite.RadiusTwoPruningBlock0T4
public import SpectreFinite.RadiusTwoPruningBlock0T5
public import SpectreFinite.RadiusTwoPruningBlock1T0
public import SpectreFinite.RadiusTwoPruningBlock1T1
public import SpectreFinite.RadiusTwoPruningBlock1T2
public import SpectreFinite.RadiusTwoPruningBlock1T3
public import SpectreFinite.RadiusTwoPruningBlock1T4
public import SpectreFinite.RadiusTwoPruningBlock1T5
public import SpectreFinite.RadiusTwoPruningBlock2T0
public import SpectreFinite.RadiusTwoPruningBlock2T1
public import SpectreFinite.RadiusTwoPruningBlock2T2
public import SpectreFinite.RadiusTwoPruningBlock2T3
public import SpectreFinite.RadiusTwoPruningBlock2T4
public import SpectreFinite.RadiusTwoPruningBlock2T5
public import SpectreFinite.RadiusTwoPruningBlock3T0
public import SpectreFinite.RadiusTwoPruningBlock3T1
public import SpectreFinite.RadiusTwoPruningBlock3T2
public import SpectreFinite.RadiusTwoPruningBlock3T3
public import SpectreFinite.RadiusTwoPruningBlock3T4
public import SpectreFinite.RadiusTwoPruningBlock3T5
public import SpectreFinite.RadiusTwoPruningBlock4T0
public import SpectreFinite.RadiusTwoPruningBlock4T1
public import SpectreFinite.RadiusTwoPruningBlock4T2
public import SpectreFinite.RadiusTwoPruningBlock4T3
public import SpectreFinite.RadiusTwoPruningBlock4T4
public import SpectreFinite.RadiusTwoPruningBlock4T5
public import SpectreFinite.RadiusTwoPruningBlock5T0
public import SpectreFinite.RadiusTwoPruningBlock5T1
public import SpectreFinite.RadiusTwoPruningBlock5T2
public import SpectreFinite.RadiusTwoPruningBlock5T3
public import SpectreFinite.RadiusTwoPruningBlock5T4
public import SpectreFinite.RadiusTwoPruningBlock5T5
public import SpectreFinite.RadiusTwoPruningBlock6T0
public import SpectreFinite.RadiusTwoPruningBlock6T1
public import SpectreFinite.RadiusTwoPruningBlock6T2
public import SpectreFinite.RadiusTwoPruningBlock6T3
public import SpectreFinite.RadiusTwoPruningBlock6T4
public import SpectreFinite.RadiusTwoPruningBlock6T5
public import SpectreFinite.RadiusTwoPruningBlock7T0
public import SpectreFinite.RadiusTwoPruningBlock7T1
public import SpectreFinite.RadiusTwoPruningBlock7T2
public import SpectreFinite.RadiusTwoPruningBlock7T3
public import SpectreFinite.RadiusTwoPruningBlock7T4
public import SpectreFinite.RadiusTwoPruningBlock7T5
public import SpectreFinite.RadiusTwoPruningBlock8T0
public import SpectreFinite.RadiusTwoPruningBlock8T1
public import SpectreFinite.RadiusTwoPruningBlock8T2
public import SpectreFinite.RadiusTwoPruningBlock8T3
public import SpectreFinite.RadiusTwoPruningBlock8T4
public import SpectreFinite.RadiusTwoPruningBlock8T5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def chunks0 : List (List (Verdict 6)) := [rows0_0_0, rows0_0_1, rows0_0_2, rows0_0_3, rows0_0_4, rows0_0_5, rows0_1_0, rows0_1_1, rows0_1_2, rows0_1_3, rows0_1_4, rows0_1_5, rows0_2_0, rows0_2_1, rows0_2_2, rows0_2_3, rows0_2_4, rows0_2_5, rows0_3_0, rows0_3_1, rows0_3_2, rows0_3_3, rows0_3_4, rows0_3_5, rows0_4_0, rows0_4_1, rows0_4_2, rows0_4_3, rows0_4_4, rows0_4_5, rows0_5_0, rows0_5_1, rows0_5_2, rows0_5_3, rows0_5_4, rows0_5_5, rows0_6_0, rows0_6_1, rows0_6_2, rows0_6_3, rows0_6_4, rows0_6_5, rows0_7_0, rows0_7_1, rows0_7_2, rows0_7_3, rows0_7_4, rows0_7_5, rows0_8_0, rows0_8_1, rows0_8_2, rows0_8_3, rows0_8_4, rows0_8_5]
def rows0 : List (Verdict 6) := chunks0.flatten
theorem checked0 : checkRows direction samples trees0 rows0 = true := by
  apply checkRows_flatten
  simp only [chunks0, List.all_cons, List.all_nil, check0_0_0, check0_0_1, check0_0_2, check0_0_3, check0_0_4, check0_0_5, check0_1_0, check0_1_1, check0_1_2, check0_1_3, check0_1_4, check0_1_5, check0_2_0, check0_2_1, check0_2_2, check0_2_3, check0_2_4, check0_2_5, check0_3_0, check0_3_1, check0_3_2, check0_3_3, check0_3_4, check0_3_5, check0_4_0, check0_4_1, check0_4_2, check0_4_3, check0_4_4, check0_4_5, check0_5_0, check0_5_1, check0_5_2, check0_5_3, check0_5_4, check0_5_5, check0_6_0, check0_6_1, check0_6_2, check0_6_3, check0_6_4, check0_6_5, check0_7_0, check0_7_1, check0_7_2, check0_7_3, check0_7_4, check0_7_5, check0_8_0, check0_8_1, check0_8_2, check0_8_3, check0_8_4, check0_8_5, Bool.true_and]
def chunks1 : List (List (Verdict 6)) := [rows1_0_0, rows1_0_1, rows1_0_2, rows1_0_3, rows1_0_4, rows1_0_5, rows1_1_0, rows1_1_1, rows1_1_2, rows1_1_3, rows1_1_4, rows1_1_5, rows1_2_0, rows1_2_1, rows1_2_2, rows1_2_3, rows1_2_4, rows1_2_5, rows1_3_0, rows1_3_1, rows1_3_2, rows1_3_3, rows1_3_4, rows1_3_5, rows1_4_0, rows1_4_1, rows1_4_2, rows1_4_3, rows1_4_4, rows1_4_5, rows1_5_0, rows1_5_1, rows1_5_2, rows1_5_3, rows1_5_4, rows1_5_5, rows1_6_0, rows1_6_1, rows1_6_2, rows1_6_3, rows1_6_4, rows1_6_5, rows1_7_0, rows1_7_1, rows1_7_2, rows1_7_3, rows1_7_4, rows1_7_5, rows1_8_0, rows1_8_1, rows1_8_2, rows1_8_3, rows1_8_4, rows1_8_5]
def rows1 : List (Verdict 6) := chunks1.flatten
theorem checked1 : checkRows direction samples trees1 rows1 = true := by
  apply checkRows_flatten
  simp only [chunks1, List.all_cons, List.all_nil, check1_0_0, check1_0_1, check1_0_2, check1_0_3, check1_0_4, check1_0_5, check1_1_0, check1_1_1, check1_1_2, check1_1_3, check1_1_4, check1_1_5, check1_2_0, check1_2_1, check1_2_2, check1_2_3, check1_2_4, check1_2_5, check1_3_0, check1_3_1, check1_3_2, check1_3_3, check1_3_4, check1_3_5, check1_4_0, check1_4_1, check1_4_2, check1_4_3, check1_4_4, check1_4_5, check1_5_0, check1_5_1, check1_5_2, check1_5_3, check1_5_4, check1_5_5, check1_6_0, check1_6_1, check1_6_2, check1_6_3, check1_6_4, check1_6_5, check1_7_0, check1_7_1, check1_7_2, check1_7_3, check1_7_4, check1_7_5, check1_8_0, check1_8_1, check1_8_2, check1_8_3, check1_8_4, check1_8_5, Bool.true_and]
theorem link1 : rows1.map Verdict.patch = rows0.filterMap Verdict.kept := by
  simp only [rows1, rows0, List.map_flatten, List.filterMap_flatten, chunks1, chunks0, List.map_cons, List.map_nil, link1_0_0, link1_0_1, link1_0_2, link1_0_3, link1_0_4, link1_0_5, link1_1_0, link1_1_1, link1_1_2, link1_1_3, link1_1_4, link1_1_5, link1_2_0, link1_2_1, link1_2_2, link1_2_3, link1_2_4, link1_2_5, link1_3_0, link1_3_1, link1_3_2, link1_3_3, link1_3_4, link1_3_5, link1_4_0, link1_4_1, link1_4_2, link1_4_3, link1_4_4, link1_4_5, link1_5_0, link1_5_1, link1_5_2, link1_5_3, link1_5_4, link1_5_5, link1_6_0, link1_6_1, link1_6_2, link1_6_3, link1_6_4, link1_6_5, link1_7_0, link1_7_1, link1_7_2, link1_7_3, link1_7_4, link1_7_5, link1_8_0, link1_8_1, link1_8_2, link1_8_3, link1_8_4, link1_8_5]
def chunks2 : List (List (Verdict 6)) := [rows2_0_0, rows2_0_1, rows2_0_2, rows2_0_3, rows2_0_4, rows2_0_5, rows2_1_0, rows2_1_1, rows2_1_2, rows2_1_3, rows2_1_4, rows2_1_5, rows2_2_0, rows2_2_1, rows2_2_2, rows2_2_3, rows2_2_4, rows2_2_5, rows2_3_0, rows2_3_1, rows2_3_2, rows2_3_3, rows2_3_4, rows2_3_5, rows2_4_0, rows2_4_1, rows2_4_2, rows2_4_3, rows2_4_4, rows2_4_5, rows2_5_0, rows2_5_1, rows2_5_2, rows2_5_3, rows2_5_4, rows2_5_5, rows2_6_0, rows2_6_1, rows2_6_2, rows2_6_3, rows2_6_4, rows2_6_5, rows2_7_0, rows2_7_1, rows2_7_2, rows2_7_3, rows2_7_4, rows2_7_5, rows2_8_0, rows2_8_1, rows2_8_2, rows2_8_3, rows2_8_4, rows2_8_5]
def rows2 : List (Verdict 6) := chunks2.flatten
theorem checked2 : checkRows direction samples trees2 rows2 = true := by
  apply checkRows_flatten
  simp only [chunks2, List.all_cons, List.all_nil, check2_0_0, check2_0_1, check2_0_2, check2_0_3, check2_0_4, check2_0_5, check2_1_0, check2_1_1, check2_1_2, check2_1_3, check2_1_4, check2_1_5, check2_2_0, check2_2_1, check2_2_2, check2_2_3, check2_2_4, check2_2_5, check2_3_0, check2_3_1, check2_3_2, check2_3_3, check2_3_4, check2_3_5, check2_4_0, check2_4_1, check2_4_2, check2_4_3, check2_4_4, check2_4_5, check2_5_0, check2_5_1, check2_5_2, check2_5_3, check2_5_4, check2_5_5, check2_6_0, check2_6_1, check2_6_2, check2_6_3, check2_6_4, check2_6_5, check2_7_0, check2_7_1, check2_7_2, check2_7_3, check2_7_4, check2_7_5, check2_8_0, check2_8_1, check2_8_2, check2_8_3, check2_8_4, check2_8_5, Bool.true_and]
theorem link2 : rows2.map Verdict.patch = rows1.filterMap Verdict.kept := by
  simp only [rows2, rows1, List.map_flatten, List.filterMap_flatten, chunks2, chunks1, List.map_cons, List.map_nil, link2_0_0, link2_0_1, link2_0_2, link2_0_3, link2_0_4, link2_0_5, link2_1_0, link2_1_1, link2_1_2, link2_1_3, link2_1_4, link2_1_5, link2_2_0, link2_2_1, link2_2_2, link2_2_3, link2_2_4, link2_2_5, link2_3_0, link2_3_1, link2_3_2, link2_3_3, link2_3_4, link2_3_5, link2_4_0, link2_4_1, link2_4_2, link2_4_3, link2_4_4, link2_4_5, link2_5_0, link2_5_1, link2_5_2, link2_5_3, link2_5_4, link2_5_5, link2_6_0, link2_6_1, link2_6_2, link2_6_3, link2_6_4, link2_6_5, link2_7_0, link2_7_1, link2_7_2, link2_7_3, link2_7_4, link2_7_5, link2_8_0, link2_8_1, link2_8_2, link2_8_3, link2_8_4, link2_8_5]
theorem initial : rows0.map Verdict.patch = RadiusTwo.allTurnFamily := by
  simp only [rows0, List.map_flatten, chunks0, List.map_cons, List.map_nil, ← initial0_0, ← initial0_1, ← initial0_2, ← initial0_3, ← initial0_4, ← initial0_5, ← initial1_0, ← initial1_1, ← initial1_2, ← initial1_3, ← initial1_4, ← initial1_5, ← initial2_0, ← initial2_1, ← initial2_2, ← initial2_3, ← initial2_4, ← initial2_5, ← initial3_0, ← initial3_1, ← initial3_2, ← initial3_3, ← initial3_4, ← initial3_5, ← initial4_0, ← initial4_1, ← initial4_2, ← initial4_3, ← initial4_4, ← initial4_5, ← initial5_0, ← initial5_1, ← initial5_2, ← initial5_3, ← initial5_4, ← initial5_5, ← initial6_0, ← initial6_1, ← initial6_2, ← initial6_3, ← initial6_4, ← initial6_5, ← initial7_0, ← initial7_1, ← initial7_2, ← initial7_3, ← initial7_4, ← initial7_5, ← initial8_0, ← initial8_1, ← initial8_2, ← initial8_3, ← initial8_4, ← initial8_5]
  rfl
theorem certifiedFamily_eq : certifiedFamily = rows2.filterMap Verdict.kept := by
  simp only [certifiedFamily, finalChunks, rows2, chunks2, List.filterMap_flatten, List.map_cons, List.map_nil, final_eq0_0, final_eq0_1, final_eq0_2, final_eq0_3, final_eq0_4, final_eq0_5, final_eq1_0, final_eq1_1, final_eq1_2, final_eq1_3, final_eq1_4, final_eq1_5, final_eq2_0, final_eq2_1, final_eq2_2, final_eq2_3, final_eq2_4, final_eq2_5, final_eq3_0, final_eq3_1, final_eq3_2, final_eq3_3, final_eq3_4, final_eq3_5, final_eq4_0, final_eq4_1, final_eq4_2, final_eq4_3, final_eq4_4, final_eq4_5, final_eq5_0, final_eq5_1, final_eq5_2, final_eq5_3, final_eq5_4, final_eq5_5, final_eq6_0, final_eq6_1, final_eq6_2, final_eq6_3, final_eq6_4, final_eq6_5, final_eq7_0, final_eq7_1, final_eq7_2, final_eq7_3, final_eq7_4, final_eq7_5, final_eq8_0, final_eq8_1, final_eq8_2, final_eq8_3, final_eq8_4, final_eq8_5]
theorem round_counts : [rows0.length, rows1.length, rows2.length, certifiedFamily.length] = [918,720,654,636] := by decide
theorem certifiedFamily_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 2) certifiedFamily := by
  have h0 : OccurrenceComplete f (hexRegion 2) (rows0.map Verdict.patch) := by
    rw [initial]
    exact RadiusTwo.allTurnFamily_occurrenceComplete f hf
  have h1 := certified_round (hexRegion 2) direction samples samples_shared trees0 rows0 checked0 f h0
  have h2 : OccurrenceComplete f (hexRegion 2) (rows1.map Verdict.patch) := by
    rw [link1]
    exact h1
  have h3 := certified_round (hexRegion 2) direction samples samples_shared trees1 rows1 checked1 f h2
  have h4 : OccurrenceComplete f (hexRegion 2) (rows2.map Verdict.patch) := by
    rw [link2]
    exact h3
  have h5 := certified_round (hexRegion 2) direction samples samples_shared trees2 rows2 checked2 f h4
  rw [certifiedFamily_eq]
  exact h5
theorem extract_mem_certifiedFamily (f : Position → State) (hf : GloballyLegal f) (center : Position) : extract f center (hexRegion 2) ∈ certifiedFamily := certifiedFamily_occurrenceComplete f hf center
#print axioms certifiedFamily_occurrenceComplete
#print axioms extract_mem_certifiedFamily

end SpectreFinite.HexSearch.RadiusTwoPruning
