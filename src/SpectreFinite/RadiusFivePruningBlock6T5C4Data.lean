module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock6T5C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_6_5_4 : List (RowVerdict 6) := [.keep stateRow6_5_4_0, .keep stateRow6_5_4_1, .keep stateRow6_5_4_2, .keep stateRow6_5_4_3, .keep stateRow6_5_4_4, .keep stateRow6_5_4_5, .keep stateRow6_5_4_6, .keep stateRow6_5_4_7, .keep stateRow6_5_4_8, .keep stateRow6_5_4_9, .keep stateRow6_5_4_10, .keep stateRow6_5_4_11]
def rows0_6_5_4 : List (Verdict 6) := indexedRows0_6_5_4.map (materialize literalDomain)
def indexedRows1_6_5_4 : List (RowVerdict 6) := [.keep stateRow6_5_4_0, .keep stateRow6_5_4_1, .keep stateRow6_5_4_2, .keep stateRow6_5_4_3, .keep stateRow6_5_4_4, .keep stateRow6_5_4_5, .keep stateRow6_5_4_6, .keep stateRow6_5_4_7, .keep stateRow6_5_4_8, .keep stateRow6_5_4_9, .keep stateRow6_5_4_10, .keep stateRow6_5_4_11]
def rows1_6_5_4 : List (Verdict 6) := indexedRows1_6_5_4.map (materialize literalDomain)
theorem link1_6_5_4 : rows1_6_5_4.map Verdict.patch = rows0_6_5_4.filterMap Verdict.kept := by rfl
def indexedRows2_6_5_4 : List (RowVerdict 6) := [.keep stateRow6_5_4_0, .keep stateRow6_5_4_1, .keep stateRow6_5_4_2, .keep stateRow6_5_4_3, .keep stateRow6_5_4_4, .keep stateRow6_5_4_5, .keep stateRow6_5_4_6, .keep stateRow6_5_4_7, .keep stateRow6_5_4_8, .keep stateRow6_5_4_9, .keep stateRow6_5_4_10, .keep stateRow6_5_4_11]
def rows2_6_5_4 : List (Verdict 6) := indexedRows2_6_5_4.map (materialize literalDomain)
theorem link2_6_5_4 : rows2_6_5_4.map Verdict.patch = rows1_6_5_4.filterMap Verdict.kept := by rfl
def indexedRows3_6_5_4 : List (RowVerdict 6) := [.keep stateRow6_5_4_0, .keep stateRow6_5_4_1, .keep stateRow6_5_4_2, .keep stateRow6_5_4_3, .keep stateRow6_5_4_4, .keep stateRow6_5_4_5, .keep stateRow6_5_4_6, .keep stateRow6_5_4_7, .keep stateRow6_5_4_8, .keep stateRow6_5_4_9, .keep stateRow6_5_4_10, .keep stateRow6_5_4_11]
def rows3_6_5_4 : List (Verdict 6) := indexedRows3_6_5_4.map (materialize literalDomain)
theorem link3_6_5_4 : rows3_6_5_4.map Verdict.patch = rows2_6_5_4.filterMap Verdict.kept := by rfl
def indexedRows4_6_5_4 : List (RowVerdict 6) := [.keep stateRow6_5_4_0, .keep stateRow6_5_4_1, .keep stateRow6_5_4_2, .keep stateRow6_5_4_3, .keep stateRow6_5_4_4, .keep stateRow6_5_4_5, .keep stateRow6_5_4_6, .keep stateRow6_5_4_7, .keep stateRow6_5_4_8, .keep stateRow6_5_4_9, .keep stateRow6_5_4_10, .keep stateRow6_5_4_11]
def rows4_6_5_4 : List (Verdict 6) := indexedRows4_6_5_4.map (materialize literalDomain)
theorem link4_6_5_4 : rows4_6_5_4.map Verdict.patch = rows3_6_5_4.filterMap Verdict.kept := by rfl
def indexedRows5_6_5_4 : List (RowVerdict 6) := [.keep stateRow6_5_4_0, .keep stateRow6_5_4_1, .keep stateRow6_5_4_2, .keep stateRow6_5_4_3, .keep stateRow6_5_4_4, .keep stateRow6_5_4_5, .keep stateRow6_5_4_6, .keep stateRow6_5_4_7, .keep stateRow6_5_4_8, .keep stateRow6_5_4_9, .keep stateRow6_5_4_10, .keep stateRow6_5_4_11]
def rows5_6_5_4 : List (Verdict 6) := indexedRows5_6_5_4.map (materialize literalDomain)
theorem link5_6_5_4 : rows5_6_5_4.map Verdict.patch = rows4_6_5_4.filterMap Verdict.kept := by rfl
def indexedRows6_6_5_4 : List (RowVerdict 6) := [.keep stateRow6_5_4_0, .keep stateRow6_5_4_1, .keep stateRow6_5_4_2, .keep stateRow6_5_4_3, .keep stateRow6_5_4_4, .keep stateRow6_5_4_5, .keep stateRow6_5_4_6, .keep stateRow6_5_4_7, .keep stateRow6_5_4_8, .keep stateRow6_5_4_9, .keep stateRow6_5_4_10, .keep stateRow6_5_4_11]
def rows6_6_5_4 : List (Verdict 6) := indexedRows6_6_5_4.map (materialize literalDomain)
theorem link6_6_5_4 : rows6_6_5_4.map Verdict.patch = rows5_6_5_4.filterMap Verdict.kept := by rfl
theorem final_eq6_5_4 : final6_5_4 = rows6_6_5_4.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
