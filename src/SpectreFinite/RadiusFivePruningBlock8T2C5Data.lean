module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock8T2C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_8_2_5 : List (RowVerdict 6) := [.keep stateRow8_2_5_0, .keep stateRow8_2_5_1, .keep stateRow8_2_5_2, .keep stateRow8_2_5_3, .keep stateRow8_2_5_4, .keep stateRow8_2_5_5, .keep stateRow8_2_5_6, .keep stateRow8_2_5_7, .keep stateRow8_2_5_8, .keep stateRow8_2_5_9]
def rows0_8_2_5 : List (Verdict 6) := indexedRows0_8_2_5.map (materialize literalDomain)
def indexedRows1_8_2_5 : List (RowVerdict 6) := [.keep stateRow8_2_5_0, .keep stateRow8_2_5_1, .keep stateRow8_2_5_2, .keep stateRow8_2_5_3, .keep stateRow8_2_5_4, .keep stateRow8_2_5_5, .keep stateRow8_2_5_6, .keep stateRow8_2_5_7, .keep stateRow8_2_5_8, .keep stateRow8_2_5_9]
def rows1_8_2_5 : List (Verdict 6) := indexedRows1_8_2_5.map (materialize literalDomain)
theorem link1_8_2_5 : rows1_8_2_5.map Verdict.patch = rows0_8_2_5.filterMap Verdict.kept := by rfl
def indexedRows2_8_2_5 : List (RowVerdict 6) := [.keep stateRow8_2_5_0, .keep stateRow8_2_5_1, .keep stateRow8_2_5_2, .keep stateRow8_2_5_3, .keep stateRow8_2_5_4, .keep stateRow8_2_5_5, .keep stateRow8_2_5_6, .keep stateRow8_2_5_7, .keep stateRow8_2_5_8, .keep stateRow8_2_5_9]
def rows2_8_2_5 : List (Verdict 6) := indexedRows2_8_2_5.map (materialize literalDomain)
theorem link2_8_2_5 : rows2_8_2_5.map Verdict.patch = rows1_8_2_5.filterMap Verdict.kept := by rfl
def indexedRows3_8_2_5 : List (RowVerdict 6) := [.keep stateRow8_2_5_0, .keep stateRow8_2_5_1, .keep stateRow8_2_5_2, .keep stateRow8_2_5_3, .keep stateRow8_2_5_4, .keep stateRow8_2_5_5, .keep stateRow8_2_5_6, .keep stateRow8_2_5_7, .keep stateRow8_2_5_8, .keep stateRow8_2_5_9]
def rows3_8_2_5 : List (Verdict 6) := indexedRows3_8_2_5.map (materialize literalDomain)
theorem link3_8_2_5 : rows3_8_2_5.map Verdict.patch = rows2_8_2_5.filterMap Verdict.kept := by rfl
def indexedRows4_8_2_5 : List (RowVerdict 6) := [.keep stateRow8_2_5_0, .keep stateRow8_2_5_1, .keep stateRow8_2_5_2, .keep stateRow8_2_5_3, .keep stateRow8_2_5_4, .keep stateRow8_2_5_5, .keep stateRow8_2_5_6, .keep stateRow8_2_5_7, .keep stateRow8_2_5_8, .keep stateRow8_2_5_9]
def rows4_8_2_5 : List (Verdict 6) := indexedRows4_8_2_5.map (materialize literalDomain)
theorem link4_8_2_5 : rows4_8_2_5.map Verdict.patch = rows3_8_2_5.filterMap Verdict.kept := by rfl
def indexedRows5_8_2_5 : List (RowVerdict 6) := [.keep stateRow8_2_5_0, .keep stateRow8_2_5_1, .keep stateRow8_2_5_2, .keep stateRow8_2_5_3, .keep stateRow8_2_5_4, .keep stateRow8_2_5_5, .keep stateRow8_2_5_6, .keep stateRow8_2_5_7, .keep stateRow8_2_5_8, .keep stateRow8_2_5_9]
def rows5_8_2_5 : List (Verdict 6) := indexedRows5_8_2_5.map (materialize literalDomain)
theorem link5_8_2_5 : rows5_8_2_5.map Verdict.patch = rows4_8_2_5.filterMap Verdict.kept := by rfl
def indexedRows6_8_2_5 : List (RowVerdict 6) := [.keep stateRow8_2_5_0, .keep stateRow8_2_5_1, .keep stateRow8_2_5_2, .keep stateRow8_2_5_3, .keep stateRow8_2_5_4, .keep stateRow8_2_5_5, .keep stateRow8_2_5_6, .keep stateRow8_2_5_7, .keep stateRow8_2_5_8, .keep stateRow8_2_5_9]
def rows6_8_2_5 : List (Verdict 6) := indexedRows6_8_2_5.map (materialize literalDomain)
theorem link6_8_2_5 : rows6_8_2_5.map Verdict.patch = rows5_8_2_5.filterMap Verdict.kept := by rfl
theorem final_eq8_2_5 : final8_2_5 = rows6_8_2_5.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
