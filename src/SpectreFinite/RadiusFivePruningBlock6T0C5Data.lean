module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock6T0C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_6_0_5 : List (RowVerdict 6) := [.keep stateRow6_0_5_0, .keep stateRow6_0_5_1, .keep stateRow6_0_5_2]
def rows0_6_0_5 : List (Verdict 6) := indexedRows0_6_0_5.map (materialize literalDomain)
def indexedRows1_6_0_5 : List (RowVerdict 6) := [.keep stateRow6_0_5_0, .keep stateRow6_0_5_1, .keep stateRow6_0_5_2]
def rows1_6_0_5 : List (Verdict 6) := indexedRows1_6_0_5.map (materialize literalDomain)
theorem link1_6_0_5 : rows1_6_0_5.map Verdict.patch = rows0_6_0_5.filterMap Verdict.kept := by rfl
def indexedRows2_6_0_5 : List (RowVerdict 6) := [.keep stateRow6_0_5_0, .keep stateRow6_0_5_1, .keep stateRow6_0_5_2]
def rows2_6_0_5 : List (Verdict 6) := indexedRows2_6_0_5.map (materialize literalDomain)
theorem link2_6_0_5 : rows2_6_0_5.map Verdict.patch = rows1_6_0_5.filterMap Verdict.kept := by rfl
def indexedRows3_6_0_5 : List (RowVerdict 6) := [.keep stateRow6_0_5_0, .keep stateRow6_0_5_1, .keep stateRow6_0_5_2]
def rows3_6_0_5 : List (Verdict 6) := indexedRows3_6_0_5.map (materialize literalDomain)
theorem link3_6_0_5 : rows3_6_0_5.map Verdict.patch = rows2_6_0_5.filterMap Verdict.kept := by rfl
def indexedRows4_6_0_5 : List (RowVerdict 6) := [.keep stateRow6_0_5_0, .keep stateRow6_0_5_1, .keep stateRow6_0_5_2]
def rows4_6_0_5 : List (Verdict 6) := indexedRows4_6_0_5.map (materialize literalDomain)
theorem link4_6_0_5 : rows4_6_0_5.map Verdict.patch = rows3_6_0_5.filterMap Verdict.kept := by rfl
def indexedRows5_6_0_5 : List (RowVerdict 6) := [.keep stateRow6_0_5_0, .keep stateRow6_0_5_1, .keep stateRow6_0_5_2]
def rows5_6_0_5 : List (Verdict 6) := indexedRows5_6_0_5.map (materialize literalDomain)
theorem link5_6_0_5 : rows5_6_0_5.map Verdict.patch = rows4_6_0_5.filterMap Verdict.kept := by rfl
def indexedRows6_6_0_5 : List (RowVerdict 6) := [.keep stateRow6_0_5_0, .keep stateRow6_0_5_1, .keep stateRow6_0_5_2]
def rows6_6_0_5 : List (Verdict 6) := indexedRows6_6_0_5.map (materialize literalDomain)
theorem link6_6_0_5 : rows6_6_0_5.map Verdict.patch = rows5_6_0_5.filterMap Verdict.kept := by rfl
theorem final_eq6_0_5 : final6_0_5 = rows6_6_0_5.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
