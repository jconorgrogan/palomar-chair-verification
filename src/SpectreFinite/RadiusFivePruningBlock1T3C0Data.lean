module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock1T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_3_0_0 : List State := [(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(5,0),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,4),(0,0),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(7,1),(1,5),(6,1),(0,4),(5,4),(6,4),(1,2),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(5,4),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(4,3),(1,5),(6,1),(4,1),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(2,0),(7,3),(2,5),(6,0),(7,1),(7,5),(6,0),(3,1),(0,1),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5)]
def stateRow1_3_0_4 : List State := [(6,4),(1,2),(7,4),(6,3),(7,2),(4,0),(3,5),(0,3),(4,1),(0,2),(1,1),(5,1),(0,1),(0,5),(2,4),(1,3),(5,2),(8,0),(8,3),(5,5),(1,0),(6,0),(7,1),(6,5),(0,4),(5,4),(1,4),(0,5),(4,4),(0,0),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(6,0),(7,1),(1,5),(6,1),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(0,0),(7,2),(7,4),(5,5),(7,0),(8,3),(5,5),(7,0),(4,3),(1,5),(6,1),(4,1),(4,4),(1,4),(0,5),(4,4),(1,4),(0,5),(2,0),(7,3),(7,5),(6,0),(7,1),(7,5),(6,0),(3,1),(0,1),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5)]
def indexedRows0_1_3_0 : List (RowVerdict 6) := [.keep stateRow1_3_0_0, .keep stateRow1_3_0_1, .keep stateRow1_3_0_2, .keep stateRow1_3_0_3, .keep stateRow1_3_0_4, .keep stateRow1_3_0_5, .keep stateRow1_3_0_6, .keep stateRow1_3_0_7, .keep stateRow1_3_0_8, .keep stateRow1_3_0_9, .keep stateRow1_3_0_10, .keep stateRow1_3_0_11]
def rows0_1_3_0 : List (Verdict 6) := indexedRows0_1_3_0.map (materialize literalDomain)
def indexedRows1_1_3_0 : List (RowVerdict 6) := [.keep stateRow1_3_0_0, .keep stateRow1_3_0_1, .keep stateRow1_3_0_2, .keep stateRow1_3_0_3, .keep stateRow1_3_0_4, .keep stateRow1_3_0_5, .keep stateRow1_3_0_6, .keep stateRow1_3_0_7, .keep stateRow1_3_0_8, .keep stateRow1_3_0_9, .keep stateRow1_3_0_10, .keep stateRow1_3_0_11]
def rows1_1_3_0 : List (Verdict 6) := indexedRows1_1_3_0.map (materialize literalDomain)
theorem link1_1_3_0 : rows1_1_3_0.map Verdict.patch = rows0_1_3_0.filterMap Verdict.kept := by rfl
def indexedRows2_1_3_0 : List (RowVerdict 6) := [.keep stateRow1_3_0_0, .keep stateRow1_3_0_1, .keep stateRow1_3_0_2, .keep stateRow1_3_0_3, .keep stateRow1_3_0_4, .keep stateRow1_3_0_5, .keep stateRow1_3_0_6, .keep stateRow1_3_0_7, .keep stateRow1_3_0_8, .keep stateRow1_3_0_9, .keep stateRow1_3_0_10, .keep stateRow1_3_0_11]
def rows2_1_3_0 : List (Verdict 6) := indexedRows2_1_3_0.map (materialize literalDomain)
theorem link2_1_3_0 : rows2_1_3_0.map Verdict.patch = rows1_1_3_0.filterMap Verdict.kept := by rfl
def indexedRows3_1_3_0 : List (RowVerdict 6) := [.reject stateRow1_3_0_0 0, .keep stateRow1_3_0_1, .keep stateRow1_3_0_2, .keep stateRow1_3_0_3, .reject stateRow1_3_0_4 0, .keep stateRow1_3_0_5, .keep stateRow1_3_0_6, .keep stateRow1_3_0_7, .keep stateRow1_3_0_8, .keep stateRow1_3_0_9, .keep stateRow1_3_0_10, .keep stateRow1_3_0_11]
def rows3_1_3_0 : List (Verdict 6) := indexedRows3_1_3_0.map (materialize literalDomain)
theorem link3_1_3_0 : rows3_1_3_0.map Verdict.patch = rows2_1_3_0.filterMap Verdict.kept := by rfl
def indexedRows4_1_3_0 : List (RowVerdict 6) := [.keep stateRow1_3_0_1, .keep stateRow1_3_0_2, .keep stateRow1_3_0_3, .keep stateRow1_3_0_5, .keep stateRow1_3_0_6, .keep stateRow1_3_0_7, .keep stateRow1_3_0_8, .keep stateRow1_3_0_9, .keep stateRow1_3_0_10, .keep stateRow1_3_0_11]
def rows4_1_3_0 : List (Verdict 6) := indexedRows4_1_3_0.map (materialize literalDomain)
theorem link4_1_3_0 : rows4_1_3_0.map Verdict.patch = rows3_1_3_0.filterMap Verdict.kept := by rfl
def indexedRows5_1_3_0 : List (RowVerdict 6) := [.keep stateRow1_3_0_1, .keep stateRow1_3_0_2, .keep stateRow1_3_0_3, .keep stateRow1_3_0_5, .keep stateRow1_3_0_6, .keep stateRow1_3_0_7, .keep stateRow1_3_0_8, .keep stateRow1_3_0_9, .keep stateRow1_3_0_10, .keep stateRow1_3_0_11]
def rows5_1_3_0 : List (Verdict 6) := indexedRows5_1_3_0.map (materialize literalDomain)
theorem link5_1_3_0 : rows5_1_3_0.map Verdict.patch = rows4_1_3_0.filterMap Verdict.kept := by rfl
def indexedRows6_1_3_0 : List (RowVerdict 6) := [.keep stateRow1_3_0_1, .keep stateRow1_3_0_2, .keep stateRow1_3_0_3, .keep stateRow1_3_0_5, .keep stateRow1_3_0_6, .keep stateRow1_3_0_7, .keep stateRow1_3_0_8, .keep stateRow1_3_0_9, .keep stateRow1_3_0_10, .keep stateRow1_3_0_11]
def rows6_1_3_0 : List (Verdict 6) := indexedRows6_1_3_0.map (materialize literalDomain)
theorem link6_1_3_0 : rows6_1_3_0.map Verdict.patch = rows5_1_3_0.filterMap Verdict.kept := by rfl
theorem final_eq1_3_0 : final1_3_0 = rows6_1_3_0.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
