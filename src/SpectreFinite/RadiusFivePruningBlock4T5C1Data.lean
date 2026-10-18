module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock4T5C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_5_1_2 : List State := [(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(8,5),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(6,3),(7,2),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(8,3),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(1,4),(0,5),(1,2),(4,0),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(7,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(8,5),(1,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(1,5),(6,1),(4,1),(0,2),(1,1),(5,1)]
def stateRow4_5_1_9 : List State := [(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(6,5),(0,4),(5,4),(0,0),(7,2),(7,4),(6,3),(5,5),(7,0),(4,3),(1,5),(6,1),(4,1),(0,2),(1,1),(0,5),(4,4),(1,4),(0,5),(2,0),(7,3),(5,2),(8,0),(8,3),(6,0),(7,1),(7,5),(6,0),(3,1),(0,1),(6,2),(8,4),(1,4),(0,5),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(7,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(8,5),(1,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(1,5),(6,1),(4,1),(0,2),(1,1),(5,1)]
def stateRow4_5_1_11 : List State := [(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(6,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(7,0),(8,3),(8,5),(1,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(7,2),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(8,1),(6,5),(0,4),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(5,5),(7,0),(4,3),(1,5),(6,1),(4,1),(0,2),(1,1),(4,1),(4,4),(1,4),(0,5),(2,0),(7,3),(5,2),(8,0),(7,3),(7,5),(6,0),(3,1),(0,1),(6,2),(8,4),(6,4),(8,2),(5,0),(4,5),(1,0),(7,1),(7,5)]
def indexedRows0_4_5_1 : List (RowVerdict 6) := [.keep stateRow4_5_1_0, .keep stateRow4_5_1_1, .keep stateRow4_5_1_2, .keep stateRow4_5_1_3, .keep stateRow4_5_1_4, .keep stateRow4_5_1_5, .keep stateRow4_5_1_6, .keep stateRow4_5_1_7, .keep stateRow4_5_1_8, .keep stateRow4_5_1_9, .keep stateRow4_5_1_10, .keep stateRow4_5_1_11]
def rows0_4_5_1 : List (Verdict 6) := indexedRows0_4_5_1.map (materialize literalDomain)
def indexedRows1_4_5_1 : List (RowVerdict 6) := [.keep stateRow4_5_1_0, .keep stateRow4_5_1_1, .keep stateRow4_5_1_2, .keep stateRow4_5_1_3, .keep stateRow4_5_1_4, .keep stateRow4_5_1_5, .keep stateRow4_5_1_6, .keep stateRow4_5_1_7, .keep stateRow4_5_1_8, .reject stateRow4_5_1_9 5, .keep stateRow4_5_1_10, .keep stateRow4_5_1_11]
def rows1_4_5_1 : List (Verdict 6) := indexedRows1_4_5_1.map (materialize literalDomain)
theorem link1_4_5_1 : rows1_4_5_1.map Verdict.patch = rows0_4_5_1.filterMap Verdict.kept := by rfl
def indexedRows2_4_5_1 : List (RowVerdict 6) := [.keep stateRow4_5_1_0, .keep stateRow4_5_1_1, .keep stateRow4_5_1_2, .keep stateRow4_5_1_3, .keep stateRow4_5_1_4, .keep stateRow4_5_1_5, .keep stateRow4_5_1_6, .keep stateRow4_5_1_7, .keep stateRow4_5_1_8, .keep stateRow4_5_1_10, .reject stateRow4_5_1_11 2]
def rows2_4_5_1 : List (Verdict 6) := indexedRows2_4_5_1.map (materialize literalDomain)
theorem link2_4_5_1 : rows2_4_5_1.map Verdict.patch = rows1_4_5_1.filterMap Verdict.kept := by rfl
def indexedRows3_4_5_1 : List (RowVerdict 6) := [.keep stateRow4_5_1_0, .keep stateRow4_5_1_1, .keep stateRow4_5_1_2, .keep stateRow4_5_1_3, .keep stateRow4_5_1_4, .keep stateRow4_5_1_5, .keep stateRow4_5_1_6, .keep stateRow4_5_1_7, .keep stateRow4_5_1_8, .keep stateRow4_5_1_10]
def rows3_4_5_1 : List (Verdict 6) := indexedRows3_4_5_1.map (materialize literalDomain)
theorem link3_4_5_1 : rows3_4_5_1.map Verdict.patch = rows2_4_5_1.filterMap Verdict.kept := by rfl
def indexedRows4_4_5_1 : List (RowVerdict 6) := [.keep stateRow4_5_1_0, .keep stateRow4_5_1_1, .keep stateRow4_5_1_2, .keep stateRow4_5_1_3, .keep stateRow4_5_1_4, .keep stateRow4_5_1_5, .keep stateRow4_5_1_6, .keep stateRow4_5_1_7, .keep stateRow4_5_1_8, .keep stateRow4_5_1_10]
def rows4_4_5_1 : List (Verdict 6) := indexedRows4_4_5_1.map (materialize literalDomain)
theorem link4_4_5_1 : rows4_4_5_1.map Verdict.patch = rows3_4_5_1.filterMap Verdict.kept := by rfl
def indexedRows5_4_5_1 : List (RowVerdict 6) := [.keep stateRow4_5_1_0, .keep stateRow4_5_1_1, .reject stateRow4_5_1_2 2, .keep stateRow4_5_1_3, .keep stateRow4_5_1_4, .keep stateRow4_5_1_5, .keep stateRow4_5_1_6, .keep stateRow4_5_1_7, .keep stateRow4_5_1_8, .keep stateRow4_5_1_10]
def rows5_4_5_1 : List (Verdict 6) := indexedRows5_4_5_1.map (materialize literalDomain)
theorem link5_4_5_1 : rows5_4_5_1.map Verdict.patch = rows4_4_5_1.filterMap Verdict.kept := by rfl
def indexedRows6_4_5_1 : List (RowVerdict 6) := [.keep stateRow4_5_1_0, .keep stateRow4_5_1_1, .keep stateRow4_5_1_3, .keep stateRow4_5_1_4, .keep stateRow4_5_1_5, .keep stateRow4_5_1_6, .keep stateRow4_5_1_7, .keep stateRow4_5_1_8, .keep stateRow4_5_1_10]
def rows6_4_5_1 : List (Verdict 6) := indexedRows6_4_5_1.map (materialize literalDomain)
theorem link6_4_5_1 : rows6_4_5_1.map Verdict.patch = rows5_4_5_1.filterMap Verdict.kept := by rfl
theorem final_eq4_5_1 : final4_5_1 = rows6_4_5_1.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
