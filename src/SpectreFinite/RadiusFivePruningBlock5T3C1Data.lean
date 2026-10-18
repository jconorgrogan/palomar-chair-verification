module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock5T3C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_3_1_2 : List State := [(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(1,3),(8,2),(5,0),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(5,4),(0,0),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(4,3),(1,5),(6,1),(1,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(2,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(3,1),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(5,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1)]
def stateRow5_3_1_5 : List State := [(1,4),(0,5),(4,4),(1,4),(0,5),(2,4),(7,5),(6,0),(7,1),(7,5),(6,0),(7,1),(6,5),(1,3),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(7,0),(6,5),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(3,0),(1,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(5,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1)]
def stateRow5_3_1_6 : List State := [(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(4,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(1,3),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(1,0),(6,5),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(4,5),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(0,1),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(1,0),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(5,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1)]
def stateRow5_3_1_10 : List State := [(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(4,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(3,3),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(1,0),(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(4,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(0,1),(0,0),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(8,5),(1,0),(6,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(7,4),(6,3),(7,2),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,5),(4,4),(0,0),(3,2),(4,0),(7,3),(5,2),(8,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1)]
def indexedRows0_5_3_1 : List (RowVerdict 6) := [.keep stateRow5_3_1_0, .keep stateRow5_3_1_1, .keep stateRow5_3_1_2, .keep stateRow5_3_1_3, .keep stateRow5_3_1_4, .keep stateRow5_3_1_5, .keep stateRow5_3_1_6, .keep stateRow5_3_1_7, .keep stateRow5_3_1_8, .keep stateRow5_3_1_9, .keep stateRow5_3_1_10, .keep stateRow5_3_1_11]
def rows0_5_3_1 : List (Verdict 6) := indexedRows0_5_3_1.map (materialize literalDomain)
def indexedRows1_5_3_1 : List (RowVerdict 6) := [.keep stateRow5_3_1_0, .keep stateRow5_3_1_1, .keep stateRow5_3_1_2, .keep stateRow5_3_1_3, .keep stateRow5_3_1_4, .keep stateRow5_3_1_5, .keep stateRow5_3_1_6, .keep stateRow5_3_1_7, .keep stateRow5_3_1_8, .keep stateRow5_3_1_9, .keep stateRow5_3_1_10, .keep stateRow5_3_1_11]
def rows1_5_3_1 : List (Verdict 6) := indexedRows1_5_3_1.map (materialize literalDomain)
theorem link1_5_3_1 : rows1_5_3_1.map Verdict.patch = rows0_5_3_1.filterMap Verdict.kept := by rfl
def indexedRows2_5_3_1 : List (RowVerdict 6) := [.keep stateRow5_3_1_0, .keep stateRow5_3_1_1, .keep stateRow5_3_1_2, .keep stateRow5_3_1_3, .keep stateRow5_3_1_4, .keep stateRow5_3_1_5, .reject stateRow5_3_1_6 2, .keep stateRow5_3_1_7, .keep stateRow5_3_1_8, .keep stateRow5_3_1_9, .keep stateRow5_3_1_10, .keep stateRow5_3_1_11]
def rows2_5_3_1 : List (Verdict 6) := indexedRows2_5_3_1.map (materialize literalDomain)
theorem link2_5_3_1 : rows2_5_3_1.map Verdict.patch = rows1_5_3_1.filterMap Verdict.kept := by rfl
def indexedRows3_5_3_1 : List (RowVerdict 6) := [.keep stateRow5_3_1_0, .keep stateRow5_3_1_1, .keep stateRow5_3_1_2, .keep stateRow5_3_1_3, .keep stateRow5_3_1_4, .keep stateRow5_3_1_5, .keep stateRow5_3_1_7, .keep stateRow5_3_1_8, .keep stateRow5_3_1_9, .keep stateRow5_3_1_10, .keep stateRow5_3_1_11]
def rows3_5_3_1 : List (Verdict 6) := indexedRows3_5_3_1.map (materialize literalDomain)
theorem link3_5_3_1 : rows3_5_3_1.map Verdict.patch = rows2_5_3_1.filterMap Verdict.kept := by rfl
def indexedRows4_5_3_1 : List (RowVerdict 6) := [.keep stateRow5_3_1_0, .keep stateRow5_3_1_1, .keep stateRow5_3_1_2, .keep stateRow5_3_1_3, .keep stateRow5_3_1_4, .keep stateRow5_3_1_5, .keep stateRow5_3_1_7, .keep stateRow5_3_1_8, .keep stateRow5_3_1_9, .keep stateRow5_3_1_10, .keep stateRow5_3_1_11]
def rows4_5_3_1 : List (Verdict 6) := indexedRows4_5_3_1.map (materialize literalDomain)
theorem link4_5_3_1 : rows4_5_3_1.map Verdict.patch = rows3_5_3_1.filterMap Verdict.kept := by rfl
def indexedRows5_5_3_1 : List (RowVerdict 6) := [.keep stateRow5_3_1_0, .keep stateRow5_3_1_1, .reject stateRow5_3_1_2 0, .keep stateRow5_3_1_3, .keep stateRow5_3_1_4, .keep stateRow5_3_1_5, .keep stateRow5_3_1_7, .keep stateRow5_3_1_8, .keep stateRow5_3_1_9, .keep stateRow5_3_1_10, .keep stateRow5_3_1_11]
def rows5_5_3_1 : List (Verdict 6) := indexedRows5_5_3_1.map (materialize literalDomain)
theorem link5_5_3_1 : rows5_5_3_1.map Verdict.patch = rows4_5_3_1.filterMap Verdict.kept := by rfl
def indexedRows6_5_3_1 : List (RowVerdict 6) := [.keep stateRow5_3_1_0, .keep stateRow5_3_1_1, .keep stateRow5_3_1_3, .keep stateRow5_3_1_4, .reject stateRow5_3_1_5 3, .keep stateRow5_3_1_7, .keep stateRow5_3_1_8, .keep stateRow5_3_1_9, .reject stateRow5_3_1_10 0, .keep stateRow5_3_1_11]
def rows6_5_3_1 : List (Verdict 6) := indexedRows6_5_3_1.map (materialize literalDomain)
theorem link6_5_3_1 : rows6_5_3_1.map Verdict.patch = rows5_5_3_1.filterMap Verdict.kept := by rfl
theorem final_eq5_3_1 : final5_3_1 = rows6_5_3_1.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
