module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock5T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_1_0_0 : List State := [(2,3),(0,2),(1,1),(4,1),(0,2),(1,1),(6,4),(1,2),(4,0),(7,3),(5,2),(8,0),(7,3),(7,5),(0,3),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(7,3),(4,2),(5,3),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(6,4),(1,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(3,5),(0,3),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(2,4),(1,3),(5,2),(8,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(6,5),(0,4),(5,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,0),(4,3),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(6,5),(0,4),(5,4),(0,0),(7,2),(7,4)]
def stateRow5_1_0_1 : List State := [(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(7,3),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(6,4),(1,2),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(0,3),(8,1),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(4,0),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4)]
def stateRow5_1_0_5 : List State := [(2,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,0),(3,2),(4,0),(7,3),(5,2),(8,0),(7,3),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(1,5),(6,1),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(2,0),(7,3),(5,2),(8,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(0,1),(6,2),(8,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(1,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(4,0),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4)]
def stateRow5_1_0_8 : List State := [(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(8,3),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(7,4),(6,3),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(4,1),(0,2),(1,1),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,3),(5,2),(8,0),(7,3),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(1,5),(6,1),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2),(2,0),(7,3),(5,2),(8,0),(8,3),(5,5),(1,0),(0,1),(6,2),(8,4),(1,4),(0,5),(4,4)]
def indexedRows0_5_1_0 : List (RowVerdict 6) := [.keep stateRow5_1_0_0, .keep stateRow5_1_0_1, .keep stateRow5_1_0_2, .keep stateRow5_1_0_3, .keep stateRow5_1_0_4, .keep stateRow5_1_0_5, .keep stateRow5_1_0_6, .keep stateRow5_1_0_7, .keep stateRow5_1_0_8, .keep stateRow5_1_0_9, .keep stateRow5_1_0_10, .keep stateRow5_1_0_11]
def rows0_5_1_0 : List (Verdict 6) := indexedRows0_5_1_0.map (materialize literalDomain)
def indexedRows1_5_1_0 : List (RowVerdict 6) := [.keep stateRow5_1_0_0, .keep stateRow5_1_0_1, .keep stateRow5_1_0_2, .keep stateRow5_1_0_3, .keep stateRow5_1_0_4, .keep stateRow5_1_0_5, .keep stateRow5_1_0_6, .keep stateRow5_1_0_7, .keep stateRow5_1_0_8, .keep stateRow5_1_0_9, .keep stateRow5_1_0_10, .keep stateRow5_1_0_11]
def rows1_5_1_0 : List (Verdict 6) := indexedRows1_5_1_0.map (materialize literalDomain)
theorem link1_5_1_0 : rows1_5_1_0.map Verdict.patch = rows0_5_1_0.filterMap Verdict.kept := by rfl
def indexedRows2_5_1_0 : List (RowVerdict 6) := [.reject stateRow5_1_0_0 4, .keep stateRow5_1_0_1, .keep stateRow5_1_0_2, .keep stateRow5_1_0_3, .keep stateRow5_1_0_4, .keep stateRow5_1_0_5, .keep stateRow5_1_0_6, .keep stateRow5_1_0_7, .reject stateRow5_1_0_8 0, .keep stateRow5_1_0_9, .keep stateRow5_1_0_10, .keep stateRow5_1_0_11]
def rows2_5_1_0 : List (Verdict 6) := indexedRows2_5_1_0.map (materialize literalDomain)
theorem link2_5_1_0 : rows2_5_1_0.map Verdict.patch = rows1_5_1_0.filterMap Verdict.kept := by rfl
def indexedRows3_5_1_0 : List (RowVerdict 6) := [.keep stateRow5_1_0_1, .keep stateRow5_1_0_2, .keep stateRow5_1_0_3, .keep stateRow5_1_0_4, .keep stateRow5_1_0_5, .keep stateRow5_1_0_6, .keep stateRow5_1_0_7, .keep stateRow5_1_0_9, .keep stateRow5_1_0_10, .keep stateRow5_1_0_11]
def rows3_5_1_0 : List (Verdict 6) := indexedRows3_5_1_0.map (materialize literalDomain)
theorem link3_5_1_0 : rows3_5_1_0.map Verdict.patch = rows2_5_1_0.filterMap Verdict.kept := by rfl
def indexedRows4_5_1_0 : List (RowVerdict 6) := [.reject stateRow5_1_0_1 0, .keep stateRow5_1_0_2, .keep stateRow5_1_0_3, .keep stateRow5_1_0_4, .keep stateRow5_1_0_5, .keep stateRow5_1_0_6, .keep stateRow5_1_0_7, .keep stateRow5_1_0_9, .keep stateRow5_1_0_10, .keep stateRow5_1_0_11]
def rows4_5_1_0 : List (Verdict 6) := indexedRows4_5_1_0.map (materialize literalDomain)
theorem link4_5_1_0 : rows4_5_1_0.map Verdict.patch = rows3_5_1_0.filterMap Verdict.kept := by rfl
def indexedRows5_5_1_0 : List (RowVerdict 6) := [.keep stateRow5_1_0_2, .keep stateRow5_1_0_3, .keep stateRow5_1_0_4, .reject stateRow5_1_0_5 0, .keep stateRow5_1_0_6, .keep stateRow5_1_0_7, .keep stateRow5_1_0_9, .keep stateRow5_1_0_10, .keep stateRow5_1_0_11]
def rows5_5_1_0 : List (Verdict 6) := indexedRows5_5_1_0.map (materialize literalDomain)
theorem link5_5_1_0 : rows5_5_1_0.map Verdict.patch = rows4_5_1_0.filterMap Verdict.kept := by rfl
def indexedRows6_5_1_0 : List (RowVerdict 6) := [.keep stateRow5_1_0_2, .keep stateRow5_1_0_3, .keep stateRow5_1_0_4, .keep stateRow5_1_0_6, .keep stateRow5_1_0_7, .keep stateRow5_1_0_9, .keep stateRow5_1_0_10, .keep stateRow5_1_0_11]
def rows6_5_1_0 : List (Verdict 6) := indexedRows6_5_1_0.map (materialize literalDomain)
theorem link6_5_1_0 : rows6_5_1_0.map Verdict.patch = rows5_5_1_0.filterMap Verdict.kept := by rfl
theorem final_eq5_1_0 : final5_1_0 = rows6_5_1_0.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
