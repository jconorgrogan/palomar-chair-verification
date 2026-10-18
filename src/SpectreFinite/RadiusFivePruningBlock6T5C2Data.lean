module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock6T5C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_5_2_3 : List State := [(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,4),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(7,1),(7,5),(6,2),(8,4),(6,4),(1,2),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(1,0),(7,1),(7,5),(0,3),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(4,3),(7,5),(0,3),(4,1),(6,4),(1,2),(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(3,3),(0,3),(4,1),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(3,3),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0)]
def stateRow6_5_2_4 : List State := [(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,4),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(7,1),(7,5),(0,4),(5,4),(6,4),(1,2),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(4,3),(7,5),(0,3),(4,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(6,3),(2,2),(3,3),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(6,4),(1,2),(4,0),(7,3),(5,2),(5,0),(4,5),(0,3),(5,1),(0,1),(6,2),(8,4),(0,0)]
def indexedRows0_6_5_2 : List (RowVerdict 6) := [.keep stateRow6_5_2_0, .keep stateRow6_5_2_1, .keep stateRow6_5_2_2, .keep stateRow6_5_2_3, .keep stateRow6_5_2_4, .keep stateRow6_5_2_5, .keep stateRow6_5_2_6, .keep stateRow6_5_2_7, .keep stateRow6_5_2_8, .keep stateRow6_5_2_9, .keep stateRow6_5_2_10, .keep stateRow6_5_2_11]
def rows0_6_5_2 : List (Verdict 6) := indexedRows0_6_5_2.map (materialize literalDomain)
def indexedRows1_6_5_2 : List (RowVerdict 6) := [.keep stateRow6_5_2_0, .keep stateRow6_5_2_1, .keep stateRow6_5_2_2, .keep stateRow6_5_2_3, .keep stateRow6_5_2_4, .keep stateRow6_5_2_5, .keep stateRow6_5_2_6, .keep stateRow6_5_2_7, .keep stateRow6_5_2_8, .keep stateRow6_5_2_9, .keep stateRow6_5_2_10, .keep stateRow6_5_2_11]
def rows1_6_5_2 : List (Verdict 6) := indexedRows1_6_5_2.map (materialize literalDomain)
theorem link1_6_5_2 : rows1_6_5_2.map Verdict.patch = rows0_6_5_2.filterMap Verdict.kept := by rfl
def indexedRows2_6_5_2 : List (RowVerdict 6) := [.keep stateRow6_5_2_0, .keep stateRow6_5_2_1, .keep stateRow6_5_2_2, .keep stateRow6_5_2_3, .keep stateRow6_5_2_4, .keep stateRow6_5_2_5, .keep stateRow6_5_2_6, .keep stateRow6_5_2_7, .keep stateRow6_5_2_8, .keep stateRow6_5_2_9, .keep stateRow6_5_2_10, .keep stateRow6_5_2_11]
def rows2_6_5_2 : List (Verdict 6) := indexedRows2_6_5_2.map (materialize literalDomain)
theorem link2_6_5_2 : rows2_6_5_2.map Verdict.patch = rows1_6_5_2.filterMap Verdict.kept := by rfl
def indexedRows3_6_5_2 : List (RowVerdict 6) := [.keep stateRow6_5_2_0, .keep stateRow6_5_2_1, .keep stateRow6_5_2_2, .keep stateRow6_5_2_3, .keep stateRow6_5_2_4, .keep stateRow6_5_2_5, .keep stateRow6_5_2_6, .keep stateRow6_5_2_7, .keep stateRow6_5_2_8, .keep stateRow6_5_2_9, .keep stateRow6_5_2_10, .keep stateRow6_5_2_11]
def rows3_6_5_2 : List (Verdict 6) := indexedRows3_6_5_2.map (materialize literalDomain)
theorem link3_6_5_2 : rows3_6_5_2.map Verdict.patch = rows2_6_5_2.filterMap Verdict.kept := by rfl
def indexedRows4_6_5_2 : List (RowVerdict 6) := [.keep stateRow6_5_2_0, .keep stateRow6_5_2_1, .keep stateRow6_5_2_2, .keep stateRow6_5_2_3, .reject stateRow6_5_2_4 1, .keep stateRow6_5_2_5, .keep stateRow6_5_2_6, .keep stateRow6_5_2_7, .keep stateRow6_5_2_8, .keep stateRow6_5_2_9, .keep stateRow6_5_2_10, .keep stateRow6_5_2_11]
def rows4_6_5_2 : List (Verdict 6) := indexedRows4_6_5_2.map (materialize literalDomain)
theorem link4_6_5_2 : rows4_6_5_2.map Verdict.patch = rows3_6_5_2.filterMap Verdict.kept := by rfl
def indexedRows5_6_5_2 : List (RowVerdict 6) := [.keep stateRow6_5_2_0, .keep stateRow6_5_2_1, .keep stateRow6_5_2_2, .reject stateRow6_5_2_3 0, .keep stateRow6_5_2_5, .keep stateRow6_5_2_6, .keep stateRow6_5_2_7, .keep stateRow6_5_2_8, .keep stateRow6_5_2_9, .keep stateRow6_5_2_10, .keep stateRow6_5_2_11]
def rows5_6_5_2 : List (Verdict 6) := indexedRows5_6_5_2.map (materialize literalDomain)
theorem link5_6_5_2 : rows5_6_5_2.map Verdict.patch = rows4_6_5_2.filterMap Verdict.kept := by rfl
def indexedRows6_6_5_2 : List (RowVerdict 6) := [.keep stateRow6_5_2_0, .keep stateRow6_5_2_1, .keep stateRow6_5_2_2, .keep stateRow6_5_2_5, .keep stateRow6_5_2_6, .keep stateRow6_5_2_7, .keep stateRow6_5_2_8, .keep stateRow6_5_2_9, .keep stateRow6_5_2_10, .keep stateRow6_5_2_11]
def rows6_6_5_2 : List (Verdict 6) := indexedRows6_6_5_2.map (materialize literalDomain)
theorem link6_6_5_2 : rows6_6_5_2.map Verdict.patch = rows5_6_5_2.filterMap Verdict.kept := by rfl
theorem final_eq6_5_2 : final6_5_2 = rows6_6_5_2.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
