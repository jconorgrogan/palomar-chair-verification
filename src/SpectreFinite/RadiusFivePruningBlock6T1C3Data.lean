module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock6T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_1_3_2 : List State := [(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(6,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(7,4),(7,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(4,1),(0,2),(4,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,3),(5,2),(8,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,2),(7,4),(6,3),(7,2),(7,4),(6,3)]
def stateRow6_1_3_3 : List State := [(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(4,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3),(7,5),(7,2),(7,4),(6,3),(7,2),(7,4),(6,3)]
def indexedRows0_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .keep stateRow6_1_3_2, .keep stateRow6_1_3_3, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .keep stateRow6_1_3_7, .keep stateRow6_1_3_8, .keep stateRow6_1_3_9, .keep stateRow6_1_3_10, .keep stateRow6_1_3_11]
def rows0_6_1_3 : List (Verdict 6) := indexedRows0_6_1_3.map (materialize literalDomain)
def indexedRows1_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .reject stateRow6_1_3_2 5, .reject stateRow6_1_3_3 0, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .keep stateRow6_1_3_7, .keep stateRow6_1_3_8, .keep stateRow6_1_3_9, .keep stateRow6_1_3_10, .keep stateRow6_1_3_11]
def rows1_6_1_3 : List (Verdict 6) := indexedRows1_6_1_3.map (materialize literalDomain)
theorem link1_6_1_3 : rows1_6_1_3.map Verdict.patch = rows0_6_1_3.filterMap Verdict.kept := by rfl
def indexedRows2_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .keep stateRow6_1_3_7, .keep stateRow6_1_3_8, .keep stateRow6_1_3_9, .keep stateRow6_1_3_10, .keep stateRow6_1_3_11]
def rows2_6_1_3 : List (Verdict 6) := indexedRows2_6_1_3.map (materialize literalDomain)
theorem link2_6_1_3 : rows2_6_1_3.map Verdict.patch = rows1_6_1_3.filterMap Verdict.kept := by rfl
def indexedRows3_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .keep stateRow6_1_3_7, .keep stateRow6_1_3_8, .keep stateRow6_1_3_9, .keep stateRow6_1_3_10, .keep stateRow6_1_3_11]
def rows3_6_1_3 : List (Verdict 6) := indexedRows3_6_1_3.map (materialize literalDomain)
theorem link3_6_1_3 : rows3_6_1_3.map Verdict.patch = rows2_6_1_3.filterMap Verdict.kept := by rfl
def indexedRows4_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .keep stateRow6_1_3_7, .keep stateRow6_1_3_8, .keep stateRow6_1_3_9, .keep stateRow6_1_3_10, .keep stateRow6_1_3_11]
def rows4_6_1_3 : List (Verdict 6) := indexedRows4_6_1_3.map (materialize literalDomain)
theorem link4_6_1_3 : rows4_6_1_3.map Verdict.patch = rows3_6_1_3.filterMap Verdict.kept := by rfl
def indexedRows5_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .keep stateRow6_1_3_7, .keep stateRow6_1_3_8, .keep stateRow6_1_3_9, .keep stateRow6_1_3_10, .keep stateRow6_1_3_11]
def rows5_6_1_3 : List (Verdict 6) := indexedRows5_6_1_3.map (materialize literalDomain)
theorem link5_6_1_3 : rows5_6_1_3.map Verdict.patch = rows4_6_1_3.filterMap Verdict.kept := by rfl
def indexedRows6_6_1_3 : List (RowVerdict 6) := [.keep stateRow6_1_3_0, .keep stateRow6_1_3_1, .keep stateRow6_1_3_4, .keep stateRow6_1_3_5, .keep stateRow6_1_3_6, .keep stateRow6_1_3_7, .keep stateRow6_1_3_8, .keep stateRow6_1_3_9, .keep stateRow6_1_3_10, .keep stateRow6_1_3_11]
def rows6_6_1_3 : List (Verdict 6) := indexedRows6_6_1_3.map (materialize literalDomain)
theorem link6_6_1_3 : rows6_6_1_3.map Verdict.patch = rows5_6_1_3.filterMap Verdict.kept := by rfl
theorem final_eq6_1_3 : final6_1_3 = rows6_6_1_3.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
