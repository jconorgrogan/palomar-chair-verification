module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock4T0C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_0_2_3 : List State := [(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(7,4),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(6,5),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(6,1),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(7,3),(5,2),(8,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(6,2),(8,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3)]
def stateRow4_0_2_5 : List State := [(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(4,1),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(7,3),(5,2),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(0,3),(8,1),(1,5),(6,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(5,3),(5,5),(7,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3)]
def stateRow4_0_2_8 : List State := [(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(8,1),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(8,3),(5,5),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(1,4),(0,5),(4,4),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(7,1),(7,5),(0,1),(6,2),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(1,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(6,1),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2),(7,3),(5,2),(8,0),(8,3),(5,5),(1,0)]
def indexedRows0_4_0_2 : List (RowVerdict 6) := [.keep stateRow4_0_2_0, .keep stateRow4_0_2_1, .keep stateRow4_0_2_2, .keep stateRow4_0_2_3, .keep stateRow4_0_2_4, .keep stateRow4_0_2_5, .keep stateRow4_0_2_6, .keep stateRow4_0_2_7, .keep stateRow4_0_2_8, .keep stateRow4_0_2_9, .keep stateRow4_0_2_10, .keep stateRow4_0_2_11]
def rows0_4_0_2 : List (Verdict 6) := indexedRows0_4_0_2.map (materialize literalDomain)
def indexedRows1_4_0_2 : List (RowVerdict 6) := [.keep stateRow4_0_2_0, .keep stateRow4_0_2_1, .keep stateRow4_0_2_2, .keep stateRow4_0_2_3, .keep stateRow4_0_2_4, .keep stateRow4_0_2_5, .keep stateRow4_0_2_6, .keep stateRow4_0_2_7, .keep stateRow4_0_2_8, .keep stateRow4_0_2_9, .keep stateRow4_0_2_10, .keep stateRow4_0_2_11]
def rows1_4_0_2 : List (Verdict 6) := indexedRows1_4_0_2.map (materialize literalDomain)
theorem link1_4_0_2 : rows1_4_0_2.map Verdict.patch = rows0_4_0_2.filterMap Verdict.kept := by rfl
def indexedRows2_4_0_2 : List (RowVerdict 6) := [.keep stateRow4_0_2_0, .keep stateRow4_0_2_1, .keep stateRow4_0_2_2, .reject stateRow4_0_2_3 3, .keep stateRow4_0_2_4, .keep stateRow4_0_2_5, .keep stateRow4_0_2_6, .keep stateRow4_0_2_7, .keep stateRow4_0_2_8, .keep stateRow4_0_2_9, .keep stateRow4_0_2_10, .keep stateRow4_0_2_11]
def rows2_4_0_2 : List (Verdict 6) := indexedRows2_4_0_2.map (materialize literalDomain)
theorem link2_4_0_2 : rows2_4_0_2.map Verdict.patch = rows1_4_0_2.filterMap Verdict.kept := by rfl
def indexedRows3_4_0_2 : List (RowVerdict 6) := [.keep stateRow4_0_2_0, .keep stateRow4_0_2_1, .keep stateRow4_0_2_2, .keep stateRow4_0_2_4, .reject stateRow4_0_2_5 0, .keep stateRow4_0_2_6, .keep stateRow4_0_2_7, .reject stateRow4_0_2_8 5, .keep stateRow4_0_2_9, .keep stateRow4_0_2_10, .keep stateRow4_0_2_11]
def rows3_4_0_2 : List (Verdict 6) := indexedRows3_4_0_2.map (materialize literalDomain)
theorem link3_4_0_2 : rows3_4_0_2.map Verdict.patch = rows2_4_0_2.filterMap Verdict.kept := by rfl
def indexedRows4_4_0_2 : List (RowVerdict 6) := [.keep stateRow4_0_2_0, .keep stateRow4_0_2_1, .keep stateRow4_0_2_2, .keep stateRow4_0_2_4, .keep stateRow4_0_2_6, .keep stateRow4_0_2_7, .keep stateRow4_0_2_9, .keep stateRow4_0_2_10, .keep stateRow4_0_2_11]
def rows4_4_0_2 : List (Verdict 6) := indexedRows4_4_0_2.map (materialize literalDomain)
theorem link4_4_0_2 : rows4_4_0_2.map Verdict.patch = rows3_4_0_2.filterMap Verdict.kept := by rfl
def indexedRows5_4_0_2 : List (RowVerdict 6) := [.keep stateRow4_0_2_0, .keep stateRow4_0_2_1, .keep stateRow4_0_2_2, .keep stateRow4_0_2_4, .keep stateRow4_0_2_6, .keep stateRow4_0_2_7, .keep stateRow4_0_2_9, .keep stateRow4_0_2_10, .keep stateRow4_0_2_11]
def rows5_4_0_2 : List (Verdict 6) := indexedRows5_4_0_2.map (materialize literalDomain)
theorem link5_4_0_2 : rows5_4_0_2.map Verdict.patch = rows4_4_0_2.filterMap Verdict.kept := by rfl
def indexedRows6_4_0_2 : List (RowVerdict 6) := [.keep stateRow4_0_2_0, .keep stateRow4_0_2_1, .keep stateRow4_0_2_2, .keep stateRow4_0_2_4, .keep stateRow4_0_2_6, .keep stateRow4_0_2_7, .keep stateRow4_0_2_9, .keep stateRow4_0_2_10, .keep stateRow4_0_2_11]
def rows6_4_0_2 : List (Verdict 6) := indexedRows6_4_0_2.map (materialize literalDomain)
theorem link6_4_0_2 : rows6_4_0_2.map Verdict.patch = rows5_4_0_2.filterMap Verdict.kept := by rfl
theorem final_eq4_0_2 : final4_0_2 = rows6_4_0_2.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
