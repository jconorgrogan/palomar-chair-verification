module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock0T0C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_0_4_3 : List State := [(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(5,5),(7,0),(4,3),(3,5),(0,3),(4,1),(0,2),(0,5),(4,4),(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(6,0),(7,1),(7,5),(6,0),(7,1),(6,5),(0,4),(5,4),(6,4),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(0,3),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(1,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(3,0),(2,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5)]
def stateRow0_0_4_5 : List State := [(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(8,5),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(6,3),(7,2),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(1,4),(1,2),(4,0),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(0,3),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(5,3),(8,5),(1,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(0,4),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(4,3),(1,5),(6,1),(4,1),(0,2),(1,1),(5,1),(0,5),(2,0),(7,3),(5,2),(8,0),(8,3)]
def stateRow0_0_4_11 : List State := [(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(8,5),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(6,3),(7,2),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(6,4),(5,2),(8,0),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(0,3),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(5,3),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(0,1),(6,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(1,0),(2,1),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5)]
def indexedRows0_0_0_4 : List (RowVerdict 6) := [.keep stateRow0_0_4_0, .keep stateRow0_0_4_1, .keep stateRow0_0_4_2, .keep stateRow0_0_4_3, .keep stateRow0_0_4_4, .keep stateRow0_0_4_5, .keep stateRow0_0_4_6, .keep stateRow0_0_4_7, .keep stateRow0_0_4_8, .keep stateRow0_0_4_9, .keep stateRow0_0_4_10, .keep stateRow0_0_4_11]
def rows0_0_0_4 : List (Verdict 6) := indexedRows0_0_0_4.map (materialize literalDomain)
def indexedRows1_0_0_4 : List (RowVerdict 6) := [.keep stateRow0_0_4_0, .keep stateRow0_0_4_1, .keep stateRow0_0_4_2, .keep stateRow0_0_4_3, .keep stateRow0_0_4_4, .keep stateRow0_0_4_5, .keep stateRow0_0_4_6, .keep stateRow0_0_4_7, .keep stateRow0_0_4_8, .keep stateRow0_0_4_9, .keep stateRow0_0_4_10, .keep stateRow0_0_4_11]
def rows1_0_0_4 : List (Verdict 6) := indexedRows1_0_0_4.map (materialize literalDomain)
theorem link1_0_0_4 : rows1_0_0_4.map Verdict.patch = rows0_0_0_4.filterMap Verdict.kept := by rfl
def indexedRows2_0_0_4 : List (RowVerdict 6) := [.keep stateRow0_0_4_0, .keep stateRow0_0_4_1, .keep stateRow0_0_4_2, .keep stateRow0_0_4_3, .keep stateRow0_0_4_4, .keep stateRow0_0_4_5, .keep stateRow0_0_4_6, .keep stateRow0_0_4_7, .keep stateRow0_0_4_8, .keep stateRow0_0_4_9, .keep stateRow0_0_4_10, .keep stateRow0_0_4_11]
def rows2_0_0_4 : List (Verdict 6) := indexedRows2_0_0_4.map (materialize literalDomain)
theorem link2_0_0_4 : rows2_0_0_4.map Verdict.patch = rows1_0_0_4.filterMap Verdict.kept := by rfl
def indexedRows3_0_0_4 : List (RowVerdict 6) := [.keep stateRow0_0_4_0, .keep stateRow0_0_4_1, .keep stateRow0_0_4_2, .keep stateRow0_0_4_3, .keep stateRow0_0_4_4, .keep stateRow0_0_4_5, .keep stateRow0_0_4_6, .keep stateRow0_0_4_7, .keep stateRow0_0_4_8, .keep stateRow0_0_4_9, .keep stateRow0_0_4_10, .reject stateRow0_0_4_11 0]
def rows3_0_0_4 : List (Verdict 6) := indexedRows3_0_0_4.map (materialize literalDomain)
theorem link3_0_0_4 : rows3_0_0_4.map Verdict.patch = rows2_0_0_4.filterMap Verdict.kept := by rfl
def indexedRows4_0_0_4 : List (RowVerdict 6) := [.keep stateRow0_0_4_0, .keep stateRow0_0_4_1, .keep stateRow0_0_4_2, .keep stateRow0_0_4_3, .keep stateRow0_0_4_4, .reject stateRow0_0_4_5 2, .keep stateRow0_0_4_6, .keep stateRow0_0_4_7, .keep stateRow0_0_4_8, .keep stateRow0_0_4_9, .keep stateRow0_0_4_10]
def rows4_0_0_4 : List (Verdict 6) := indexedRows4_0_0_4.map (materialize literalDomain)
theorem link4_0_0_4 : rows4_0_0_4.map Verdict.patch = rows3_0_0_4.filterMap Verdict.kept := by rfl
def indexedRows5_0_0_4 : List (RowVerdict 6) := [.keep stateRow0_0_4_0, .keep stateRow0_0_4_1, .keep stateRow0_0_4_2, .reject stateRow0_0_4_3 3, .keep stateRow0_0_4_4, .keep stateRow0_0_4_6, .keep stateRow0_0_4_7, .keep stateRow0_0_4_8, .keep stateRow0_0_4_9, .keep stateRow0_0_4_10]
def rows5_0_0_4 : List (Verdict 6) := indexedRows5_0_0_4.map (materialize literalDomain)
theorem link5_0_0_4 : rows5_0_0_4.map Verdict.patch = rows4_0_0_4.filterMap Verdict.kept := by rfl
def indexedRows6_0_0_4 : List (RowVerdict 6) := [.keep stateRow0_0_4_0, .keep stateRow0_0_4_1, .keep stateRow0_0_4_2, .keep stateRow0_0_4_4, .keep stateRow0_0_4_6, .keep stateRow0_0_4_7, .keep stateRow0_0_4_8, .keep stateRow0_0_4_9, .keep stateRow0_0_4_10]
def rows6_0_0_4 : List (Verdict 6) := indexedRows6_0_0_4.map (materialize literalDomain)
theorem link6_0_0_4 : rows6_0_0_4.map Verdict.patch = rows5_0_0_4.filterMap Verdict.kept := by rfl
theorem final_eq0_0_4 : final0_0_4 = rows6_0_0_4.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
