module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock8T3C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_3_2_1 : List State := [(1,4),(0,5),(2,4),(1,3),(5,2),(8,0),(7,5),(6,0),(7,1),(6,5),(0,4),(5,4),(6,4),(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(0,3),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4),(8,5),(1,0),(7,1),(1,5),(6,1),(8,1)]
def indexedRows0_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .keep stateRow8_3_2_1, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows0_8_3_2 : List (Verdict 6) := indexedRows0_8_3_2.map (materialize literalDomain)
def indexedRows1_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .keep stateRow8_3_2_1, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows1_8_3_2 : List (Verdict 6) := indexedRows1_8_3_2.map (materialize literalDomain)
theorem link1_8_3_2 : rows1_8_3_2.map Verdict.patch = rows0_8_3_2.filterMap Verdict.kept := by rfl
def indexedRows2_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .keep stateRow8_3_2_1, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows2_8_3_2 : List (Verdict 6) := indexedRows2_8_3_2.map (materialize literalDomain)
theorem link2_8_3_2 : rows2_8_3_2.map Verdict.patch = rows1_8_3_2.filterMap Verdict.kept := by rfl
def indexedRows3_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .reject stateRow8_3_2_1 3, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows3_8_3_2 : List (Verdict 6) := indexedRows3_8_3_2.map (materialize literalDomain)
theorem link3_8_3_2 : rows3_8_3_2.map Verdict.patch = rows2_8_3_2.filterMap Verdict.kept := by rfl
def indexedRows4_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows4_8_3_2 : List (Verdict 6) := indexedRows4_8_3_2.map (materialize literalDomain)
theorem link4_8_3_2 : rows4_8_3_2.map Verdict.patch = rows3_8_3_2.filterMap Verdict.kept := by rfl
def indexedRows5_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows5_8_3_2 : List (Verdict 6) := indexedRows5_8_3_2.map (materialize literalDomain)
theorem link5_8_3_2 : rows5_8_3_2.map Verdict.patch = rows4_8_3_2.filterMap Verdict.kept := by rfl
def indexedRows6_8_3_2 : List (RowVerdict 6) := [.keep stateRow8_3_2_0, .keep stateRow8_3_2_2, .keep stateRow8_3_2_3, .keep stateRow8_3_2_4, .keep stateRow8_3_2_5, .keep stateRow8_3_2_6, .keep stateRow8_3_2_7, .keep stateRow8_3_2_8, .keep stateRow8_3_2_9, .keep stateRow8_3_2_10, .keep stateRow8_3_2_11]
def rows6_8_3_2 : List (Verdict 6) := indexedRows6_8_3_2.map (materialize literalDomain)
theorem link6_8_3_2 : rows6_8_3_2.map Verdict.patch = rows5_8_3_2.filterMap Verdict.kept := by rfl
theorem final_eq8_3_2 : final8_3_2 = rows6_8_3_2.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
