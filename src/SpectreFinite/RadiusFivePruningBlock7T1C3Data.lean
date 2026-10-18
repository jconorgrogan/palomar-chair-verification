module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_3_4 : List State := [(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(7,4),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(4,1),(0,2),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(7,3),(5,2),(5,0),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(1,2),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(8,1),(1,5),(6,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(5,5),(7,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(4,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1)]
def indexedRows0_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .keep stateRow7_1_3_4, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows0_7_1_3 : List (Verdict 6) := indexedRows0_7_1_3.map (materialize literalDomain)
def indexedRows1_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .keep stateRow7_1_3_4, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows1_7_1_3 : List (Verdict 6) := indexedRows1_7_1_3.map (materialize literalDomain)
theorem link1_7_1_3 : rows1_7_1_3.map Verdict.patch = rows0_7_1_3.filterMap Verdict.kept := by rfl
def indexedRows2_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .keep stateRow7_1_3_4, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows2_7_1_3 : List (Verdict 6) := indexedRows2_7_1_3.map (materialize literalDomain)
theorem link2_7_1_3 : rows2_7_1_3.map Verdict.patch = rows1_7_1_3.filterMap Verdict.kept := by rfl
def indexedRows3_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .reject stateRow7_1_3_4 0, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows3_7_1_3 : List (Verdict 6) := indexedRows3_7_1_3.map (materialize literalDomain)
theorem link3_7_1_3 : rows3_7_1_3.map Verdict.patch = rows2_7_1_3.filterMap Verdict.kept := by rfl
def indexedRows4_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows4_7_1_3 : List (Verdict 6) := indexedRows4_7_1_3.map (materialize literalDomain)
theorem link4_7_1_3 : rows4_7_1_3.map Verdict.patch = rows3_7_1_3.filterMap Verdict.kept := by rfl
def indexedRows5_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows5_7_1_3 : List (Verdict 6) := indexedRows5_7_1_3.map (materialize literalDomain)
theorem link5_7_1_3 : rows5_7_1_3.map Verdict.patch = rows4_7_1_3.filterMap Verdict.kept := by rfl
def indexedRows6_7_1_3 : List (RowVerdict 6) := [.keep stateRow7_1_3_0, .keep stateRow7_1_3_1, .keep stateRow7_1_3_2, .keep stateRow7_1_3_3, .keep stateRow7_1_3_5, .keep stateRow7_1_3_6, .keep stateRow7_1_3_7, .keep stateRow7_1_3_8, .keep stateRow7_1_3_9, .keep stateRow7_1_3_10, .keep stateRow7_1_3_11]
def rows6_7_1_3 : List (Verdict 6) := indexedRows6_7_1_3.map (materialize literalDomain)
theorem link6_7_1_3 : rows6_7_1_3.map Verdict.patch = rows5_7_1_3.filterMap Verdict.kept := by rfl
theorem final_eq7_1_3 : final7_1_3 = rows6_7_1_3.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
