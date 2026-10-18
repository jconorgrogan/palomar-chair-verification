module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_5_1 : List State := [(8,0),(7,3),(8,2),(5,0),(4,5),(7,0),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(3,0),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5),(7,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(1,5),(6,1),(7,2),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,1),(6,5),(0,4),(5,4),(0,0),(7,2)]
def indexedRows0_7_1_5 : List (RowVerdict 6) := [.keep stateRow7_1_5_0, .keep stateRow7_1_5_1, .keep stateRow7_1_5_2, .keep stateRow7_1_5_3, .keep stateRow7_1_5_4, .keep stateRow7_1_5_5, .keep stateRow7_1_5_6, .keep stateRow7_1_5_7, .keep stateRow7_1_5_8, .keep stateRow7_1_5_9, .keep stateRow7_1_5_10, .keep stateRow7_1_5_11]
def rows0_7_1_5 : List (Verdict 6) := indexedRows0_7_1_5.map (materialize literalDomain)
def indexedRows1_7_1_5 : List (RowVerdict 6) := [.keep stateRow7_1_5_0, .keep stateRow7_1_5_1, .keep stateRow7_1_5_2, .keep stateRow7_1_5_3, .keep stateRow7_1_5_4, .keep stateRow7_1_5_5, .keep stateRow7_1_5_6, .keep stateRow7_1_5_7, .keep stateRow7_1_5_8, .keep stateRow7_1_5_9, .keep stateRow7_1_5_10, .keep stateRow7_1_5_11]
def rows1_7_1_5 : List (Verdict 6) := indexedRows1_7_1_5.map (materialize literalDomain)
theorem link1_7_1_5 : rows1_7_1_5.map Verdict.patch = rows0_7_1_5.filterMap Verdict.kept := by rfl
def indexedRows2_7_1_5 : List (RowVerdict 6) := [.keep stateRow7_1_5_0, .keep stateRow7_1_5_1, .keep stateRow7_1_5_2, .keep stateRow7_1_5_3, .keep stateRow7_1_5_4, .keep stateRow7_1_5_5, .keep stateRow7_1_5_6, .keep stateRow7_1_5_7, .keep stateRow7_1_5_8, .keep stateRow7_1_5_9, .keep stateRow7_1_5_10, .keep stateRow7_1_5_11]
def rows2_7_1_5 : List (Verdict 6) := indexedRows2_7_1_5.map (materialize literalDomain)
theorem link2_7_1_5 : rows2_7_1_5.map Verdict.patch = rows1_7_1_5.filterMap Verdict.kept := by rfl
def indexedRows3_7_1_5 : List (RowVerdict 6) := [.keep stateRow7_1_5_0, .keep stateRow7_1_5_1, .keep stateRow7_1_5_2, .keep stateRow7_1_5_3, .keep stateRow7_1_5_4, .keep stateRow7_1_5_5, .keep stateRow7_1_5_6, .keep stateRow7_1_5_7, .keep stateRow7_1_5_8, .keep stateRow7_1_5_9, .keep stateRow7_1_5_10, .keep stateRow7_1_5_11]
def rows3_7_1_5 : List (Verdict 6) := indexedRows3_7_1_5.map (materialize literalDomain)
theorem link3_7_1_5 : rows3_7_1_5.map Verdict.patch = rows2_7_1_5.filterMap Verdict.kept := by rfl
def indexedRows4_7_1_5 : List (RowVerdict 6) := [.keep stateRow7_1_5_0, .keep stateRow7_1_5_1, .keep stateRow7_1_5_2, .keep stateRow7_1_5_3, .keep stateRow7_1_5_4, .keep stateRow7_1_5_5, .keep stateRow7_1_5_6, .keep stateRow7_1_5_7, .keep stateRow7_1_5_8, .keep stateRow7_1_5_9, .keep stateRow7_1_5_10, .keep stateRow7_1_5_11]
def rows4_7_1_5 : List (Verdict 6) := indexedRows4_7_1_5.map (materialize literalDomain)
theorem link4_7_1_5 : rows4_7_1_5.map Verdict.patch = rows3_7_1_5.filterMap Verdict.kept := by rfl
def indexedRows5_7_1_5 : List (RowVerdict 6) := [.keep stateRow7_1_5_0, .reject stateRow7_1_5_1 4, .keep stateRow7_1_5_2, .keep stateRow7_1_5_3, .keep stateRow7_1_5_4, .keep stateRow7_1_5_5, .keep stateRow7_1_5_6, .keep stateRow7_1_5_7, .keep stateRow7_1_5_8, .keep stateRow7_1_5_9, .keep stateRow7_1_5_10, .keep stateRow7_1_5_11]
def rows5_7_1_5 : List (Verdict 6) := indexedRows5_7_1_5.map (materialize literalDomain)
theorem link5_7_1_5 : rows5_7_1_5.map Verdict.patch = rows4_7_1_5.filterMap Verdict.kept := by rfl
def indexedRows6_7_1_5 : List (RowVerdict 6) := [.keep stateRow7_1_5_0, .keep stateRow7_1_5_2, .keep stateRow7_1_5_3, .keep stateRow7_1_5_4, .keep stateRow7_1_5_5, .keep stateRow7_1_5_6, .keep stateRow7_1_5_7, .keep stateRow7_1_5_8, .keep stateRow7_1_5_9, .keep stateRow7_1_5_10, .keep stateRow7_1_5_11]
def rows6_7_1_5 : List (Verdict 6) := indexedRows6_7_1_5.map (materialize literalDomain)
theorem link6_7_1_5 : rows6_7_1_5.map Verdict.patch = rows5_7_1_5.filterMap Verdict.kept := by rfl
theorem final_eq7_1_5 : final7_1_5 = rows6_7_1_5.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
