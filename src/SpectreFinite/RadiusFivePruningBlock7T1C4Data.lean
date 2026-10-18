module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock7T1C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_4_0 : List State := [(8,0),(7,3),(4,2),(5,3),(8,5),(7,0),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(7,4),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(8,1),(6,5),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(8,3),(5,5),(7,0),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(1,4),(0,5),(4,4),(6,4),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(7,1),(7,5),(0,3),(6,2),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2)]
def stateRow7_1_4_6 : List State := [(5,0),(4,5),(7,0),(8,3),(8,5),(7,0),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(7,4),(4,3),(1,5),(6,1),(4,1),(0,2),(1,1),(8,1),(6,5),(1,4),(0,5),(2,0),(7,3),(5,2),(8,0),(8,3),(5,5),(7,0),(7,5),(6,0),(3,1),(0,1),(6,2),(8,4),(1,4),(0,5),(4,4),(6,4),(7,3),(8,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(7,1),(7,5),(0,3),(6,2),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2)]
def stateRow7_1_4_7 : List State := [(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(5,4),(6,4),(1,2),(7,4),(1,3),(8,2),(5,0),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(5,4),(0,0),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(4,3),(1,5),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(2,0),(7,3),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(3,1),(0,1),(6,2),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5),(1,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(1,5),(6,1),(7,2),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,1),(6,5),(0,4),(5,4),(0,0),(7,2)]
def stateRow7_1_4_9 : List State := [(8,0),(7,3),(5,2),(5,0),(4,5),(1,0),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(0,1),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(1,0),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5),(7,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(1,5),(6,1),(7,2),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,1),(6,5),(0,4),(5,4),(0,0),(7,2)]
def stateRow7_1_4_11 : List State := [(8,0),(7,3),(8,2),(5,0),(4,5),(7,0),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(7,0),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(6,4),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(0,3),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2)]
def indexedRows0_7_1_4 : List (RowVerdict 6) := [.keep stateRow7_1_4_0, .keep stateRow7_1_4_1, .keep stateRow7_1_4_2, .keep stateRow7_1_4_3, .keep stateRow7_1_4_4, .keep stateRow7_1_4_5, .keep stateRow7_1_4_6, .keep stateRow7_1_4_7, .keep stateRow7_1_4_8, .keep stateRow7_1_4_9, .keep stateRow7_1_4_10, .keep stateRow7_1_4_11]
def rows0_7_1_4 : List (Verdict 6) := indexedRows0_7_1_4.map (materialize literalDomain)
def indexedRows1_7_1_4 : List (RowVerdict 6) := [.keep stateRow7_1_4_0, .keep stateRow7_1_4_1, .keep stateRow7_1_4_2, .keep stateRow7_1_4_3, .keep stateRow7_1_4_4, .keep stateRow7_1_4_5, .keep stateRow7_1_4_6, .keep stateRow7_1_4_7, .keep stateRow7_1_4_8, .reject stateRow7_1_4_9 1, .keep stateRow7_1_4_10, .keep stateRow7_1_4_11]
def rows1_7_1_4 : List (Verdict 6) := indexedRows1_7_1_4.map (materialize literalDomain)
theorem link1_7_1_4 : rows1_7_1_4.map Verdict.patch = rows0_7_1_4.filterMap Verdict.kept := by rfl
def indexedRows2_7_1_4 : List (RowVerdict 6) := [.reject stateRow7_1_4_0 0, .keep stateRow7_1_4_1, .keep stateRow7_1_4_2, .keep stateRow7_1_4_3, .keep stateRow7_1_4_4, .keep stateRow7_1_4_5, .reject stateRow7_1_4_6 0, .keep stateRow7_1_4_7, .keep stateRow7_1_4_8, .keep stateRow7_1_4_10, .reject stateRow7_1_4_11 0]
def rows2_7_1_4 : List (Verdict 6) := indexedRows2_7_1_4.map (materialize literalDomain)
theorem link2_7_1_4 : rows2_7_1_4.map Verdict.patch = rows1_7_1_4.filterMap Verdict.kept := by rfl
def indexedRows3_7_1_4 : List (RowVerdict 6) := [.keep stateRow7_1_4_1, .keep stateRow7_1_4_2, .keep stateRow7_1_4_3, .keep stateRow7_1_4_4, .keep stateRow7_1_4_5, .keep stateRow7_1_4_7, .keep stateRow7_1_4_8, .keep stateRow7_1_4_10]
def rows3_7_1_4 : List (Verdict 6) := indexedRows3_7_1_4.map (materialize literalDomain)
theorem link3_7_1_4 : rows3_7_1_4.map Verdict.patch = rows2_7_1_4.filterMap Verdict.kept := by rfl
def indexedRows4_7_1_4 : List (RowVerdict 6) := [.keep stateRow7_1_4_1, .keep stateRow7_1_4_2, .keep stateRow7_1_4_3, .keep stateRow7_1_4_4, .keep stateRow7_1_4_5, .reject stateRow7_1_4_7 4, .keep stateRow7_1_4_8, .keep stateRow7_1_4_10]
def rows4_7_1_4 : List (Verdict 6) := indexedRows4_7_1_4.map (materialize literalDomain)
theorem link4_7_1_4 : rows4_7_1_4.map Verdict.patch = rows3_7_1_4.filterMap Verdict.kept := by rfl
def indexedRows5_7_1_4 : List (RowVerdict 6) := [.keep stateRow7_1_4_1, .keep stateRow7_1_4_2, .keep stateRow7_1_4_3, .keep stateRow7_1_4_4, .keep stateRow7_1_4_5, .keep stateRow7_1_4_8, .keep stateRow7_1_4_10]
def rows5_7_1_4 : List (Verdict 6) := indexedRows5_7_1_4.map (materialize literalDomain)
theorem link5_7_1_4 : rows5_7_1_4.map Verdict.patch = rows4_7_1_4.filterMap Verdict.kept := by rfl
def indexedRows6_7_1_4 : List (RowVerdict 6) := [.keep stateRow7_1_4_1, .keep stateRow7_1_4_2, .keep stateRow7_1_4_3, .keep stateRow7_1_4_4, .keep stateRow7_1_4_5, .keep stateRow7_1_4_8, .keep stateRow7_1_4_10]
def rows6_7_1_4 : List (Verdict 6) := indexedRows6_7_1_4.map (materialize literalDomain)
theorem link6_7_1_4 : rows6_7_1_4.map Verdict.patch = rows5_7_1_4.filterMap Verdict.kept := by rfl
theorem final_eq7_1_4 : final7_1_4 = rows6_7_1_4.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
