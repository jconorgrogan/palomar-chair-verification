module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock7T0C8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_0_8_4 : List State := [(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(8,3),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(7,4),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(4,1),(0,2),(1,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(7,3),(5,2),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(6,2),(8,4),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(7,1),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(7,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(6,2),(8,4),(6,4),(1,2),(7,4),(1,3),(8,2),(7,1),(7,5),(0,3),(8,1),(6,5),(0,4)]
def stateRow7_0_8_6 : List State := [(7,4),(1,3),(8,2),(8,0),(7,3),(8,2),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(8,4),(5,3),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(7,4),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(4,1),(0,2),(1,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(1,3),(5,2),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(0,4),(5,4),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(4,3),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(4,3),(3,5),(0,3),(4,1),(0,2),(1,1)]
def indexedRows0_7_0_8 : List (RowVerdict 6) := [.keep stateRow7_0_8_0, .keep stateRow7_0_8_1, .keep stateRow7_0_8_2, .keep stateRow7_0_8_3, .reject stateRow7_0_8_4 3, .keep stateRow7_0_8_5, .keep stateRow7_0_8_6, .keep stateRow7_0_8_7, .keep stateRow7_0_8_8, .keep stateRow7_0_8_9]
def rows0_7_0_8 : List (Verdict 6) := indexedRows0_7_0_8.map (materialize literalDomain)
def indexedRows1_7_0_8 : List (RowVerdict 6) := [.keep stateRow7_0_8_0, .keep stateRow7_0_8_1, .keep stateRow7_0_8_2, .keep stateRow7_0_8_3, .keep stateRow7_0_8_5, .keep stateRow7_0_8_6, .keep stateRow7_0_8_7, .keep stateRow7_0_8_8, .keep stateRow7_0_8_9]
def rows1_7_0_8 : List (Verdict 6) := indexedRows1_7_0_8.map (materialize literalDomain)
theorem link1_7_0_8 : rows1_7_0_8.map Verdict.patch = rows0_7_0_8.filterMap Verdict.kept := by rfl
def indexedRows2_7_0_8 : List (RowVerdict 6) := [.keep stateRow7_0_8_0, .keep stateRow7_0_8_1, .keep stateRow7_0_8_2, .keep stateRow7_0_8_3, .keep stateRow7_0_8_5, .keep stateRow7_0_8_6, .keep stateRow7_0_8_7, .keep stateRow7_0_8_8, .keep stateRow7_0_8_9]
def rows2_7_0_8 : List (Verdict 6) := indexedRows2_7_0_8.map (materialize literalDomain)
theorem link2_7_0_8 : rows2_7_0_8.map Verdict.patch = rows1_7_0_8.filterMap Verdict.kept := by rfl
def indexedRows3_7_0_8 : List (RowVerdict 6) := [.keep stateRow7_0_8_0, .keep stateRow7_0_8_1, .keep stateRow7_0_8_2, .keep stateRow7_0_8_3, .keep stateRow7_0_8_5, .keep stateRow7_0_8_6, .keep stateRow7_0_8_7, .keep stateRow7_0_8_8, .keep stateRow7_0_8_9]
def rows3_7_0_8 : List (Verdict 6) := indexedRows3_7_0_8.map (materialize literalDomain)
theorem link3_7_0_8 : rows3_7_0_8.map Verdict.patch = rows2_7_0_8.filterMap Verdict.kept := by rfl
def indexedRows4_7_0_8 : List (RowVerdict 6) := [.keep stateRow7_0_8_0, .keep stateRow7_0_8_1, .keep stateRow7_0_8_2, .keep stateRow7_0_8_3, .keep stateRow7_0_8_5, .keep stateRow7_0_8_6, .keep stateRow7_0_8_7, .keep stateRow7_0_8_8, .keep stateRow7_0_8_9]
def rows4_7_0_8 : List (Verdict 6) := indexedRows4_7_0_8.map (materialize literalDomain)
theorem link4_7_0_8 : rows4_7_0_8.map Verdict.patch = rows3_7_0_8.filterMap Verdict.kept := by rfl
def indexedRows5_7_0_8 : List (RowVerdict 6) := [.keep stateRow7_0_8_0, .keep stateRow7_0_8_1, .keep stateRow7_0_8_2, .keep stateRow7_0_8_3, .keep stateRow7_0_8_5, .keep stateRow7_0_8_6, .keep stateRow7_0_8_7, .keep stateRow7_0_8_8, .keep stateRow7_0_8_9]
def rows5_7_0_8 : List (Verdict 6) := indexedRows5_7_0_8.map (materialize literalDomain)
theorem link5_7_0_8 : rows5_7_0_8.map Verdict.patch = rows4_7_0_8.filterMap Verdict.kept := by rfl
def indexedRows6_7_0_8 : List (RowVerdict 6) := [.keep stateRow7_0_8_0, .keep stateRow7_0_8_1, .keep stateRow7_0_8_2, .keep stateRow7_0_8_3, .keep stateRow7_0_8_5, .reject stateRow7_0_8_6 2, .keep stateRow7_0_8_7, .keep stateRow7_0_8_8, .keep stateRow7_0_8_9]
def rows6_7_0_8 : List (Verdict 6) := indexedRows6_7_0_8.map (materialize literalDomain)
theorem link6_7_0_8 : rows6_7_0_8.map Verdict.patch = rows5_7_0_8.filterMap Verdict.kept := by rfl
theorem final_eq7_0_8 : final7_0_8 = rows6_7_0_8.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
