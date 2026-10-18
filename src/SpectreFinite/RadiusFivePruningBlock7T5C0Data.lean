module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock7T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_5_0_0 : List State := [(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(3,0),(2,5),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(7,2),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(0,0),(7,2),(7,4),(7,0),(8,3),(8,5),(1,0),(7,1),(1,5),(6,1),(8,1),(7,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(6,5),(0,4),(5,4),(0,0),(7,2),(7,4)]
def stateRow7_5_0_9 : List State := [(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(1,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(5,5),(7,0),(2,3),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(4,4),(6,4),(1,2),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,3),(4,2),(5,3),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(7,4),(7,0),(8,3),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(5,3),(0,2),(1,1),(5,1),(0,1),(6,2),(7,4)]
def stateRow7_5_0_10 : List State := [(7,3),(4,2),(5,3),(8,5),(7,0),(4,3),(6,4),(1,2),(7,4),(6,3),(7,2),(7,4),(1,3),(3,5),(0,3),(4,1),(0,2),(1,1),(8,1),(6,5),(0,4),(0,5),(2,4),(1,3),(5,2),(8,0),(8,3),(5,5),(7,0),(2,3),(6,0),(7,1),(6,5),(0,4),(5,4),(1,4),(0,5),(4,4),(6,4),(1,2),(8,2),(5,0),(4,5),(7,0),(4,3),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(7,0),(8,3),(5,5),(7,0),(4,3),(3,5),(0,3),(4,1),(1,4),(0,5),(4,4),(1,4),(0,5),(2,4),(1,3),(6,0),(7,1),(7,5),(6,0),(7,1),(6,5)]
def indexedRows0_7_5_0 : List (RowVerdict 6) := [.keep stateRow7_5_0_0, .keep stateRow7_5_0_1, .keep stateRow7_5_0_2, .keep stateRow7_5_0_3, .keep stateRow7_5_0_4, .keep stateRow7_5_0_5, .keep stateRow7_5_0_6, .keep stateRow7_5_0_7, .keep stateRow7_5_0_8, .keep stateRow7_5_0_9, .keep stateRow7_5_0_10, .keep stateRow7_5_0_11]
def rows0_7_5_0 : List (Verdict 6) := indexedRows0_7_5_0.map (materialize literalDomain)
def indexedRows1_7_5_0 : List (RowVerdict 6) := [.keep stateRow7_5_0_0, .keep stateRow7_5_0_1, .keep stateRow7_5_0_2, .keep stateRow7_5_0_3, .keep stateRow7_5_0_4, .keep stateRow7_5_0_5, .keep stateRow7_5_0_6, .keep stateRow7_5_0_7, .keep stateRow7_5_0_8, .keep stateRow7_5_0_9, .keep stateRow7_5_0_10, .keep stateRow7_5_0_11]
def rows1_7_5_0 : List (Verdict 6) := indexedRows1_7_5_0.map (materialize literalDomain)
theorem link1_7_5_0 : rows1_7_5_0.map Verdict.patch = rows0_7_5_0.filterMap Verdict.kept := by rfl
def indexedRows2_7_5_0 : List (RowVerdict 6) := [.keep stateRow7_5_0_0, .keep stateRow7_5_0_1, .keep stateRow7_5_0_2, .keep stateRow7_5_0_3, .keep stateRow7_5_0_4, .keep stateRow7_5_0_5, .keep stateRow7_5_0_6, .keep stateRow7_5_0_7, .keep stateRow7_5_0_8, .keep stateRow7_5_0_9, .keep stateRow7_5_0_10, .keep stateRow7_5_0_11]
def rows2_7_5_0 : List (Verdict 6) := indexedRows2_7_5_0.map (materialize literalDomain)
theorem link2_7_5_0 : rows2_7_5_0.map Verdict.patch = rows1_7_5_0.filterMap Verdict.kept := by rfl
def indexedRows3_7_5_0 : List (RowVerdict 6) := [.keep stateRow7_5_0_0, .keep stateRow7_5_0_1, .keep stateRow7_5_0_2, .keep stateRow7_5_0_3, .keep stateRow7_5_0_4, .keep stateRow7_5_0_5, .keep stateRow7_5_0_6, .keep stateRow7_5_0_7, .keep stateRow7_5_0_8, .reject stateRow7_5_0_9 0, .keep stateRow7_5_0_10, .keep stateRow7_5_0_11]
def rows3_7_5_0 : List (Verdict 6) := indexedRows3_7_5_0.map (materialize literalDomain)
theorem link3_7_5_0 : rows3_7_5_0.map Verdict.patch = rows2_7_5_0.filterMap Verdict.kept := by rfl
def indexedRows4_7_5_0 : List (RowVerdict 6) := [.reject stateRow7_5_0_0 4, .keep stateRow7_5_0_1, .keep stateRow7_5_0_2, .keep stateRow7_5_0_3, .keep stateRow7_5_0_4, .keep stateRow7_5_0_5, .keep stateRow7_5_0_6, .keep stateRow7_5_0_7, .keep stateRow7_5_0_8, .reject stateRow7_5_0_10 2, .keep stateRow7_5_0_11]
def rows4_7_5_0 : List (Verdict 6) := indexedRows4_7_5_0.map (materialize literalDomain)
theorem link4_7_5_0 : rows4_7_5_0.map Verdict.patch = rows3_7_5_0.filterMap Verdict.kept := by rfl
def indexedRows5_7_5_0 : List (RowVerdict 6) := [.keep stateRow7_5_0_1, .keep stateRow7_5_0_2, .keep stateRow7_5_0_3, .keep stateRow7_5_0_4, .keep stateRow7_5_0_5, .keep stateRow7_5_0_6, .keep stateRow7_5_0_7, .keep stateRow7_5_0_8, .keep stateRow7_5_0_11]
def rows5_7_5_0 : List (Verdict 6) := indexedRows5_7_5_0.map (materialize literalDomain)
theorem link5_7_5_0 : rows5_7_5_0.map Verdict.patch = rows4_7_5_0.filterMap Verdict.kept := by rfl
def indexedRows6_7_5_0 : List (RowVerdict 6) := [.keep stateRow7_5_0_1, .keep stateRow7_5_0_2, .keep stateRow7_5_0_3, .keep stateRow7_5_0_4, .keep stateRow7_5_0_5, .keep stateRow7_5_0_6, .keep stateRow7_5_0_7, .keep stateRow7_5_0_8, .keep stateRow7_5_0_11]
def rows6_7_5_0 : List (Verdict 6) := indexedRows6_7_5_0.map (materialize literalDomain)
theorem link6_7_5_0 : rows6_7_5_0.map Verdict.patch = rows5_7_5_0.filterMap Verdict.kept := by rfl
theorem final_eq7_5_0 : final7_5_0 = rows6_7_5_0.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
