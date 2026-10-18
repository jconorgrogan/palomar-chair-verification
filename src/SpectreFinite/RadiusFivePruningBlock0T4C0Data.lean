module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock0T4C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_4_0_2 : List State := [(0,3),(4,1),(0,2),(1,1),(4,1),(0,2),(2,4),(1,3),(5,2),(8,0),(7,3),(5,2),(5,0),(7,1),(6,5),(0,4),(5,4),(6,4),(1,2),(8,4),(0,0),(5,0),(4,5),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(6,1),(8,4),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,3),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(0,5),(5,5),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(4,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2)]
def stateRow0_4_0_7 : List State := [(4,3),(7,5),(6,0),(7,1),(7,5),(0,3),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(1,3),(8,3),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(0,4),(7,4),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(8,5),(7,0),(4,3),(4,1),(0,2),(1,1),(8,1),(6,5),(0,4),(3,4),(6,3),(7,2),(7,4),(6,3),(5,2),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,2),(8,4),(1,4),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(7,5),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(1,0),(8,4),(6,4),(1,2),(7,4),(1,3),(8,2)]
def indexedRows0_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_2, .keep stateRow0_4_0_3, .keep stateRow0_4_0_4, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .reject stateRow0_4_0_7 3, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows0_0_4_0 : List (Verdict 6) := indexedRows0_0_4_0.map (materialize literalDomain)
def indexedRows1_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .reject stateRow0_4_0_2 3, .keep stateRow0_4_0_3, .keep stateRow0_4_0_4, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows1_0_4_0 : List (Verdict 6) := indexedRows1_0_4_0.map (materialize literalDomain)
theorem link1_0_4_0 : rows1_0_4_0.map Verdict.patch = rows0_0_4_0.filterMap Verdict.kept := by rfl
def indexedRows2_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_3, .keep stateRow0_4_0_4, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows2_0_4_0 : List (Verdict 6) := indexedRows2_0_4_0.map (materialize literalDomain)
theorem link2_0_4_0 : rows2_0_4_0.map Verdict.patch = rows1_0_4_0.filterMap Verdict.kept := by rfl
def indexedRows3_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_3, .keep stateRow0_4_0_4, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows3_0_4_0 : List (Verdict 6) := indexedRows3_0_4_0.map (materialize literalDomain)
theorem link3_0_4_0 : rows3_0_4_0.map Verdict.patch = rows2_0_4_0.filterMap Verdict.kept := by rfl
def indexedRows4_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_3, .keep stateRow0_4_0_4, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows4_0_4_0 : List (Verdict 6) := indexedRows4_0_4_0.map (materialize literalDomain)
theorem link4_0_4_0 : rows4_0_4_0.map Verdict.patch = rows3_0_4_0.filterMap Verdict.kept := by rfl
def indexedRows5_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_3, .keep stateRow0_4_0_4, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows5_0_4_0 : List (Verdict 6) := indexedRows5_0_4_0.map (materialize literalDomain)
theorem link5_0_4_0 : rows5_0_4_0.map Verdict.patch = rows4_0_4_0.filterMap Verdict.kept := by rfl
def indexedRows6_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_3, .keep stateRow0_4_0_4, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows6_0_4_0 : List (Verdict 6) := indexedRows6_0_4_0.map (materialize literalDomain)
theorem link6_0_4_0 : rows6_0_4_0.map Verdict.patch = rows5_0_4_0.filterMap Verdict.kept := by rfl
theorem final_eq0_4_0 : final0_4_0 = rows6_0_4_0.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
