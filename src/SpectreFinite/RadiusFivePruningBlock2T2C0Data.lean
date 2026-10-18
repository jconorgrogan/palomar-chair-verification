module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock2T2C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow2_2_0_0 : List State := [(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(5,3),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(5,3),(8,5),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(4,1),(7,4),(6,3),(7,2),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(7,3),(5,2),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(6,4),(1,2),(8,0),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(0,3),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(7,3),(4,2),(0,3),(8,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,3),(5,5),(7,0),(8,3),(5,5),(1,0)]
def stateRow2_2_0_4 : List State := [(5,1),(0,1),(6,2),(8,4),(6,4),(1,2),(5,3),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(5,3),(8,5),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(6,3),(7,2),(5,3),(8,5),(7,0),(4,3),(7,5),(0,3),(4,1),(0,2),(1,1),(8,1),(3,4),(6,3),(7,2),(7,4),(6,3),(2,2),(3,3),(5,2),(8,0),(8,3),(5,5),(0,2),(1,1),(4,1),(0,2),(1,1),(0,1),(6,2),(8,4),(1,4),(0,5),(4,0),(7,3),(5,2),(5,0),(4,5),(1,0),(7,1),(7,5),(6,0),(0,1),(6,2),(8,4),(0,0),(7,2),(4,0),(7,3),(8,2),(1,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0)]
def indexedRows0_2_2_0 : List (RowVerdict 6) := [.reject stateRow2_2_0_0 0, .keep stateRow2_2_0_1, .keep stateRow2_2_0_2, .keep stateRow2_2_0_3, .keep stateRow2_2_0_4, .keep stateRow2_2_0_5]
def rows0_2_2_0 : List (Verdict 6) := indexedRows0_2_2_0.map (materialize literalDomain)
def indexedRows1_2_2_0 : List (RowVerdict 6) := [.keep stateRow2_2_0_1, .keep stateRow2_2_0_2, .keep stateRow2_2_0_3, .keep stateRow2_2_0_4, .keep stateRow2_2_0_5]
def rows1_2_2_0 : List (Verdict 6) := indexedRows1_2_2_0.map (materialize literalDomain)
theorem link1_2_2_0 : rows1_2_2_0.map Verdict.patch = rows0_2_2_0.filterMap Verdict.kept := by rfl
def indexedRows2_2_2_0 : List (RowVerdict 6) := [.keep stateRow2_2_0_1, .keep stateRow2_2_0_2, .keep stateRow2_2_0_3, .keep stateRow2_2_0_4, .keep stateRow2_2_0_5]
def rows2_2_2_0 : List (Verdict 6) := indexedRows2_2_2_0.map (materialize literalDomain)
theorem link2_2_2_0 : rows2_2_2_0.map Verdict.patch = rows1_2_2_0.filterMap Verdict.kept := by rfl
def indexedRows3_2_2_0 : List (RowVerdict 6) := [.keep stateRow2_2_0_1, .keep stateRow2_2_0_2, .keep stateRow2_2_0_3, .keep stateRow2_2_0_4, .keep stateRow2_2_0_5]
def rows3_2_2_0 : List (Verdict 6) := indexedRows3_2_2_0.map (materialize literalDomain)
theorem link3_2_2_0 : rows3_2_2_0.map Verdict.patch = rows2_2_2_0.filterMap Verdict.kept := by rfl
def indexedRows4_2_2_0 : List (RowVerdict 6) := [.keep stateRow2_2_0_1, .keep stateRow2_2_0_2, .keep stateRow2_2_0_3, .keep stateRow2_2_0_4, .keep stateRow2_2_0_5]
def rows4_2_2_0 : List (Verdict 6) := indexedRows4_2_2_0.map (materialize literalDomain)
theorem link4_2_2_0 : rows4_2_2_0.map Verdict.patch = rows3_2_2_0.filterMap Verdict.kept := by rfl
def indexedRows5_2_2_0 : List (RowVerdict 6) := [.keep stateRow2_2_0_1, .keep stateRow2_2_0_2, .keep stateRow2_2_0_3, .keep stateRow2_2_0_4, .keep stateRow2_2_0_5]
def rows5_2_2_0 : List (Verdict 6) := indexedRows5_2_2_0.map (materialize literalDomain)
theorem link5_2_2_0 : rows5_2_2_0.map Verdict.patch = rows4_2_2_0.filterMap Verdict.kept := by rfl
def indexedRows6_2_2_0 : List (RowVerdict 6) := [.keep stateRow2_2_0_1, .keep stateRow2_2_0_2, .keep stateRow2_2_0_3, .reject stateRow2_2_0_4 1, .keep stateRow2_2_0_5]
def rows6_2_2_0 : List (Verdict 6) := indexedRows6_2_2_0.map (materialize literalDomain)
theorem link6_2_2_0 : rows6_2_2_0.map Verdict.patch = rows5_2_2_0.filterMap Verdict.kept := by rfl
theorem final_eq2_2_0 : final2_2_0 = rows6_2_2_0.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
