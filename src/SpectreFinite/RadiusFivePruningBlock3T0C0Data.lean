module

public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock3T0C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow3_0_0_0 : List State := [(2,4),(1,3),(5,2),(8,0),(7,3),(5,2),(7,1),(6,5),(0,4),(5,4),(6,4),(1,2),(8,4),(5,0),(4,5),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(8,4),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(8,1),(1,5),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(5,3),(5,5),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4)]
def stateRow3_0_0_2 : List State := [(7,4),(1,3),(8,2),(8,0),(7,3),(4,2),(8,1),(6,5),(0,4),(5,4),(6,4),(1,2),(7,4),(8,3),(8,5),(7,0),(4,3),(7,5),(0,3),(8,1),(6,5),(7,4),(6,3),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(4,1),(0,2),(1,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(7,3),(5,2),(8,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(6,2),(8,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4)]
def indexedRows0_3_0_0 : List (RowVerdict 6) := [.keep stateRow3_0_0_0, .keep stateRow3_0_0_1, .reject stateRow3_0_0_2 3, .keep stateRow3_0_0_3, .keep stateRow3_0_0_4, .keep stateRow3_0_0_5, .keep stateRow3_0_0_6]
def rows0_3_0_0 : List (Verdict 6) := indexedRows0_3_0_0.map (materialize literalDomain)
def indexedRows1_3_0_0 : List (RowVerdict 6) := [.reject stateRow3_0_0_0 3, .keep stateRow3_0_0_1, .keep stateRow3_0_0_3, .keep stateRow3_0_0_4, .keep stateRow3_0_0_5, .keep stateRow3_0_0_6]
def rows1_3_0_0 : List (Verdict 6) := indexedRows1_3_0_0.map (materialize literalDomain)
theorem link1_3_0_0 : rows1_3_0_0.map Verdict.patch = rows0_3_0_0.filterMap Verdict.kept := by rfl
def indexedRows2_3_0_0 : List (RowVerdict 6) := [.keep stateRow3_0_0_1, .keep stateRow3_0_0_3, .keep stateRow3_0_0_4, .keep stateRow3_0_0_5, .keep stateRow3_0_0_6]
def rows2_3_0_0 : List (Verdict 6) := indexedRows2_3_0_0.map (materialize literalDomain)
theorem link2_3_0_0 : rows2_3_0_0.map Verdict.patch = rows1_3_0_0.filterMap Verdict.kept := by rfl
def indexedRows3_3_0_0 : List (RowVerdict 6) := [.keep stateRow3_0_0_1, .keep stateRow3_0_0_3, .keep stateRow3_0_0_4, .keep stateRow3_0_0_5, .keep stateRow3_0_0_6]
def rows3_3_0_0 : List (Verdict 6) := indexedRows3_3_0_0.map (materialize literalDomain)
theorem link3_3_0_0 : rows3_3_0_0.map Verdict.patch = rows2_3_0_0.filterMap Verdict.kept := by rfl
def indexedRows4_3_0_0 : List (RowVerdict 6) := [.keep stateRow3_0_0_1, .keep stateRow3_0_0_3, .keep stateRow3_0_0_4, .keep stateRow3_0_0_5, .keep stateRow3_0_0_6]
def rows4_3_0_0 : List (Verdict 6) := indexedRows4_3_0_0.map (materialize literalDomain)
theorem link4_3_0_0 : rows4_3_0_0.map Verdict.patch = rows3_3_0_0.filterMap Verdict.kept := by rfl
def indexedRows5_3_0_0 : List (RowVerdict 6) := [.keep stateRow3_0_0_1, .keep stateRow3_0_0_3, .keep stateRow3_0_0_4, .keep stateRow3_0_0_5, .keep stateRow3_0_0_6]
def rows5_3_0_0 : List (Verdict 6) := indexedRows5_3_0_0.map (materialize literalDomain)
theorem link5_3_0_0 : rows5_3_0_0.map Verdict.patch = rows4_3_0_0.filterMap Verdict.kept := by rfl
def indexedRows6_3_0_0 : List (RowVerdict 6) := [.keep stateRow3_0_0_1, .keep stateRow3_0_0_3, .keep stateRow3_0_0_4, .keep stateRow3_0_0_5, .keep stateRow3_0_0_6]
def rows6_3_0_0 : List (Verdict 6) := indexedRows6_3_0_0.map (materialize literalDomain)
theorem link6_3_0_0 : rows6_3_0_0.map Verdict.patch = rows5_3_0_0.filterMap Verdict.kept := by rfl
theorem final_eq3_0_0 : final3_0_0 = rows6_3_0_0.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
