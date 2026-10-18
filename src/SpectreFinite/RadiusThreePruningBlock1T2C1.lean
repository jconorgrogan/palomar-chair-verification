module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock1T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow1_2_1_6 : List State := [(0,5),(4,4),(1,4),(0,5),(6,0),(7,1),(7,5),(6,0),(7,1),(8,2),(8,0),(7,3),(8,2),(5,0),(4,5),(6,2),(8,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(7,3),(4,2),(5,3),(8,5),(7,0),(1,2),(7,4),(6,3),(7,2)]
def stateRow1_2_1_8 : List State := [(1,3),(4,2),(5,3),(8,5),(6,5),(0,4),(3,4),(6,3),(7,2),(5,5),(7,0),(2,3),(0,2),(1,1),(4,1),(0,5),(4,4),(6,4),(1,2),(4,0),(7,3),(5,2),(7,1),(7,5),(0,3),(5,1),(0,1),(6,2),(7,3),(4,2),(5,3),(8,5),(1,0),(6,2),(7,4),(1,3),(8,2)]
def stateRow1_2_1_9 : List State := [(0,0),(7,2),(7,4),(6,3),(1,5),(6,1),(4,1),(0,2),(1,1),(5,5),(7,0),(7,3),(5,2),(5,0),(4,5),(0,5),(4,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,1),(7,5),(0,3),(8,1),(1,5),(6,1),(7,3),(4,2),(5,3),(8,5),(7,0),(6,2),(7,4),(6,3),(7,2)]
def indexedRows0_1_2_1 : List (RowVerdict 6) := [.keep stateRow1_2_1_0, .keep stateRow1_2_1_1, .keep stateRow1_2_1_2, .keep stateRow1_2_1_3, .keep stateRow1_2_1_4, .keep stateRow1_2_1_5, .reject stateRow1_2_1_6 3, .keep stateRow1_2_1_7, .keep stateRow1_2_1_8, .keep stateRow1_2_1_9, .keep stateRow1_2_1_10, .keep stateRow1_2_1_11]
def rows0_1_2_1 : List (Verdict 6) := indexedRows0_1_2_1.map (materialize literalDomain)
theorem check0_1_2_1 : checkRows direction samples0 trees0 rows0_1_2_1 = true := by
  rw [rows0_1_2_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_1_2_1]
  decide
def indexedRows1_1_2_1 : List (RowVerdict 6) := [.keep stateRow1_2_1_0, .keep stateRow1_2_1_1, .keep stateRow1_2_1_2, .keep stateRow1_2_1_3, .keep stateRow1_2_1_4, .keep stateRow1_2_1_5, .keep stateRow1_2_1_7, .reject stateRow1_2_1_8 1, .reject stateRow1_2_1_9 1, .keep stateRow1_2_1_10, .keep stateRow1_2_1_11]
def rows1_1_2_1 : List (Verdict 6) := indexedRows1_1_2_1.map (materialize literalDomain)
theorem check1_1_2_1 : checkRows direction samples1 trees1 rows1_1_2_1 = true := by
  rw [rows1_1_2_1, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_1_2_1]
  decide
theorem link1_1_2_1 : rows1_1_2_1.map Verdict.patch = rows0_1_2_1.filterMap Verdict.kept := by rfl
def indexedRows2_1_2_1 : List (RowVerdict 6) := [.keep stateRow1_2_1_0, .keep stateRow1_2_1_1, .keep stateRow1_2_1_2, .keep stateRow1_2_1_3, .keep stateRow1_2_1_4, .keep stateRow1_2_1_5, .keep stateRow1_2_1_7, .keep stateRow1_2_1_10, .keep stateRow1_2_1_11]
def rows2_1_2_1 : List (Verdict 6) := indexedRows2_1_2_1.map (materialize literalDomain)
theorem check2_1_2_1 : checkRows direction samples2 trees2 rows2_1_2_1 = true := by
  rw [rows2_1_2_1, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_1_2_1]
  decide
theorem link2_1_2_1 : rows2_1_2_1.map Verdict.patch = rows1_1_2_1.filterMap Verdict.kept := by rfl
theorem final_eq1_2_1 : final1_2_1 = rows2_1_2_1.filterMap Verdict.kept := by rfl
theorem initial1_2_1 : (source1_1).map (rotatePatch 2 (hexRegion 3)) = rows0_1_2_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
