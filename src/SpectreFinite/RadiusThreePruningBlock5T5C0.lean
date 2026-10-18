module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock5T5C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow5_5_0_3 : List State := [(7,3),(8,2),(5,0),(4,5),(6,4),(1,2),(8,4),(0,0),(7,2),(7,5),(0,3),(8,1),(1,5),(6,1),(4,1),(1,3),(4,2),(5,3),(5,5),(7,0),(7,3),(5,2),(0,4),(1,4),(0,5),(4,4),(6,4),(1,2),(2,5),(6,0),(7,1),(7,5),(0,3),(7,2),(4,0),(7,3),(4,2)]
def stateRow5_5_0_7 : List State := [(8,5),(7,0),(4,3),(7,5),(6,3),(7,2),(7,4),(1,3),(4,2),(0,2),(1,1),(8,1),(6,5),(0,4),(3,4),(5,2),(8,0),(8,3),(5,5),(7,0),(2,3),(0,2),(5,4),(1,4),(0,5),(4,4),(6,4),(1,2),(7,5),(6,0),(7,1),(7,5),(0,3),(7,2),(4,0),(7,3),(4,2)]
def indexedRows0_5_5_0 : List (RowVerdict 6) := [.keep stateRow5_5_0_0, .keep stateRow5_5_0_1, .keep stateRow5_5_0_2, .keep stateRow5_5_0_3, .keep stateRow5_5_0_4, .keep stateRow5_5_0_5, .keep stateRow5_5_0_6, .keep stateRow5_5_0_7, .keep stateRow5_5_0_8, .keep stateRow5_5_0_9, .keep stateRow5_5_0_10, .keep stateRow5_5_0_11]
def rows0_5_5_0 : List (Verdict 6) := indexedRows0_5_5_0.map (materialize literalDomain)
theorem check0_5_5_0 : checkRows direction samples0 trees0 rows0_5_5_0 = true := by
  rw [rows0_5_5_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_5_5_0]
  decide
def indexedRows1_5_5_0 : List (RowVerdict 6) := [.keep stateRow5_5_0_0, .keep stateRow5_5_0_1, .keep stateRow5_5_0_2, .reject stateRow5_5_0_3 2, .keep stateRow5_5_0_4, .keep stateRow5_5_0_5, .keep stateRow5_5_0_6, .reject stateRow5_5_0_7 2, .keep stateRow5_5_0_8, .keep stateRow5_5_0_9, .keep stateRow5_5_0_10, .keep stateRow5_5_0_11]
def rows1_5_5_0 : List (Verdict 6) := indexedRows1_5_5_0.map (materialize literalDomain)
theorem check1_5_5_0 : checkRows direction samples1 trees1 rows1_5_5_0 = true := by
  rw [rows1_5_5_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_5_5_0]
  decide
theorem link1_5_5_0 : rows1_5_5_0.map Verdict.patch = rows0_5_5_0.filterMap Verdict.kept := by rfl
def indexedRows2_5_5_0 : List (RowVerdict 6) := [.keep stateRow5_5_0_0, .keep stateRow5_5_0_1, .keep stateRow5_5_0_2, .keep stateRow5_5_0_4, .keep stateRow5_5_0_5, .keep stateRow5_5_0_6, .keep stateRow5_5_0_8, .keep stateRow5_5_0_9, .keep stateRow5_5_0_10, .keep stateRow5_5_0_11]
def rows2_5_5_0 : List (Verdict 6) := indexedRows2_5_5_0.map (materialize literalDomain)
theorem check2_5_5_0 : checkRows direction samples2 trees2 rows2_5_5_0 = true := by
  rw [rows2_5_5_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_5_5_0]
  decide
theorem link2_5_5_0 : rows2_5_5_0.map Verdict.patch = rows1_5_5_0.filterMap Verdict.kept := by rfl
theorem final_eq5_5_0 : final5_5_0 = rows2_5_5_0.filterMap Verdict.kept := by rfl
theorem initial5_5_0 : (source5_0).map (rotatePatch 5 (hexRegion 3)) = rows0_5_5_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
