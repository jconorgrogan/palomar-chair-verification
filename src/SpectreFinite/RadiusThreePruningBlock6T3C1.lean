module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock6T3C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_3_1_0 : List State := [(1,3),(5,2),(8,0),(8,3),(6,5),(0,4),(5,4),(1,4),(0,5),(4,5),(7,0),(4,3),(7,5),(6,0),(7,1),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(6,1),(4,1),(0,2),(1,1),(5,1),(0,1),(7,3),(5,2),(8,0),(8,3),(5,5),(6,2),(8,4),(1,4),(0,5)]
def indexedRows0_6_3_1 : List (RowVerdict 6) := [.reject stateRow6_3_1_0 1, .keep stateRow6_3_1_1, .keep stateRow6_3_1_2, .keep stateRow6_3_1_3, .keep stateRow6_3_1_4, .keep stateRow6_3_1_5, .keep stateRow6_3_1_6, .keep stateRow6_3_1_7, .keep stateRow6_3_1_8, .keep stateRow6_3_1_9, .keep stateRow6_3_1_10]
def rows0_6_3_1 : List (Verdict 6) := indexedRows0_6_3_1.map (materialize literalDomain)
theorem check0_6_3_1 : checkRows direction samples0 trees0 rows0_6_3_1 = true := by
  rw [rows0_6_3_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_6_3_1]
  decide
def indexedRows1_6_3_1 : List (RowVerdict 6) := [.keep stateRow6_3_1_1, .keep stateRow6_3_1_2, .keep stateRow6_3_1_3, .keep stateRow6_3_1_4, .keep stateRow6_3_1_5, .keep stateRow6_3_1_6, .keep stateRow6_3_1_7, .keep stateRow6_3_1_8, .keep stateRow6_3_1_9, .keep stateRow6_3_1_10]
def rows1_6_3_1 : List (Verdict 6) := indexedRows1_6_3_1.map (materialize literalDomain)
theorem check1_6_3_1 : checkRows direction samples1 trees1 rows1_6_3_1 = true := by
  rw [rows1_6_3_1, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_6_3_1]
  decide
theorem link1_6_3_1 : rows1_6_3_1.map Verdict.patch = rows0_6_3_1.filterMap Verdict.kept := by rfl
def indexedRows2_6_3_1 : List (RowVerdict 6) := [.keep stateRow6_3_1_1, .keep stateRow6_3_1_2, .keep stateRow6_3_1_3, .keep stateRow6_3_1_4, .keep stateRow6_3_1_5, .keep stateRow6_3_1_6, .keep stateRow6_3_1_7, .keep stateRow6_3_1_8, .keep stateRow6_3_1_9, .keep stateRow6_3_1_10]
def rows2_6_3_1 : List (Verdict 6) := indexedRows2_6_3_1.map (materialize literalDomain)
theorem check2_6_3_1 : checkRows direction samples2 trees2 rows2_6_3_1 = true := by
  rw [rows2_6_3_1, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_6_3_1]
  decide
theorem link2_6_3_1 : rows2_6_3_1.map Verdict.patch = rows1_6_3_1.filterMap Verdict.kept := by rfl
theorem final_eq6_3_1 : final6_3_1 = rows2_6_3_1.filterMap Verdict.kept := by rfl
theorem initial6_3_1 : (source6_1).map (rotatePatch 3 (hexRegion 3)) = rows0_6_3_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
