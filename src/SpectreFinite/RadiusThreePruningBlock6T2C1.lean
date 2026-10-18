module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock6T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow6_2_1_0 : List State := [(0,5),(4,4),(6,4),(1,2),(6,0),(7,1),(7,5),(0,3),(5,1),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(6,1),(5,1),(0,1),(6,2),(7,4),(1,3),(8,2),(8,3),(8,5),(1,0),(7,1),(6,5),(0,4),(1,3),(8,2),(5,0),(4,5),(7,0),(0,4),(5,4),(0,0),(7,2)]
def indexedRows0_6_2_1 : List (RowVerdict 6) := [.reject stateRow6_2_1_0 0, .keep stateRow6_2_1_1, .keep stateRow6_2_1_2, .keep stateRow6_2_1_3, .keep stateRow6_2_1_4, .keep stateRow6_2_1_5, .keep stateRow6_2_1_6, .keep stateRow6_2_1_7, .keep stateRow6_2_1_8, .keep stateRow6_2_1_9, .keep stateRow6_2_1_10]
def rows0_6_2_1 : List (Verdict 6) := indexedRows0_6_2_1.map (materialize literalDomain)
theorem check0_6_2_1 : checkRows direction samples0 trees0 rows0_6_2_1 = true := by
  rw [rows0_6_2_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_6_2_1]
  decide
def indexedRows1_6_2_1 : List (RowVerdict 6) := [.keep stateRow6_2_1_1, .keep stateRow6_2_1_2, .keep stateRow6_2_1_3, .keep stateRow6_2_1_4, .keep stateRow6_2_1_5, .keep stateRow6_2_1_6, .keep stateRow6_2_1_7, .keep stateRow6_2_1_8, .keep stateRow6_2_1_9, .keep stateRow6_2_1_10]
def rows1_6_2_1 : List (Verdict 6) := indexedRows1_6_2_1.map (materialize literalDomain)
theorem check1_6_2_1 : checkRows direction samples1 trees1 rows1_6_2_1 = true := by
  rw [rows1_6_2_1, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_6_2_1]
  decide
theorem link1_6_2_1 : rows1_6_2_1.map Verdict.patch = rows0_6_2_1.filterMap Verdict.kept := by rfl
def indexedRows2_6_2_1 : List (RowVerdict 6) := [.keep stateRow6_2_1_1, .keep stateRow6_2_1_2, .keep stateRow6_2_1_3, .keep stateRow6_2_1_4, .keep stateRow6_2_1_5, .keep stateRow6_2_1_6, .keep stateRow6_2_1_7, .keep stateRow6_2_1_8, .keep stateRow6_2_1_9, .keep stateRow6_2_1_10]
def rows2_6_2_1 : List (Verdict 6) := indexedRows2_6_2_1.map (materialize literalDomain)
theorem check2_6_2_1 : checkRows direction samples2 trees2 rows2_6_2_1 = true := by
  rw [rows2_6_2_1, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_6_2_1]
  decide
theorem link2_6_2_1 : rows2_6_2_1.map Verdict.patch = rows1_6_2_1.filterMap Verdict.kept := by rfl
theorem final_eq6_2_1 : final6_2_1 = rows2_6_2_1.filterMap Verdict.kept := by rfl
theorem initial6_2_1 : (source6_1).map (rotatePatch 2 (hexRegion 3)) = rows0_6_2_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
