module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock4T3C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_4_3_1 : List (RowVerdict 6) := [.keep stateRow4_3_1_0, .keep stateRow4_3_1_1, .keep stateRow4_3_1_2, .keep stateRow4_3_1_3, .keep stateRow4_3_1_4, .keep stateRow4_3_1_5, .keep stateRow4_3_1_6, .keep stateRow4_3_1_7, .keep stateRow4_3_1_8, .keep stateRow4_3_1_9]
def rows0_4_3_1 : List (Verdict 6) := indexedRows0_4_3_1.map (materialize literalDomain)
theorem check0_4_3_1 : checkRows direction samples0 trees0 rows0_4_3_1 = true := by
  rw [rows0_4_3_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_4_3_1]
  decide
def indexedRows1_4_3_1 : List (RowVerdict 6) := [.keep stateRow4_3_1_0, .keep stateRow4_3_1_1, .keep stateRow4_3_1_2, .keep stateRow4_3_1_3, .keep stateRow4_3_1_4, .keep stateRow4_3_1_5, .keep stateRow4_3_1_6, .keep stateRow4_3_1_7, .keep stateRow4_3_1_8, .keep stateRow4_3_1_9]
def rows1_4_3_1 : List (Verdict 6) := indexedRows1_4_3_1.map (materialize literalDomain)
theorem check1_4_3_1 : checkRows direction samples1 trees1 rows1_4_3_1 = true := by
  rw [rows1_4_3_1, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_4_3_1]
  decide
theorem link1_4_3_1 : rows1_4_3_1.map Verdict.patch = rows0_4_3_1.filterMap Verdict.kept := by rfl
def indexedRows2_4_3_1 : List (RowVerdict 6) := [.keep stateRow4_3_1_0, .keep stateRow4_3_1_1, .keep stateRow4_3_1_2, .keep stateRow4_3_1_3, .keep stateRow4_3_1_4, .keep stateRow4_3_1_5, .keep stateRow4_3_1_6, .keep stateRow4_3_1_7, .keep stateRow4_3_1_8, .keep stateRow4_3_1_9]
def rows2_4_3_1 : List (Verdict 6) := indexedRows2_4_3_1.map (materialize literalDomain)
theorem check2_4_3_1 : checkRows direction samples2 trees2 rows2_4_3_1 = true := by
  rw [rows2_4_3_1, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_4_3_1]
  decide
theorem link2_4_3_1 : rows2_4_3_1.map Verdict.patch = rows1_4_3_1.filterMap Verdict.kept := by rfl
theorem final_eq4_3_1 : final4_3_1 = rows2_4_3_1.filterMap Verdict.kept := by rfl
theorem initial4_3_1 : (source4_1).map (rotatePatch 3 (hexRegion 3)) = rows0_4_3_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
