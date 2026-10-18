module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock1T1C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_1_1_0 : List (RowVerdict 6) := [.keep stateRow1_1_0_0, .keep stateRow1_1_0_1, .keep stateRow1_1_0_2, .keep stateRow1_1_0_3, .keep stateRow1_1_0_4, .keep stateRow1_1_0_5, .keep stateRow1_1_0_6, .keep stateRow1_1_0_7, .keep stateRow1_1_0_8, .keep stateRow1_1_0_9, .keep stateRow1_1_0_10, .keep stateRow1_1_0_11]
def rows0_1_1_0 : List (Verdict 6) := indexedRows0_1_1_0.map (materialize literalDomain)
theorem check0_1_1_0 : checkRows direction samples0 trees0 rows0_1_1_0 = true := by
  rw [rows0_1_1_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_1_1_0]
  decide
def indexedRows1_1_1_0 : List (RowVerdict 6) := [.keep stateRow1_1_0_0, .keep stateRow1_1_0_1, .keep stateRow1_1_0_2, .keep stateRow1_1_0_3, .keep stateRow1_1_0_4, .keep stateRow1_1_0_5, .keep stateRow1_1_0_6, .keep stateRow1_1_0_7, .keep stateRow1_1_0_8, .keep stateRow1_1_0_9, .keep stateRow1_1_0_10, .keep stateRow1_1_0_11]
def rows1_1_1_0 : List (Verdict 6) := indexedRows1_1_1_0.map (materialize literalDomain)
theorem check1_1_1_0 : checkRows direction samples1 trees1 rows1_1_1_0 = true := by
  rw [rows1_1_1_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_1_1_0]
  decide
theorem link1_1_1_0 : rows1_1_1_0.map Verdict.patch = rows0_1_1_0.filterMap Verdict.kept := by rfl
def indexedRows2_1_1_0 : List (RowVerdict 6) := [.keep stateRow1_1_0_0, .keep stateRow1_1_0_1, .keep stateRow1_1_0_2, .keep stateRow1_1_0_3, .keep stateRow1_1_0_4, .keep stateRow1_1_0_5, .keep stateRow1_1_0_6, .keep stateRow1_1_0_7, .keep stateRow1_1_0_8, .keep stateRow1_1_0_9, .keep stateRow1_1_0_10, .keep stateRow1_1_0_11]
def rows2_1_1_0 : List (Verdict 6) := indexedRows2_1_1_0.map (materialize literalDomain)
theorem check2_1_1_0 : checkRows direction samples2 trees2 rows2_1_1_0 = true := by
  rw [rows2_1_1_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_1_1_0]
  decide
theorem link2_1_1_0 : rows2_1_1_0.map Verdict.patch = rows1_1_1_0.filterMap Verdict.kept := by rfl
theorem final_eq1_1_0 : final1_1_0 = rows2_1_1_0.filterMap Verdict.kept := by rfl
theorem initial1_1_0 : (source1_0).map (rotatePatch 1 (hexRegion 3)) = rows0_1_1_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
