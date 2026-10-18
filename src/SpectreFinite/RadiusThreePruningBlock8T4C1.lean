module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock8T4C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_8_4_1 : List (RowVerdict 6) := [.keep stateRow8_4_1_0, .keep stateRow8_4_1_1, .keep stateRow8_4_1_2, .keep stateRow8_4_1_3, .keep stateRow8_4_1_4, .keep stateRow8_4_1_5, .keep stateRow8_4_1_6, .keep stateRow8_4_1_7, .keep stateRow8_4_1_8, .keep stateRow8_4_1_9, .keep stateRow8_4_1_10, .keep stateRow8_4_1_11]
def rows0_8_4_1 : List (Verdict 6) := indexedRows0_8_4_1.map (materialize literalDomain)
theorem check0_8_4_1 : checkRows direction samples0 trees0 rows0_8_4_1 = true := by
  rw [rows0_8_4_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_4_1]
  decide
def indexedRows1_8_4_1 : List (RowVerdict 6) := [.keep stateRow8_4_1_0, .keep stateRow8_4_1_1, .keep stateRow8_4_1_2, .keep stateRow8_4_1_3, .keep stateRow8_4_1_4, .keep stateRow8_4_1_5, .keep stateRow8_4_1_6, .keep stateRow8_4_1_7, .keep stateRow8_4_1_8, .keep stateRow8_4_1_9, .keep stateRow8_4_1_10, .keep stateRow8_4_1_11]
def rows1_8_4_1 : List (Verdict 6) := indexedRows1_8_4_1.map (materialize literalDomain)
theorem check1_8_4_1 : checkRows direction samples1 trees1 rows1_8_4_1 = true := by
  rw [rows1_8_4_1, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_8_4_1]
  decide
theorem link1_8_4_1 : rows1_8_4_1.map Verdict.patch = rows0_8_4_1.filterMap Verdict.kept := by rfl
def indexedRows2_8_4_1 : List (RowVerdict 6) := [.keep stateRow8_4_1_0, .keep stateRow8_4_1_1, .keep stateRow8_4_1_2, .keep stateRow8_4_1_3, .keep stateRow8_4_1_4, .keep stateRow8_4_1_5, .keep stateRow8_4_1_6, .keep stateRow8_4_1_7, .keep stateRow8_4_1_8, .keep stateRow8_4_1_9, .keep stateRow8_4_1_10, .keep stateRow8_4_1_11]
def rows2_8_4_1 : List (Verdict 6) := indexedRows2_8_4_1.map (materialize literalDomain)
theorem check2_8_4_1 : checkRows direction samples2 trees2 rows2_8_4_1 = true := by
  rw [rows2_8_4_1, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_8_4_1]
  decide
theorem link2_8_4_1 : rows2_8_4_1.map Verdict.patch = rows1_8_4_1.filterMap Verdict.kept := by rfl
theorem final_eq8_4_1 : final8_4_1 = rows2_8_4_1.filterMap Verdict.kept := by rfl
theorem initial8_4_1 : (source8_1).map (rotatePatch 4 (hexRegion 3)) = rows0_8_4_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
