module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock7T3C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_7_3_0 : List (RowVerdict 6) := [.keep stateRow7_3_0_0, .keep stateRow7_3_0_1, .keep stateRow7_3_0_2, .keep stateRow7_3_0_3, .keep stateRow7_3_0_4, .keep stateRow7_3_0_5, .keep stateRow7_3_0_6, .keep stateRow7_3_0_7, .keep stateRow7_3_0_8, .keep stateRow7_3_0_9, .keep stateRow7_3_0_10, .keep stateRow7_3_0_11]
def rows0_7_3_0 : List (Verdict 6) := indexedRows0_7_3_0.map (materialize literalDomain)
theorem check0_7_3_0 : checkRows direction samples0 trees0 rows0_7_3_0 = true := by
  rw [rows0_7_3_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_3_0]
  decide
def indexedRows1_7_3_0 : List (RowVerdict 6) := [.keep stateRow7_3_0_0, .keep stateRow7_3_0_1, .keep stateRow7_3_0_2, .keep stateRow7_3_0_3, .keep stateRow7_3_0_4, .keep stateRow7_3_0_5, .keep stateRow7_3_0_6, .keep stateRow7_3_0_7, .keep stateRow7_3_0_8, .keep stateRow7_3_0_9, .keep stateRow7_3_0_10, .keep stateRow7_3_0_11]
def rows1_7_3_0 : List (Verdict 6) := indexedRows1_7_3_0.map (materialize literalDomain)
theorem check1_7_3_0 : checkRows direction samples1 trees1 rows1_7_3_0 = true := by
  rw [rows1_7_3_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_7_3_0]
  decide
theorem link1_7_3_0 : rows1_7_3_0.map Verdict.patch = rows0_7_3_0.filterMap Verdict.kept := by rfl
def indexedRows2_7_3_0 : List (RowVerdict 6) := [.keep stateRow7_3_0_0, .keep stateRow7_3_0_1, .keep stateRow7_3_0_2, .keep stateRow7_3_0_3, .keep stateRow7_3_0_4, .keep stateRow7_3_0_5, .keep stateRow7_3_0_6, .keep stateRow7_3_0_7, .keep stateRow7_3_0_8, .keep stateRow7_3_0_9, .keep stateRow7_3_0_10, .keep stateRow7_3_0_11]
def rows2_7_3_0 : List (Verdict 6) := indexedRows2_7_3_0.map (materialize literalDomain)
theorem check2_7_3_0 : checkRows direction samples2 trees2 rows2_7_3_0 = true := by
  rw [rows2_7_3_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_7_3_0]
  decide
theorem link2_7_3_0 : rows2_7_3_0.map Verdict.patch = rows1_7_3_0.filterMap Verdict.kept := by rfl
theorem final_eq7_3_0 : final7_3_0 = rows2_7_3_0.filterMap Verdict.kept := by rfl
theorem initial7_3_0 : (source7_0).map (rotatePatch 3 (hexRegion 3)) = rows0_7_3_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
