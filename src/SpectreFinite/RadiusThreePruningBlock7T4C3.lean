module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock7T4C3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_7_4_3 : List (RowVerdict 6) := [.keep stateRow7_4_3_0, .keep stateRow7_4_3_1, .keep stateRow7_4_3_2, .keep stateRow7_4_3_3, .keep stateRow7_4_3_4, .keep stateRow7_4_3_5, .keep stateRow7_4_3_6, .keep stateRow7_4_3_7, .keep stateRow7_4_3_8, .keep stateRow7_4_3_9, .keep stateRow7_4_3_10, .keep stateRow7_4_3_11]
def rows0_7_4_3 : List (Verdict 6) := indexedRows0_7_4_3.map (materialize literalDomain)
theorem check0_7_4_3 : checkRows direction samples0 trees0 rows0_7_4_3 = true := by
  rw [rows0_7_4_3, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_4_3]
  decide
def indexedRows1_7_4_3 : List (RowVerdict 6) := [.keep stateRow7_4_3_0, .keep stateRow7_4_3_1, .keep stateRow7_4_3_2, .keep stateRow7_4_3_3, .keep stateRow7_4_3_4, .keep stateRow7_4_3_5, .keep stateRow7_4_3_6, .keep stateRow7_4_3_7, .keep stateRow7_4_3_8, .keep stateRow7_4_3_9, .keep stateRow7_4_3_10, .keep stateRow7_4_3_11]
def rows1_7_4_3 : List (Verdict 6) := indexedRows1_7_4_3.map (materialize literalDomain)
theorem check1_7_4_3 : checkRows direction samples1 trees1 rows1_7_4_3 = true := by
  rw [rows1_7_4_3, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_7_4_3]
  decide
theorem link1_7_4_3 : rows1_7_4_3.map Verdict.patch = rows0_7_4_3.filterMap Verdict.kept := by rfl
def indexedRows2_7_4_3 : List (RowVerdict 6) := [.keep stateRow7_4_3_0, .keep stateRow7_4_3_1, .keep stateRow7_4_3_2, .keep stateRow7_4_3_3, .keep stateRow7_4_3_4, .keep stateRow7_4_3_5, .keep stateRow7_4_3_6, .keep stateRow7_4_3_7, .keep stateRow7_4_3_8, .keep stateRow7_4_3_9, .keep stateRow7_4_3_10, .keep stateRow7_4_3_11]
def rows2_7_4_3 : List (Verdict 6) := indexedRows2_7_4_3.map (materialize literalDomain)
theorem check2_7_4_3 : checkRows direction samples2 trees2 rows2_7_4_3 = true := by
  rw [rows2_7_4_3, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_7_4_3]
  decide
theorem link2_7_4_3 : rows2_7_4_3.map Verdict.patch = rows1_7_4_3.filterMap Verdict.kept := by rfl
theorem final_eq7_4_3 : final7_4_3 = rows2_7_4_3.filterMap Verdict.kept := by rfl
theorem initial7_4_3 : (source7_3).map (rotatePatch 4 (hexRegion 3)) = rows0_7_4_3.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
