module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock1T0C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_1_0_2 : List (RowVerdict 6) := [.keep stateRow1_0_2_0, .keep stateRow1_0_2_1]
def rows0_1_0_2 : List (Verdict 6) := indexedRows0_1_0_2.map (materialize literalDomain)
theorem check0_1_0_2 : checkRows direction samples0 trees0 rows0_1_0_2 = true := by
  rw [rows0_1_0_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_1_0_2]
  decide
def indexedRows1_1_0_2 : List (RowVerdict 6) := [.keep stateRow1_0_2_0, .keep stateRow1_0_2_1]
def rows1_1_0_2 : List (Verdict 6) := indexedRows1_1_0_2.map (materialize literalDomain)
theorem check1_1_0_2 : checkRows direction samples1 trees1 rows1_1_0_2 = true := by
  rw [rows1_1_0_2, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_1_0_2]
  decide
theorem link1_1_0_2 : rows1_1_0_2.map Verdict.patch = rows0_1_0_2.filterMap Verdict.kept := by rfl
def indexedRows2_1_0_2 : List (RowVerdict 6) := [.keep stateRow1_0_2_0, .keep stateRow1_0_2_1]
def rows2_1_0_2 : List (Verdict 6) := indexedRows2_1_0_2.map (materialize literalDomain)
theorem check2_1_0_2 : checkRows direction samples2 trees2 rows2_1_0_2 = true := by
  rw [rows2_1_0_2, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_1_0_2]
  decide
theorem link2_1_0_2 : rows2_1_0_2.map Verdict.patch = rows1_1_0_2.filterMap Verdict.kept := by rfl
theorem final_eq1_0_2 : final1_0_2 = rows2_1_0_2.filterMap Verdict.kept := by rfl
theorem initial1_0_2 : (source1_2).map (rotatePatch 0 (hexRegion 3)) = rows0_1_0_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
