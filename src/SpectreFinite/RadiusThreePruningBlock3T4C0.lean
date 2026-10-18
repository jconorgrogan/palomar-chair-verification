module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock3T4C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_3_4_0 : List (RowVerdict 6) := [.keep stateRow3_4_0_0, .keep stateRow3_4_0_1]
def rows0_3_4_0 : List (Verdict 6) := indexedRows0_3_4_0.map (materialize literalDomain)
theorem check0_3_4_0 : checkRows direction samples0 trees0 rows0_3_4_0 = true := by
  rw [rows0_3_4_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_3_4_0]
  decide
def indexedRows1_3_4_0 : List (RowVerdict 6) := [.keep stateRow3_4_0_0, .keep stateRow3_4_0_1]
def rows1_3_4_0 : List (Verdict 6) := indexedRows1_3_4_0.map (materialize literalDomain)
theorem check1_3_4_0 : checkRows direction samples1 trees1 rows1_3_4_0 = true := by
  rw [rows1_3_4_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_3_4_0]
  decide
theorem link1_3_4_0 : rows1_3_4_0.map Verdict.patch = rows0_3_4_0.filterMap Verdict.kept := by rfl
def indexedRows2_3_4_0 : List (RowVerdict 6) := [.keep stateRow3_4_0_0, .keep stateRow3_4_0_1]
def rows2_3_4_0 : List (Verdict 6) := indexedRows2_3_4_0.map (materialize literalDomain)
theorem check2_3_4_0 : checkRows direction samples2 trees2 rows2_3_4_0 = true := by
  rw [rows2_3_4_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_3_4_0]
  decide
theorem link2_3_4_0 : rows2_3_4_0.map Verdict.patch = rows1_3_4_0.filterMap Verdict.kept := by rfl
theorem final_eq3_4_0 : final3_4_0 = rows2_3_4_0.filterMap Verdict.kept := by rfl
theorem initial3_4_0 : (source3_0).map (rotatePatch 4 (hexRegion 3)) = rows0_3_4_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
