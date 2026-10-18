module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock0T4C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_4_1_2 : List State := [(0,3),(5,1),(0,1),(6,2),(4,2),(5,3),(8,5),(1,0),(7,1),(6,2),(7,4),(1,3),(8,2),(8,0),(7,3),(1,0),(7,1),(6,5),(0,4),(5,4),(6,4),(1,2),(5,0),(4,5),(7,0),(4,3),(7,5),(0,3),(0,0),(7,2),(7,4),(6,3),(2,2),(6,1),(4,1),(0,2),(1,1)]
def indexedRows0_0_4_1 : List (RowVerdict 6) := [.keep stateRow0_4_1_0, .keep stateRow0_4_1_1, .reject stateRow0_4_1_2 2, .keep stateRow0_4_1_3, .keep stateRow0_4_1_4, .keep stateRow0_4_1_5, .keep stateRow0_4_1_6, .keep stateRow0_4_1_7, .keep stateRow0_4_1_8, .keep stateRow0_4_1_9]
def rows0_0_4_1 : List (Verdict 6) := indexedRows0_0_4_1.map (materialize literalDomain)
theorem check0_0_4_1 : checkRows direction samples0 trees0 rows0_0_4_1 = true := by
  rw [rows0_0_4_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_0_4_1]
  decide
def indexedRows1_0_4_1 : List (RowVerdict 6) := [.keep stateRow0_4_1_0, .keep stateRow0_4_1_1, .keep stateRow0_4_1_3, .keep stateRow0_4_1_4, .keep stateRow0_4_1_5, .keep stateRow0_4_1_6, .keep stateRow0_4_1_7, .keep stateRow0_4_1_8, .keep stateRow0_4_1_9]
def rows1_0_4_1 : List (Verdict 6) := indexedRows1_0_4_1.map (materialize literalDomain)
theorem check1_0_4_1 : checkRows direction samples1 trees1 rows1_0_4_1 = true := by
  rw [rows1_0_4_1, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_0_4_1]
  decide
theorem link1_0_4_1 : rows1_0_4_1.map Verdict.patch = rows0_0_4_1.filterMap Verdict.kept := by rfl
def indexedRows2_0_4_1 : List (RowVerdict 6) := [.keep stateRow0_4_1_0, .keep stateRow0_4_1_1, .keep stateRow0_4_1_3, .keep stateRow0_4_1_4, .keep stateRow0_4_1_5, .keep stateRow0_4_1_6, .keep stateRow0_4_1_7, .keep stateRow0_4_1_8, .keep stateRow0_4_1_9]
def rows2_0_4_1 : List (Verdict 6) := indexedRows2_0_4_1.map (materialize literalDomain)
theorem check2_0_4_1 : checkRows direction samples2 trees2 rows2_0_4_1 = true := by
  rw [rows2_0_4_1, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_0_4_1]
  decide
theorem link2_0_4_1 : rows2_0_4_1.map Verdict.patch = rows1_0_4_1.filterMap Verdict.kept := by rfl
theorem final_eq0_4_1 : final0_4_1 = rows2_0_4_1.filterMap Verdict.kept := by rfl
theorem initial0_4_1 : (source0_1).map (rotatePatch 4 (hexRegion 3)) = rows0_0_4_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
