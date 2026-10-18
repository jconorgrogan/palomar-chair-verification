module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock0T4C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_4_0_4 : List State := [(6,4),(1,2),(7,4),(6,3),(3,5),(0,3),(4,1),(0,2),(1,1),(0,5),(2,4),(1,3),(5,2),(8,0),(8,3),(6,0),(7,1),(6,5),(0,4),(5,4),(1,4),(0,5),(5,0),(4,5),(7,0),(4,3),(7,5),(6,0),(0,0),(7,2),(7,4),(6,3),(7,2),(6,1),(4,1),(0,2),(1,1)]
def indexedRows0_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_2, .keep stateRow0_4_0_3, .reject stateRow0_4_0_4 2, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_7, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows0_0_4_0 : List (Verdict 6) := indexedRows0_0_4_0.map (materialize literalDomain)
theorem check0_0_4_0 : checkRows direction samples0 trees0 rows0_0_4_0 = true := by
  rw [rows0_0_4_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_0_4_0]
  decide
def indexedRows1_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_2, .keep stateRow0_4_0_3, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_7, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows1_0_4_0 : List (Verdict 6) := indexedRows1_0_4_0.map (materialize literalDomain)
theorem check1_0_4_0 : checkRows direction samples1 trees1 rows1_0_4_0 = true := by
  rw [rows1_0_4_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_0_4_0]
  decide
theorem link1_0_4_0 : rows1_0_4_0.map Verdict.patch = rows0_0_4_0.filterMap Verdict.kept := by rfl
def indexedRows2_0_4_0 : List (RowVerdict 6) := [.keep stateRow0_4_0_0, .keep stateRow0_4_0_1, .keep stateRow0_4_0_2, .keep stateRow0_4_0_3, .keep stateRow0_4_0_5, .keep stateRow0_4_0_6, .keep stateRow0_4_0_7, .keep stateRow0_4_0_8, .keep stateRow0_4_0_9, .keep stateRow0_4_0_10, .keep stateRow0_4_0_11]
def rows2_0_4_0 : List (Verdict 6) := indexedRows2_0_4_0.map (materialize literalDomain)
theorem check2_0_4_0 : checkRows direction samples2 trees2 rows2_0_4_0 = true := by
  rw [rows2_0_4_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_0_4_0]
  decide
theorem link2_0_4_0 : rows2_0_4_0.map Verdict.patch = rows1_0_4_0.filterMap Verdict.kept := by rfl
theorem final_eq0_4_0 : final0_4_0 = rows2_0_4_0.filterMap Verdict.kept := by rfl
theorem initial0_4_0 : (source0_0).map (rotatePatch 4 (hexRegion 3)) = rows0_0_4_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
