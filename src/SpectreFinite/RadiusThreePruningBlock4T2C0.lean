module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock4T2C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow4_2_0_3 : List State := [(5,5),(7,0),(7,3),(5,2),(0,5),(4,4),(6,4),(1,2),(8,4),(6,0),(7,1),(7,5),(0,3),(8,1),(1,5),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(5,5),(1,0),(2,1),(0,2),(1,1),(4,4),(0,0),(3,2),(4,0)]
def stateRow4_2_0_10 : List State := [(5,5),(7,0),(2,3),(0,2),(0,5),(4,4),(6,4),(1,2),(4,0),(6,0),(7,1),(7,5),(0,3),(5,1),(0,1),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(1,0),(5,1),(0,1),(6,2),(7,4),(1,3),(8,2),(8,5),(1,0),(7,1),(6,5),(0,4),(8,2),(5,0),(4,5),(7,0)]
def indexedRows0_4_2_0 : List (RowVerdict 6) := [.keep stateRow4_2_0_0, .keep stateRow4_2_0_1, .keep stateRow4_2_0_2, .reject stateRow4_2_0_3 0, .keep stateRow4_2_0_4, .keep stateRow4_2_0_5, .keep stateRow4_2_0_6, .keep stateRow4_2_0_7, .keep stateRow4_2_0_8, .keep stateRow4_2_0_9, .reject stateRow4_2_0_10 0, .keep stateRow4_2_0_11]
def rows0_4_2_0 : List (Verdict 6) := indexedRows0_4_2_0.map (materialize literalDomain)
theorem check0_4_2_0 : checkRows direction samples0 trees0 rows0_4_2_0 = true := by
  rw [rows0_4_2_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_4_2_0]
  decide
def indexedRows1_4_2_0 : List (RowVerdict 6) := [.keep stateRow4_2_0_0, .keep stateRow4_2_0_1, .keep stateRow4_2_0_2, .keep stateRow4_2_0_4, .keep stateRow4_2_0_5, .keep stateRow4_2_0_6, .keep stateRow4_2_0_7, .keep stateRow4_2_0_8, .keep stateRow4_2_0_9, .keep stateRow4_2_0_11]
def rows1_4_2_0 : List (Verdict 6) := indexedRows1_4_2_0.map (materialize literalDomain)
theorem check1_4_2_0 : checkRows direction samples1 trees1 rows1_4_2_0 = true := by
  rw [rows1_4_2_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_4_2_0]
  decide
theorem link1_4_2_0 : rows1_4_2_0.map Verdict.patch = rows0_4_2_0.filterMap Verdict.kept := by rfl
def indexedRows2_4_2_0 : List (RowVerdict 6) := [.keep stateRow4_2_0_0, .keep stateRow4_2_0_1, .keep stateRow4_2_0_2, .keep stateRow4_2_0_4, .keep stateRow4_2_0_5, .keep stateRow4_2_0_6, .keep stateRow4_2_0_7, .keep stateRow4_2_0_8, .keep stateRow4_2_0_9, .keep stateRow4_2_0_11]
def rows2_4_2_0 : List (Verdict 6) := indexedRows2_4_2_0.map (materialize literalDomain)
theorem check2_4_2_0 : checkRows direction samples2 trees2 rows2_4_2_0 = true := by
  rw [rows2_4_2_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_4_2_0]
  decide
theorem link2_4_2_0 : rows2_4_2_0.map Verdict.patch = rows1_4_2_0.filterMap Verdict.kept := by rfl
theorem final_eq4_2_0 : final4_2_0 = rows2_4_2_0.filterMap Verdict.kept := by rfl
theorem initial4_2_0 : (source4_0).map (rotatePatch 2 (hexRegion 3)) = rows0_4_2_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
