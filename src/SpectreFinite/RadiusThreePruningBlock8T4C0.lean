module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock8T4C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_4_0_8 : List State := [(7,2),(7,4),(6,3),(2,2),(6,1),(4,1),(0,2),(1,1),(0,1),(7,0),(7,3),(5,2),(5,0),(4,5),(1,0),(4,4),(6,4),(1,2),(8,4),(0,0),(7,2),(4,0),(7,5),(0,3),(8,1),(1,5),(6,1),(5,1),(4,2),(5,3),(8,5),(7,0),(8,3),(7,4),(6,3),(7,2),(7,4)]
def stateRow8_4_0_9 : List State := [(4,4),(1,4),(0,5),(2,4),(7,1),(7,5),(6,0),(7,1),(6,5),(8,0),(7,3),(8,2),(5,0),(4,5),(7,0),(5,4),(6,4),(1,2),(8,4),(0,0),(7,2),(7,4),(7,5),(0,3),(8,1),(1,5),(6,1),(4,1),(4,2),(5,3),(5,5),(7,0),(7,3),(1,4),(0,5),(4,4),(6,4)]
def indexedRows0_8_4_0 : List (RowVerdict 6) := [.keep stateRow8_4_0_0, .keep stateRow8_4_0_1, .keep stateRow8_4_0_2, .keep stateRow8_4_0_3, .keep stateRow8_4_0_4, .keep stateRow8_4_0_5, .keep stateRow8_4_0_6, .keep stateRow8_4_0_7, .keep stateRow8_4_0_8, .keep stateRow8_4_0_9, .keep stateRow8_4_0_10, .keep stateRow8_4_0_11]
def rows0_8_4_0 : List (Verdict 6) := indexedRows0_8_4_0.map (materialize literalDomain)
theorem check0_8_4_0 : checkRows direction samples0 trees0 rows0_8_4_0 = true := by
  rw [rows0_8_4_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_4_0]
  decide
def indexedRows1_8_4_0 : List (RowVerdict 6) := [.keep stateRow8_4_0_0, .keep stateRow8_4_0_1, .keep stateRow8_4_0_2, .keep stateRow8_4_0_3, .keep stateRow8_4_0_4, .keep stateRow8_4_0_5, .keep stateRow8_4_0_6, .keep stateRow8_4_0_7, .keep stateRow8_4_0_8, .reject stateRow8_4_0_9 4, .keep stateRow8_4_0_10, .keep stateRow8_4_0_11]
def rows1_8_4_0 : List (Verdict 6) := indexedRows1_8_4_0.map (materialize literalDomain)
theorem check1_8_4_0 : checkRows direction samples1 trees1 rows1_8_4_0 = true := by
  rw [rows1_8_4_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_8_4_0]
  decide
theorem link1_8_4_0 : rows1_8_4_0.map Verdict.patch = rows0_8_4_0.filterMap Verdict.kept := by rfl
def indexedRows2_8_4_0 : List (RowVerdict 6) := [.keep stateRow8_4_0_0, .keep stateRow8_4_0_1, .keep stateRow8_4_0_2, .keep stateRow8_4_0_3, .keep stateRow8_4_0_4, .keep stateRow8_4_0_5, .keep stateRow8_4_0_6, .keep stateRow8_4_0_7, .reject stateRow8_4_0_8 0, .keep stateRow8_4_0_10, .keep stateRow8_4_0_11]
def rows2_8_4_0 : List (Verdict 6) := indexedRows2_8_4_0.map (materialize literalDomain)
theorem check2_8_4_0 : checkRows direction samples2 trees2 rows2_8_4_0 = true := by
  rw [rows2_8_4_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_8_4_0]
  decide
theorem link2_8_4_0 : rows2_8_4_0.map Verdict.patch = rows1_8_4_0.filterMap Verdict.kept := by rfl
theorem final_eq8_4_0 : final8_4_0 = rows2_8_4_0.filterMap Verdict.kept := by rfl
theorem initial8_4_0 : (source8_0).map (rotatePatch 4 (hexRegion 3)) = rows0_8_4_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
