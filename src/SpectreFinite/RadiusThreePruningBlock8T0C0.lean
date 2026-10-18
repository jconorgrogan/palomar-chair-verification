module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock8T0C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow8_0_0_8 : List State := [(4,2),(5,3),(8,5),(7,0),(1,2),(7,4),(6,3),(7,2),(7,4),(0,3),(4,1),(0,2),(1,1),(8,1),(6,5),(2,4),(1,3),(5,2),(8,0),(8,3),(5,5),(7,0),(6,5),(0,4),(5,4),(1,4),(0,5),(4,4),(7,0),(4,3),(7,5),(6,0),(7,1),(7,4),(6,3),(7,2),(4,0)]
def stateRow8_0_0_9 : List State := [(7,0),(4,3),(7,5),(6,0),(7,2),(7,4),(6,3),(7,2),(4,0),(6,1),(4,1),(0,2),(1,1),(5,1),(0,1),(2,0),(7,3),(5,2),(8,0),(8,3),(5,5),(1,0),(0,1),(6,2),(8,4),(1,4),(0,5),(4,4),(1,0),(7,1),(7,5),(6,0),(7,1),(4,0),(7,3),(8,2),(5,0)]
def indexedRows0_8_0_0 : List (RowVerdict 6) := [.keep stateRow8_0_0_0, .keep stateRow8_0_0_1, .keep stateRow8_0_0_2, .keep stateRow8_0_0_3, .keep stateRow8_0_0_4, .keep stateRow8_0_0_5, .keep stateRow8_0_0_6, .keep stateRow8_0_0_7, .keep stateRow8_0_0_8, .keep stateRow8_0_0_9, .keep stateRow8_0_0_10, .keep stateRow8_0_0_11]
def rows0_8_0_0 : List (Verdict 6) := indexedRows0_8_0_0.map (materialize literalDomain)
theorem check0_8_0_0 : checkRows direction samples0 trees0 rows0_8_0_0 = true := by
  rw [rows0_8_0_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_0_0]
  decide
def indexedRows1_8_0_0 : List (RowVerdict 6) := [.keep stateRow8_0_0_0, .keep stateRow8_0_0_1, .keep stateRow8_0_0_2, .keep stateRow8_0_0_3, .keep stateRow8_0_0_4, .keep stateRow8_0_0_5, .keep stateRow8_0_0_6, .keep stateRow8_0_0_7, .keep stateRow8_0_0_8, .reject stateRow8_0_0_9 0, .keep stateRow8_0_0_10, .keep stateRow8_0_0_11]
def rows1_8_0_0 : List (Verdict 6) := indexedRows1_8_0_0.map (materialize literalDomain)
theorem check1_8_0_0 : checkRows direction samples1 trees1 rows1_8_0_0 = true := by
  rw [rows1_8_0_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_8_0_0]
  decide
theorem link1_8_0_0 : rows1_8_0_0.map Verdict.patch = rows0_8_0_0.filterMap Verdict.kept := by rfl
def indexedRows2_8_0_0 : List (RowVerdict 6) := [.keep stateRow8_0_0_0, .keep stateRow8_0_0_1, .keep stateRow8_0_0_2, .keep stateRow8_0_0_3, .keep stateRow8_0_0_4, .keep stateRow8_0_0_5, .keep stateRow8_0_0_6, .keep stateRow8_0_0_7, .reject stateRow8_0_0_8 1, .keep stateRow8_0_0_10, .keep stateRow8_0_0_11]
def rows2_8_0_0 : List (Verdict 6) := indexedRows2_8_0_0.map (materialize literalDomain)
theorem check2_8_0_0 : checkRows direction samples2 trees2 rows2_8_0_0 = true := by
  rw [rows2_8_0_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_8_0_0]
  decide
theorem link2_8_0_0 : rows2_8_0_0.map Verdict.patch = rows1_8_0_0.filterMap Verdict.kept := by rfl
theorem final_eq8_0_0 : final8_0_0 = rows2_8_0_0.filterMap Verdict.kept := by rfl
theorem initial8_0_0 : (source8_0).map (rotatePatch 0 (hexRegion 3)) = rows0_8_0_0.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
