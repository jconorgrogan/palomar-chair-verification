module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock7T2C1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_2_1_4 : List State := [(5,2),(8,0),(8,3),(5,5),(0,4),(5,4),(1,4),(0,5),(4,4),(7,0),(4,3),(7,5),(6,0),(7,1),(7,5),(7,2),(7,4),(6,3),(7,2),(4,0),(7,3),(4,2),(4,1),(0,2),(1,1),(5,1),(0,1),(6,2),(5,2),(8,0),(8,3),(5,5),(1,0),(8,4),(1,4),(0,5),(4,4)]
def indexedRows0_7_2_1 : List (RowVerdict 6) := [.keep stateRow7_2_1_0, .keep stateRow7_2_1_1, .keep stateRow7_2_1_2, .keep stateRow7_2_1_3, .keep stateRow7_2_1_4, .keep stateRow7_2_1_5, .keep stateRow7_2_1_6, .keep stateRow7_2_1_7, .keep stateRow7_2_1_8, .keep stateRow7_2_1_9, .keep stateRow7_2_1_10, .keep stateRow7_2_1_11]
def rows0_7_2_1 : List (Verdict 6) := indexedRows0_7_2_1.map (materialize literalDomain)
theorem check0_7_2_1 : checkRows direction samples0 trees0 rows0_7_2_1 = true := by
  rw [rows0_7_2_1, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_2_1]
  decide
def indexedRows1_7_2_1 : List (RowVerdict 6) := [.keep stateRow7_2_1_0, .keep stateRow7_2_1_1, .keep stateRow7_2_1_2, .keep stateRow7_2_1_3, .reject stateRow7_2_1_4 1, .keep stateRow7_2_1_5, .keep stateRow7_2_1_6, .keep stateRow7_2_1_7, .keep stateRow7_2_1_8, .keep stateRow7_2_1_9, .keep stateRow7_2_1_10, .keep stateRow7_2_1_11]
def rows1_7_2_1 : List (Verdict 6) := indexedRows1_7_2_1.map (materialize literalDomain)
theorem check1_7_2_1 : checkRows direction samples1 trees1 rows1_7_2_1 = true := by
  rw [rows1_7_2_1, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_7_2_1]
  decide
theorem link1_7_2_1 : rows1_7_2_1.map Verdict.patch = rows0_7_2_1.filterMap Verdict.kept := by rfl
def indexedRows2_7_2_1 : List (RowVerdict 6) := [.keep stateRow7_2_1_0, .keep stateRow7_2_1_1, .keep stateRow7_2_1_2, .keep stateRow7_2_1_3, .keep stateRow7_2_1_5, .keep stateRow7_2_1_6, .keep stateRow7_2_1_7, .keep stateRow7_2_1_8, .keep stateRow7_2_1_9, .keep stateRow7_2_1_10, .keep stateRow7_2_1_11]
def rows2_7_2_1 : List (Verdict 6) := indexedRows2_7_2_1.map (materialize literalDomain)
theorem check2_7_2_1 : checkRows direction samples2 trees2 rows2_7_2_1 = true := by
  rw [rows2_7_2_1, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_7_2_1]
  decide
theorem link2_7_2_1 : rows2_7_2_1.map Verdict.patch = rows1_7_2_1.filterMap Verdict.kept := by rfl
theorem final_eq7_2_1 : final7_2_1 = rows2_7_2_1.filterMap Verdict.kept := by rfl
theorem initial7_2_1 : (source7_1).map (rotatePatch 2 (hexRegion 3)) = rows0_7_2_1.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
