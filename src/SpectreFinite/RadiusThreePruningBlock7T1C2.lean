module

public import SpectreFinite.RadiusThreePruningTrees
public import SpectreFinite.RadiusThreePruningIndexedSignatures
public import SpectreFinite.RadiusThreePruningSourceSlices
public import SpectreFinite.RadiusThreePruningLiteralBlock7T1C2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow7_1_2_9 : List State := [(0,4),(5,4),(6,4),(1,2),(7,0),(4,3),(3,5),(0,3),(4,1),(4,4),(1,4),(0,5),(2,4),(1,3),(5,2),(7,1),(7,5),(6,0),(7,1),(6,5),(0,4),(5,4),(7,3),(8,2),(5,0),(4,5),(7,0),(4,3),(1,2),(8,4),(0,0),(7,2),(7,4),(8,1),(1,5),(6,1),(4,1)]
def indexedRows0_7_1_2 : List (RowVerdict 6) := [.keep stateRow7_1_2_0, .keep stateRow7_1_2_1, .keep stateRow7_1_2_2, .keep stateRow7_1_2_3, .keep stateRow7_1_2_4, .keep stateRow7_1_2_5, .keep stateRow7_1_2_6, .keep stateRow7_1_2_7, .keep stateRow7_1_2_8, .keep stateRow7_1_2_9, .keep stateRow7_1_2_10, .keep stateRow7_1_2_11]
def rows0_7_1_2 : List (Verdict 6) := indexedRows0_7_1_2.map (materialize literalDomain)
theorem check0_7_1_2 : checkRows direction samples0 trees0 rows0_7_1_2 = true := by
  rw [rows0_7_1_2, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_7_1_2]
  decide
def indexedRows1_7_1_2 : List (RowVerdict 6) := [.keep stateRow7_1_2_0, .keep stateRow7_1_2_1, .keep stateRow7_1_2_2, .keep stateRow7_1_2_3, .keep stateRow7_1_2_4, .keep stateRow7_1_2_5, .keep stateRow7_1_2_6, .keep stateRow7_1_2_7, .keep stateRow7_1_2_8, .reject stateRow7_1_2_9 3, .keep stateRow7_1_2_10, .keep stateRow7_1_2_11]
def rows1_7_1_2 : List (Verdict 6) := indexedRows1_7_1_2.map (materialize literalDomain)
theorem check1_7_1_2 : checkRows direction samples1 trees1 rows1_7_1_2 = true := by
  rw [rows1_7_1_2, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_7_1_2]
  decide
theorem link1_7_1_2 : rows1_7_1_2.map Verdict.patch = rows0_7_1_2.filterMap Verdict.kept := by rfl
def indexedRows2_7_1_2 : List (RowVerdict 6) := [.keep stateRow7_1_2_0, .keep stateRow7_1_2_1, .keep stateRow7_1_2_2, .keep stateRow7_1_2_3, .keep stateRow7_1_2_4, .keep stateRow7_1_2_5, .keep stateRow7_1_2_6, .keep stateRow7_1_2_7, .keep stateRow7_1_2_8, .keep stateRow7_1_2_10, .keep stateRow7_1_2_11]
def rows2_7_1_2 : List (Verdict 6) := indexedRows2_7_1_2.map (materialize literalDomain)
theorem check2_7_1_2 : checkRows direction samples2 trees2 rows2_7_1_2 = true := by
  rw [rows2_7_1_2, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_7_1_2]
  decide
theorem link2_7_1_2 : rows2_7_1_2.map Verdict.patch = rows1_7_1_2.filterMap Verdict.kept := by rfl
theorem final_eq7_1_2 : final7_1_2 = rows2_7_1_2.filterMap Verdict.kept := by rfl
theorem initial7_1_2 : (source7_2).map (rotatePatch 1 (hexRegion 3)) = rows0_7_1_2.map Verdict.patch := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
