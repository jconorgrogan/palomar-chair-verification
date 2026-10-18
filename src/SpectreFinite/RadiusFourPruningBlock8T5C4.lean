module

public import SpectreFinite.RadiusFourPruningTrees
public import SpectreFinite.RadiusFourPruningIndexedSignatures
public import SpectreFinite.RadiusFourPruningSourceSlices
public import SpectreFinite.RadiusFourPruningSourceStates
public import SpectreFinite.RadiusFourPruningLiteralBlock8T5C4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def indexedRows0_8_5_4 : List (RowVerdict 6) := [.keep stateRow8_5_4_0, .keep stateRow8_5_4_1, .keep stateRow8_5_4_2, .keep stateRow8_5_4_3]
def rows0_8_5_4 : List (Verdict 6) := indexedRows0_8_5_4.map (materialize literalDomain)
theorem check0_8_5_4 : checkRows direction samples0 trees0 rows0_8_5_4 = true := by
  rw [rows0_8_5_4, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_8_5_4]
  decide
theorem final_eq8_5_4 : final8_5_4 = rows0_8_5_4.filterMap Verdict.kept := by rfl
theorem sourceRowRotation8_5_4_0 : rotatedStateRow5 sourceState8_4_0 = stateRow8_5_4_0 := by decide
theorem sourceRowRotation8_5_4_1 : rotatedStateRow5 sourceState8_4_1 = stateRow8_5_4_1 := by decide
theorem sourceRowRotation8_5_4_2 : rotatedStateRow5 sourceState8_4_2 = stateRow8_5_4_2 := by decide
theorem sourceRowRotation8_5_4_3 : rotatedStateRow5 sourceState8_4_3 = stateRow8_5_4_3 := by decide
theorem initial8_5_4 : (source8_4).map (rotatePatch 5 (hexRegion 4)) = rows0_8_5_4.map Verdict.patch := by
  rw [sourceStates8_4, sourceStateSplit8_4, rotateCanonical_map5]
  simp only [List.map_cons, List.map_nil, sourceRowRotation8_5_4_0, sourceRowRotation8_5_4_1, sourceRowRotation8_5_4_2, sourceRowRotation8_5_4_3] <;> rfl

end SpectreFinite.HexSearch.RadiusFourPruning
