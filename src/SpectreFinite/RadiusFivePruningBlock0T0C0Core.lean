module

public import SpectreFinite.RadiusFivePruningTrees
public import SpectreFinite.RadiusFivePruningIndexedSignatures
public import SpectreFinite.RadiusFivePruningLiteralBlock0T0C0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stateRow0_0_0_2 : List State := [(0,1),(6,2),(8,4),(6,4),(1,2),(8,4),(8,5),(1,0),(7,1),(7,5),(0,3),(8,1),(1,5),(6,3),(7,2),(4,0),(7,3),(4,2),(5,3),(8,5),(7,0),(0,2),(1,1),(5,1),(0,1),(6,2),(7,4),(6,3),(7,2),(7,4),(5,2),(8,0),(8,3),(5,5),(1,0),(2,1),(0,2),(1,1),(4,1),(0,2),(0,4),(5,4),(1,4),(0,5),(4,4),(0,0),(3,2),(4,0),(7,3),(5,2),(8,0),(4,3),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(1,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(0,4),(5,4),(0,0),(7,2),(7,4),(6,3),(7,2),(4,0),(4,3),(1,5),(6,1),(4,1),(0,2),(1,1),(5,1),(0,5),(2,0),(7,3),(5,2),(8,0),(8,3)]
def stateRow0_0_0_7 : List State := [(6,5),(0,4),(5,4),(6,4),(1,2),(8,4),(4,5),(7,0),(4,3),(7,5),(0,3),(8,1),(1,5),(0,0),(7,2),(7,4),(1,3),(4,2),(5,3),(5,5),(7,0),(1,5),(6,1),(8,1),(6,5),(0,4),(1,4),(0,5),(4,4),(1,4),(5,5),(7,0),(8,3),(5,5),(3,0),(2,5),(6,0),(7,1),(7,5),(6,0),(0,5),(4,4),(1,4),(0,5),(4,4),(0,0),(7,2),(4,0),(7,3),(8,2),(8,0),(7,1),(7,5),(6,0),(7,1),(1,5),(6,1),(5,1),(0,1),(6,2),(8,4),(7,3),(8,2),(5,0),(4,5),(7,0),(8,3),(8,5),(1,0),(7,1),(6,2),(8,4),(0,0),(7,2),(7,4),(1,3),(8,2),(8,0),(7,1),(1,5),(6,1),(8,1),(6,5),(0,4),(5,4),(4,5),(7,0),(8,3),(8,5),(7,0),(4,3)]
def indexedRows0_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .keep stateRow0_0_0_2, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .reject stateRow0_0_0_7 5, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows0_0_0_0 : List (Verdict 6) := indexedRows0_0_0_0.map (materialize literalDomain)
theorem check0_0_0_0 : checkRows direction samples0 trees0 rows0_0_0_0 = true := by
  rw [rows0_0_0_0, checkRows_materialize literalDomain direction samples0 leftIndices0 rightIndices0 leftSignature_index0 rightSignature_index0 trees0 indexedRows0_0_0_0]
  decide
def indexedRows1_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .reject stateRow0_0_0_2 5, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows1_0_0_0 : List (Verdict 6) := indexedRows1_0_0_0.map (materialize literalDomain)
theorem check1_0_0_0 : checkRows direction samples1 trees1 rows1_0_0_0 = true := by
  rw [rows1_0_0_0, checkRows_materialize literalDomain direction samples1 leftIndices1 rightIndices1 leftSignature_index1 rightSignature_index1 trees1 indexedRows1_0_0_0]
  decide
theorem link1_0_0_0 : rows1_0_0_0.map Verdict.patch = rows0_0_0_0.filterMap Verdict.kept := by rfl
def indexedRows2_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows2_0_0_0 : List (Verdict 6) := indexedRows2_0_0_0.map (materialize literalDomain)
theorem check2_0_0_0 : checkRows direction samples2 trees2 rows2_0_0_0 = true := by
  rw [rows2_0_0_0, checkRows_materialize literalDomain direction samples2 leftIndices2 rightIndices2 leftSignature_index2 rightSignature_index2 trees2 indexedRows2_0_0_0]
  decide
theorem link2_0_0_0 : rows2_0_0_0.map Verdict.patch = rows1_0_0_0.filterMap Verdict.kept := by rfl
def indexedRows3_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows3_0_0_0 : List (Verdict 6) := indexedRows3_0_0_0.map (materialize literalDomain)
theorem check3_0_0_0 : checkRows direction samples3 trees3 rows3_0_0_0 = true := by
  rw [rows3_0_0_0, checkRows_materialize literalDomain direction samples3 leftIndices3 rightIndices3 leftSignature_index3 rightSignature_index3 trees3 indexedRows3_0_0_0]
  decide
theorem link3_0_0_0 : rows3_0_0_0.map Verdict.patch = rows2_0_0_0.filterMap Verdict.kept := by rfl
def indexedRows4_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows4_0_0_0 : List (Verdict 6) := indexedRows4_0_0_0.map (materialize literalDomain)
theorem check4_0_0_0 : checkRows direction samples4 trees4 rows4_0_0_0 = true := by
  rw [rows4_0_0_0, checkRows_materialize literalDomain direction samples4 leftIndices4 rightIndices4 leftSignature_index4 rightSignature_index4 trees4 indexedRows4_0_0_0]
  decide
theorem link4_0_0_0 : rows4_0_0_0.map Verdict.patch = rows3_0_0_0.filterMap Verdict.kept := by rfl
def indexedRows5_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows5_0_0_0 : List (Verdict 6) := indexedRows5_0_0_0.map (materialize literalDomain)
theorem check5_0_0_0 : checkRows direction samples5 trees5 rows5_0_0_0 = true := by
  rw [rows5_0_0_0, checkRows_materialize literalDomain direction samples5 leftIndices5 rightIndices5 leftSignature_index5 rightSignature_index5 trees5 indexedRows5_0_0_0]
  decide
theorem link5_0_0_0 : rows5_0_0_0.map Verdict.patch = rows4_0_0_0.filterMap Verdict.kept := by rfl
def indexedRows6_0_0_0 : List (RowVerdict 6) := [.keep stateRow0_0_0_0, .keep stateRow0_0_0_1, .keep stateRow0_0_0_3, .keep stateRow0_0_0_4, .keep stateRow0_0_0_5, .keep stateRow0_0_0_6, .keep stateRow0_0_0_8, .keep stateRow0_0_0_9, .keep stateRow0_0_0_10, .keep stateRow0_0_0_11]
def rows6_0_0_0 : List (Verdict 6) := indexedRows6_0_0_0.map (materialize literalDomain)
theorem check6_0_0_0 : checkRows direction samples6 trees6 rows6_0_0_0 = true := by
  rw [rows6_0_0_0, checkRows_materialize literalDomain direction samples6 leftIndices6 rightIndices6 leftSignature_index6 rightSignature_index6 trees6 indexedRows6_0_0_0]
  decide
theorem link6_0_0_0 : rows6_0_0_0.map Verdict.patch = rows5_0_0_0.filterMap Verdict.kept := by rfl
theorem final_eq0_0_0 : final0_0_0 = rows6_0_0_0.filterMap Verdict.kept := by rfl

end SpectreFinite.HexSearch.RadiusFivePruning
