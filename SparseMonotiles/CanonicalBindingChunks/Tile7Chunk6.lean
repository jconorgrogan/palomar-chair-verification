module

public import SparseMonotiles.CanonicalReferenceKeys
public import SparseMonotiles.CanonicalPermutations7
public import SparseMonotiles.Tile7Data
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def canonicalPose7_192 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, false, false, false, false], ![0, 0, 1, 1, 0, 0, 0]⟩
def canonicalBox7_192 : BoxKey 7 :=
  ⟨![0, 120960, 315840, 322560, 100800, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 121380, 316240, 322945, 101360, 108010, 114688], true⟩

theorem canonicalMatch7_192 :
    canonicalPose7_192.boxKey 188160 (referenceBox7 (!canonicalBox7_192.bump)) = canonicalBox7_192 := by decide +kernel

theorem canonicalDecode7_192 : canonicalBox7_192.toKeyData 188160 = keys7Chunk6.get ⟨0, by decide⟩ := by
  change canonicalBox7_192.toKeyData 188160 = ⟨![0, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_192 : keySolid (keys7Chunk6.get ⟨0, by decide⟩) = canonicalPose7_192.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_192 (box := canonicalBox7_192) (k := keys7Chunk6.get ⟨0, by decide⟩) (canonicalMatch7_192) (canonicalDecode7_192)

def canonicalPose7_193 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, true, true, false, false, true], ![0, 0, 2, 2, 0, 0, 1]⟩
def canonicalBox7_193 : BoxKey 7 :=
  ⟨![120960, 0, 262080, 268800, 100800, 134400, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, -560, 261632, 268310, 101360, 134785, 60080], true⟩

theorem canonicalMatch7_193 :
    canonicalPose7_193.boxKey 188160 (referenceBox7 (!canonicalBox7_193.bump)) = canonicalBox7_193 := by decide +kernel

theorem canonicalDecode7_193 : canonicalBox7_193.toKeyData 188160 = keys7Chunk6.get ⟨1, by decide⟩ := by
  change canonicalBox7_193.toKeyData 188160 = ⟨![(9 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (5 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (-1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_193 : keySolid (keys7Chunk6.get ⟨1, by decide⟩) = canonicalPose7_193.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_193 (box := canonicalBox7_193) (k := keys7Chunk6.get ⟨1, by decide⟩) (canonicalMatch7_193) (canonicalDecode7_193)

def canonicalPose7_194 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, false, true, true, false, true, false], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_194 : BoxKey 7 :=
  ⟨![67200, 114240, 376320, 268800, 100800, 53760, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 114688, 375760, 268310, 101360, 53375, 128080], false⟩

theorem canonicalMatch7_194 :
    canonicalPose7_194.boxKey 188160 (referenceBox7 (!canonicalBox7_194.bump)) = canonicalBox7_194 := by decide +kernel

theorem canonicalDecode7_194 : canonicalBox7_194.toKeyData 188160 = keys7Chunk6.get ⟨2, by decide⟩ := by
  change canonicalBox7_194.toKeyData 188160 = ⟨![(5 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (2 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (64 / 105), (671 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_194 : keySolid (keys7Chunk6.get ⟨2, by decide⟩) = canonicalPose7_194.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_194 (box := canonicalBox7_194) (k := keys7Chunk6.get ⟨2, by decide⟩) (canonicalMatch7_194) (canonicalDecode7_194)

def canonicalPose7_195 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, false, true, false, false, true, false], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_195 : BoxKey 7 :=
  ⟨![53760, 100800, 268800, 376320, 114240, 67200, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 101360, 268310, 376880, 114688, 66780, 128080], true⟩

theorem canonicalMatch7_195 :
    canonicalPose7_195.boxKey 188160 (referenceBox7 (!canonicalBox7_195.bump)) = canonicalBox7_195 := by decide +kernel

theorem canonicalDecode7_195 : canonicalBox7_195.toKeyData 188160 = keys7Chunk6.get ⟨3, by decide⟩ := by
  change canonicalBox7_195.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (3833 / 2688), (673 / 336), (64 / 105), (159 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_195 : keySolid (keys7Chunk6.get ⟨3, by decide⟩) = canonicalPose7_195.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_195 (box := canonicalBox7_195) (k := keys7Chunk6.get ⟨3, by decide⟩) (canonicalMatch7_195) (canonicalDecode7_195)

def canonicalPose7_196 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, true, false, false, true], ![0, 0, 2, 2, 0, 0, 1]⟩
def canonicalBox7_196 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 262080, 0, 120960, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 261632, 560, 121380, 60080], false⟩

theorem canonicalMatch7_196 :
    canonicalPose7_196.boxKey 188160 (referenceBox7 (!canonicalBox7_196.bump)) = canonicalBox7_196 := by decide +kernel

theorem canonicalDecode7_196 : canonicalBox7_196.toKeyData 188160 = keys7Chunk6.get ⟨4, by decide⟩ := by
  change canonicalBox7_196.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (9 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (1 / 336), (289 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_196 : keySolid (keys7Chunk6.get ⟨4, by decide⟩) = canonicalPose7_196.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_196 (box := canonicalBox7_196) (k := keys7Chunk6.get ⟨4, by decide⟩) (canonicalMatch7_196) (canonicalDecode7_196)

def canonicalPose7_197 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, false, false, false, false], ![0, 0, 1, 1, 0, 0, 0]⟩
def canonicalBox7_197 : BoxKey 7 :=
  ⟨![107520, 100800, 322560, 315840, 120960, 0, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 322945, 316240, 121380, 560, 114688], false⟩

theorem canonicalMatch7_197 :
    canonicalPose7_197.boxKey 188160 (referenceBox7 (!canonicalBox7_197.bump)) = canonicalBox7_197 := by decide +kernel

theorem canonicalDecode7_197 : canonicalBox7_197.toKeyData 188160 = keys7Chunk6.get ⟨5, by decide⟩ := by
  change canonicalBox7_197.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 0, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_197 : keySolid (keys7Chunk6.get ⟨5, by decide⟩) = canonicalPose7_197.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_197 (box := canonicalBox7_197) (k := keys7Chunk6.get ⟨5, by decide⟩) (canonicalMatch7_197) (canonicalDecode7_197)

def canonicalPose7_198 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, true, false, true, false], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_198 : BoxKey 7 :=
  ⟨![73920, 107520, 275520, 241920, 127680, 67200, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 108010, 274960, 241535, 128080, 66780, 560], false⟩

theorem canonicalMatch7_198 :
    canonicalPose7_198.boxKey 188160 (referenceBox7 (!canonicalBox7_198.bump)) = canonicalBox7_198 := by decide +kernel

theorem canonicalDecode7_198 : canonicalBox7_198.toKeyData 188160 = keys7Chunk6.get ⟨6, by decide⟩ := by
  change canonicalBox7_198.toKeyData 188160 = ⟨![(11 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (5 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_198 : keySolid (keys7Chunk6.get ⟨6, by decide⟩) = canonicalPose7_198.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_198 (box := canonicalBox7_198) (k := keys7Chunk6.get ⟨6, by decide⟩) (canonicalMatch7_198) (canonicalDecode7_198)

def canonicalPose7_199 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, true, true, false, true, true], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_199 : BoxKey 7 :=
  ⟨![67200, 127680, 241920, 275520, 107520, 73920, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 128080, 241535, 274960, 108010, 73472, -560], true⟩

theorem canonicalMatch7_199 :
    canonicalPose7_199.boxKey 188160 (referenceBox7 (!canonicalBox7_199.bump)) = canonicalBox7_199 := by decide +kernel

theorem canonicalDecode7_199 : canonicalBox7_199.toKeyData 188160 = keys7Chunk6.get ⟨7, by decide⟩ := by
  change canonicalBox7_199.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (11 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_199 : keySolid (keys7Chunk6.get ⟨7, by decide⟩) = canonicalPose7_199.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_199 (box := canonicalBox7_199) (k := keys7Chunk6.get ⟨7, by decide⟩) (canonicalMatch7_199) (canonicalDecode7_199)

def canonicalPose7_200 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, false, false, false, false, true], ![0, 0, 1, 1, 0, 0, 2]⟩
def canonicalBox7_200 : BoxKey 7 :=
  ⟨![0, 120960, 315840, 322560, 100800, 107520, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 121380, 316240, 322945, 101360, 108010, 261632], false⟩

theorem canonicalMatch7_200 :
    canonicalPose7_200.boxKey 188160 (referenceBox7 (!canonicalBox7_200.bump)) = canonicalBox7_200 := by decide +kernel

theorem canonicalDecode7_200 : canonicalBox7_200.toKeyData 188160 = keys7Chunk6.get ⟨8, by decide⟩ := by
  change canonicalBox7_200.toKeyData 188160 = ⟨![0, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (4 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_200 : keySolid (keys7Chunk6.get ⟨8, by decide⟩) = canonicalPose7_200.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_200 (box := canonicalBox7_200) (k := keys7Chunk6.get ⟨8, by decide⟩) (canonicalMatch7_200) (canonicalDecode7_200)

def canonicalPose7_201 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, true, true, false, false, false], ![0, 0, 2, 2, 0, 0, 1]⟩
def canonicalBox7_201 : BoxKey 7 :=
  ⟨![120960, 0, 262080, 268800, 100800, 134400, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 560, 261632, 268310, 101360, 134785, 316240], false⟩

theorem canonicalMatch7_201 :
    canonicalPose7_201.boxKey 188160 (referenceBox7 (!canonicalBox7_201.bump)) = canonicalBox7_201 := by decide +kernel

theorem canonicalDecode7_201 : canonicalBox7_201.toKeyData 188160 = keys7Chunk6.get ⟨9, by decide⟩ := by
  change canonicalBox7_201.toKeyData 188160 = ⟨![(9 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (5 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_201 : keySolid (keys7Chunk6.get ⟨9, by decide⟩) = canonicalPose7_201.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_201 (box := canonicalBox7_201) (k := keys7Chunk6.get ⟨9, by decide⟩) (canonicalMatch7_201) (canonicalDecode7_201)

def canonicalPose7_202 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, false, false, true, false, true, true], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_202 : BoxKey 7 :=
  ⟨![67200, 114240, 376320, 268800, 100800, 53760, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 114688, 376880, 268310, 101360, 53375, 248240], true⟩

theorem canonicalMatch7_202 :
    canonicalPose7_202.boxKey 188160 (referenceBox7 (!canonicalBox7_202.bump)) = canonicalBox7_202 := by decide +kernel

theorem canonicalDecode7_202 : canonicalBox7_202.toKeyData 188160 = keys7Chunk6.get ⟨10, by decide⟩ := by
  change canonicalBox7_202.toKeyData 188160 = ⟨![(5 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (2 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (64 / 105), (673 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_202 : keySolid (keys7Chunk6.get ⟨10, by decide⟩) = canonicalPose7_202.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_202 (box := canonicalBox7_202) (k := keys7Chunk6.get ⟨10, by decide⟩) (canonicalMatch7_202) (canonicalDecode7_202)

def canonicalPose7_203 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, false, true, true, false, true, true], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_203 : BoxKey 7 :=
  ⟨![53760, 100800, 268800, 376320, 114240, 67200, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 101360, 268310, 375760, 114688, 66780, 248240], false⟩

theorem canonicalMatch7_203 :
    canonicalPose7_203.boxKey 188160 (referenceBox7 (!canonicalBox7_203.bump)) = canonicalBox7_203 := by decide +kernel

theorem canonicalDecode7_203 : canonicalBox7_203.toKeyData 188160 = keys7Chunk6.get ⟨11, by decide⟩ := by
  change canonicalBox7_203.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (3833 / 2688), (671 / 336), (64 / 105), (159 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_203 : keySolid (keys7Chunk6.get ⟨11, by decide⟩) = canonicalPose7_203.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_203 (box := canonicalBox7_203) (k := keys7Chunk6.get ⟨11, by decide⟩) (canonicalMatch7_203) (canonicalDecode7_203)

def canonicalPose7_204 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, true, true, false, false], ![0, 0, 2, 2, 0, 0, 1]⟩
def canonicalBox7_204 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 262080, 0, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 261632, -560, 121380, 316240], true⟩

theorem canonicalMatch7_204 :
    canonicalPose7_204.boxKey 188160 (referenceBox7 (!canonicalBox7_204.bump)) = canonicalBox7_204 := by decide +kernel

theorem canonicalDecode7_204 : canonicalBox7_204.toKeyData 188160 = keys7Chunk6.get ⟨12, by decide⟩ := by
  change canonicalBox7_204.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (289 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_204 : keySolid (keys7Chunk6.get ⟨12, by decide⟩) = canonicalPose7_204.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_204 (box := canonicalBox7_204) (k := keys7Chunk6.get ⟨12, by decide⟩) (canonicalMatch7_204) (canonicalDecode7_204)

def canonicalPose7_205 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, false, false, true, true], ![0, 0, 1, 1, 0, 0, 2]⟩
def canonicalBox7_205 : BoxKey 7 :=
  ⟨![107520, 100800, 322560, 315840, 120960, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 322945, 316240, 121380, -560, 261632], true⟩

theorem canonicalMatch7_205 :
    canonicalPose7_205.boxKey 188160 (referenceBox7 (!canonicalBox7_205.bump)) = canonicalBox7_205 := by decide +kernel

theorem canonicalDecode7_205 : canonicalBox7_205.toKeyData 188160 = keys7Chunk6.get ⟨13, by decide⟩ := by
  change canonicalBox7_205.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_205 : keySolid (keys7Chunk6.get ⟨13, by decide⟩) = canonicalPose7_205.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_205 (box := canonicalBox7_205) (k := keys7Chunk6.get ⟨13, by decide⟩) (canonicalMatch7_205) (canonicalDecode7_205)

def canonicalPose7_206 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, true, false, true, false], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_206 : BoxKey 7 :=
  ⟨![73920, 107520, 275520, 241920, 127680, 67200, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 108010, 274960, 241535, 128080, 66780, 376880], true⟩

theorem canonicalMatch7_206 :
    canonicalPose7_206.boxKey 188160 (referenceBox7 (!canonicalBox7_206.bump)) = canonicalBox7_206 := by decide +kernel

theorem canonicalDecode7_206 : canonicalBox7_206.toKeyData 188160 = keys7Chunk6.get ⟨14, by decide⟩ := by
  change canonicalBox7_206.toKeyData 188160 = ⟨![(11 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (5 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_206 : keySolid (keys7Chunk6.get ⟨14, by decide⟩) = canonicalPose7_206.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_206 (box := canonicalBox7_206) (k := keys7Chunk6.get ⟨14, by decide⟩) (canonicalMatch7_206) (canonicalDecode7_206)

def canonicalPose7_207 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, true, true, false, true, true], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_207 : BoxKey 7 :=
  ⟨![67200, 127680, 241920, 275520, 107520, 73920, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 128080, 241535, 274960, 108010, 73472, 375760], false⟩

theorem canonicalMatch7_207 :
    canonicalPose7_207.boxKey 188160 (referenceBox7 (!canonicalBox7_207.bump)) = canonicalBox7_207 := by decide +kernel

theorem canonicalDecode7_207 : canonicalBox7_207.toKeyData 188160 = keys7Chunk6.get ⟨15, by decide⟩ := by
  change canonicalBox7_207.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (11 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_207 : keySolid (keys7Chunk6.get ⟨15, by decide⟩) = canonicalPose7_207.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_207 (box := canonicalBox7_207) (k := keys7Chunk6.get ⟨15, by decide⟩) (canonicalMatch7_207) (canonicalDecode7_207)

def canonicalPose7_208 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, true, true, false, false], ![0, 0, 2, 2, 1, 1, 0]⟩
def canonicalBox7_208 : BoxKey 7 :=
  ⟨![0, 114240, 268800, 275520, 53760, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 114688, 268310, 274960, 53375, 316240, 121380], true⟩

theorem canonicalMatch7_208 :
    canonicalPose7_208.boxKey 188160 (referenceBox7 (!canonicalBox7_208.bump)) = canonicalBox7_208 := by decide +kernel

theorem canonicalDecode7_208 : canonicalBox7_208.toKeyData 188160 = keys7Chunk6.get ⟨16, by decide⟩ := by
  change canonicalBox7_208.toKeyData 188160 = ⟨![0, (17 / 28), (10 / 7), (41 / 28), (2 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_208 : keySolid (keys7Chunk6.get ⟨16, by decide⟩) = canonicalPose7_208.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_208 (box := canonicalBox7_208) (k := keys7Chunk6.get ⟨16, by decide⟩) (canonicalMatch7_208) (canonicalDecode7_208)

def canonicalPose7_209 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, false, true, false, true, false], ![1, 0, 1, 2, 0, 2, 0]⟩
def canonicalBox7_209 : BoxKey 7 :=
  ⟨![73920, 0, 309120, 248640, 134400, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, 560, 309540, 248240, 134785, 274960, 108010], false⟩

theorem canonicalMatch7_209 :
    canonicalPose7_209.boxKey 188160 (referenceBox7 (!canonicalBox7_209.bump)) = canonicalBox7_209 := by decide +kernel

theorem canonicalDecode7_209 : canonicalBox7_209.toKeyData 188160 = keys7Chunk6.get ⟨17, by decide⟩ := by
  change canonicalBox7_209.toKeyData 188160 = ⟨![(11 / 28), 0, (23 / 14), (37 / 28), (5 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_209 : keySolid (keys7Chunk6.get ⟨17, by decide⟩) = canonicalPose7_209.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_209 (box := canonicalBox7_209) (k := keys7Chunk6.get ⟨17, by decide⟩) (canonicalMatch7_209) (canonicalDecode7_209)

def canonicalPose7_210 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, false, true, false, true, false], ![1, 0, 1, 2, 0, 2, 0]⟩
def canonicalBox7_210 : BoxKey 7 :=
  ⟨![67200, 0, 302400, 268800, 100800, 241920, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, -560, 302848, 268310, 101360, 241535, 128080], true⟩

theorem canonicalMatch7_210 :
    canonicalPose7_210.boxKey 188160 (referenceBox7 (!canonicalBox7_210.bump)) = canonicalBox7_210 := by decide +kernel

theorem canonicalDecode7_210 : canonicalBox7_210.toKeyData 188160 = keys7Chunk6.get ⟨18, by decide⟩ := by
  change canonicalBox7_210.toKeyData 188160 = ⟨![(5 / 14), 0, (45 / 28), (10 / 7), (15 / 28), (9 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (-1 / 336), (169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_210 : keySolid (keys7Chunk6.get ⟨18, by decide⟩) = canonicalPose7_210.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_210 (box := canonicalBox7_210) (k := keys7Chunk6.get ⟨18, by decide⟩) (canonicalMatch7_210) (canonicalDecode7_210)

def canonicalPose7_211 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, true, true, false, false], ![0, 0, 2, 2, 1, 1, 0]⟩
def canonicalBox7_211 : BoxKey 7 :=
  ⟨![107520, 114240, 376320, 255360, 60480, 322560, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, 375760, 254940, 60080, 322945, 101360], false⟩

theorem canonicalMatch7_211 :
    canonicalPose7_211.boxKey 188160 (referenceBox7 (!canonicalBox7_211.bump)) = canonicalBox7_211 := by decide +kernel

theorem canonicalDecode7_211 : canonicalBox7_211.toKeyData 188160 = keys7Chunk6.get ⟨19, by decide⟩ := by
  change canonicalBox7_211.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (12 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (671 / 336), (607 / 448), (751 / 2352), (9227 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_211 : keySolid (keys7Chunk6.get ⟨19, by decide⟩) = canonicalPose7_211.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_211 (box := canonicalBox7_211) (k := keys7Chunk6.get ⟨19, by decide⟩) (canonicalMatch7_211) (canonicalDecode7_211)

def canonicalPose7_212 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, true, true, false, true, false], ![0, 1, 2, 2, 0, 2, 0]⟩
def canonicalBox7_212 : BoxKey 7 :=
  ⟨![134400, 60480, 255360, 376320, 114240, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 60080, 254940, 375760, 114688, 268310, 101360], false⟩

theorem canonicalMatch7_212 :
    canonicalPose7_212.boxKey 188160 (referenceBox7 (!canonicalBox7_212.bump)) = canonicalBox7_212 := by decide +kernel

theorem canonicalDecode7_212 : canonicalBox7_212.toKeyData 188160 = keys7Chunk6.get ⟨20, by decide⟩ := by
  change canonicalBox7_212.toKeyData 188160 = ⟨![(5 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (751 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_212 : keySolid (keys7Chunk6.get ⟨20, by decide⟩) = canonicalPose7_212.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_212 (box := canonicalBox7_212) (k := keys7Chunk6.get ⟨20, by decide⟩) (canonicalMatch7_212) (canonicalDecode7_212)

def canonicalPose7_213 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, false, false, true, true, true, false], ![1, 0, 1, 2, 0, 2, 0]⟩
def canonicalBox7_213 : BoxKey 7 :=
  ⟨![53760, 127680, 309120, 262080, 0, 268800, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 128080, 309540, 261632, -560, 268310, 101360], true⟩

theorem canonicalMatch7_213 :
    canonicalPose7_213.boxKey 188160 (referenceBox7 (!canonicalBox7_213.bump)) = canonicalBox7_213 := by decide +kernel

theorem canonicalDecode7_213 : canonicalBox7_213.toKeyData 188160 = keys7Chunk6.get ⟨21, by decide⟩ := by
  change canonicalBox7_213.toKeyData 188160 = ⟨![(2 / 7), (19 / 28), (23 / 14), (39 / 28), 0, (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (-1 / 336), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_213 : keySolid (keys7Chunk6.get ⟨21, by decide⟩) = canonicalPose7_213.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_213 (box := canonicalBox7_213) (k := keys7Chunk6.get ⟨21, by decide⟩) (canonicalMatch7_213) (canonicalDecode7_213)

def canonicalPose7_214 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, false, false, true, false, true, false], ![1, 0, 1, 2, 0, 2, 0]⟩
def canonicalBox7_214 : BoxKey 7 :=
  ⟨![67200, 127680, 322560, 275520, 107520, 376320, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 128080, 322945, 274960, 108010, 375760, 114688], false⟩

theorem canonicalMatch7_214 :
    canonicalPose7_214.boxKey 188160 (referenceBox7 (!canonicalBox7_214.bump)) = canonicalBox7_214 := by decide +kernel

theorem canonicalDecode7_214 : canonicalBox7_214.toKeyData 188160 = keys7Chunk6.get ⟨22, by decide⟩ := by
  change canonicalBox7_214.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (12 / 7), (41 / 28), (4 / 7), 2, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_214 : keySolid (keys7Chunk6.get ⟨22, by decide⟩) = canonicalPose7_214.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_214 (box := canonicalBox7_214) (k := keys7Chunk6.get ⟨22, by decide⟩) (canonicalMatch7_214) (canonicalDecode7_214)

def canonicalPose7_215 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, true, true, false, true, true], ![0, 1, 2, 2, 0, 2, 0]⟩
def canonicalBox7_215 : BoxKey 7 :=
  ⟨![120960, 60480, 241920, 275520, 107520, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 60080, 241535, 274960, 108010, 261632, -560], true⟩

theorem canonicalMatch7_215 :
    canonicalPose7_215.boxKey 188160 (referenceBox7 (!canonicalBox7_215.bump)) = canonicalBox7_215 := by decide +kernel

theorem canonicalDecode7_215 : canonicalBox7_215.toKeyData 188160 = keys7Chunk6.get ⟨23, by decide⟩ := by
  change canonicalBox7_215.toKeyData 188160 = ⟨![(9 / 14), (9 / 28), (9 / 7), (41 / 28), (4 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_215 : keySolid (keys7Chunk6.get ⟨23, by decide⟩) = canonicalPose7_215.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_215 (box := canonicalBox7_215) (k := keys7Chunk6.get ⟨23, by decide⟩) (canonicalMatch7_215) (canonicalDecode7_215)

def canonicalPose7_216 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, false, true, false, false, false, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_216 : BoxKey 7 :=
  ⟨![0, 107520, 275520, 322560, 127680, 309120, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![560, 108010, 274960, 322945, 128080, 309540, 261632], false⟩

theorem canonicalMatch7_216 :
    canonicalPose7_216.boxKey 188160 (referenceBox7 (!canonicalBox7_216.bump)) = canonicalBox7_216 := by decide +kernel

theorem canonicalDecode7_216 : canonicalBox7_216.toKeyData 188160 = keys7Chunk6.get ⟨24, by decide⟩ := by
  change canonicalBox7_216.toKeyData 188160 = ⟨![0, (4 / 7), (41 / 28), (12 / 7), (19 / 28), (23 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_216 : keySolid (keys7Chunk6.get ⟨24, by decide⟩) = canonicalPose7_216.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_216 (box := canonicalBox7_216) (k := keys7Chunk6.get ⟨24, by decide⟩) (canonicalMatch7_216) (canonicalDecode7_216)

def canonicalPose7_217 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, true, true, false, false, false, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_217 : BoxKey 7 :=
  ⟨![107520, 0, 262080, 309120, 127680, 322560, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, -560, 261632, 309540, 128080, 322945, 274960], true⟩

theorem canonicalMatch7_217 :
    canonicalPose7_217.boxKey 188160 (referenceBox7 (!canonicalBox7_217.bump)) = canonicalBox7_217 := by decide +kernel

theorem canonicalDecode7_217 : canonicalBox7_217.toKeyData 188160 = keys7Chunk6.get ⟨25, by decide⟩ := by
  change canonicalBox7_217.toKeyData 188160 = ⟨![(4 / 7), 0, (39 / 28), (23 / 14), (19 / 28), (12 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (-1 / 336), (146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_217 : keySolid (keys7Chunk6.get ⟨25, by decide⟩) = canonicalPose7_217.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_217 (box := canonicalBox7_217) (k := keys7Chunk6.get ⟨25, by decide⟩) (canonicalMatch7_217) (canonicalDecode7_217)

def canonicalPose7_218 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, true, true, true, true], ![0, 0, 2, 2, 1, 2, 2]⟩
def canonicalBox7_218 : BoxKey 7 :=
  ⟨![107520, 114240, 376320, 255360, 60480, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, 375760, 254940, 60080, 241535, 274960], false⟩

theorem canonicalMatch7_218 :
    canonicalPose7_218.boxKey 188160 (referenceBox7 (!canonicalBox7_218.bump)) = canonicalBox7_218 := by decide +kernel

theorem canonicalDecode7_218 : canonicalBox7_218.toKeyData 188160 = keys7Chunk6.get ⟨26, by decide⟩ := by
  change canonicalBox7_218.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (671 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_218 : keySolid (keys7Chunk6.get ⟨26, by decide⟩) = canonicalPose7_218.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_218 (box := canonicalBox7_218) (k := keys7Chunk6.get ⟨26, by decide⟩) (canonicalMatch7_218) (canonicalDecode7_218)

def canonicalPose7_219 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, true, false, true, true], ![1, 1, 2, 2, 0, 2, 2]⟩
def canonicalBox7_219 : BoxKey 7 :=
  ⟨![53760, 60480, 255360, 376320, 114240, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 60080, 254940, 375760, 114688, 268310, 274960], false⟩

theorem canonicalMatch7_219 :
    canonicalPose7_219.boxKey 188160 (referenceBox7 (!canonicalBox7_219.bump)) = canonicalBox7_219 := by decide +kernel

theorem canonicalDecode7_219 : canonicalBox7_219.toKeyData 188160 = keys7Chunk6.get ⟨27, by decide⟩ := by
  change canonicalBox7_219.toKeyData 188160 = ⟨![(2 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (751 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_219 : keySolid (keys7Chunk6.get ⟨27, by decide⟩) = canonicalPose7_219.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_219 (box := canonicalBox7_219) (k := keys7Chunk6.get ⟨27, by decide⟩) (canonicalMatch7_219) (canonicalDecode7_219)

def canonicalPose7_220 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, false, false, false, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_220 : BoxKey 7 :=
  ⟨![100800, 134400, 248640, 309120, 0, 302400, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 248240, 309540, 560, 302848, 268310], false⟩

theorem canonicalMatch7_220 :
    canonicalPose7_220.boxKey 188160 (referenceBox7 (!canonicalBox7_220.bump)) = canonicalBox7_220 := by decide +kernel

theorem canonicalDecode7_220 : canonicalBox7_220.toKeyData 188160 = keys7Chunk6.get ⟨28, by decide⟩ := by
  change canonicalBox7_220.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (37 / 28), (23 / 14), 0, (45 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (1 / 336), (169 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_220 : keySolid (keys7Chunk6.get ⟨28, by decide⟩) = canonicalPose7_220.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_220 (box := canonicalBox7_220) (k := keys7Chunk6.get ⟨28, by decide⟩) (canonicalMatch7_220) (canonicalDecode7_220)

def canonicalPose7_221 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, false, true, false, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_221 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 302400, 0, 309120, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 302848, -560, 309540, 248240], true⟩

theorem canonicalMatch7_221 :
    canonicalPose7_221.boxKey 188160 (referenceBox7 (!canonicalBox7_221.bump)) = canonicalBox7_221 := by decide +kernel

theorem canonicalDecode7_221 : canonicalBox7_221.toKeyData 188160 = keys7Chunk6.get ⟨29, by decide⟩ := by
  change canonicalBox7_221.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (45 / 28), 0, (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (-1 / 336), (737 / 448), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_221 : keySolid (keys7Chunk6.get ⟨29, by decide⟩) = canonicalPose7_221.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_221 (box := canonicalBox7_221) (k := keys7Chunk6.get ⟨29, by decide⟩) (canonicalMatch7_221) (canonicalDecode7_221)

def canonicalPose7_222 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, true, false, false, true], ![1, 1, 2, 2, 0, 2, 2]⟩
def canonicalBox7_222 : BoxKey 7 :=
  ⟨![60480, 53760, 275520, 268800, 114240, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 53375, 274960, 268310, 114688, 376880, 254940], true⟩

theorem canonicalMatch7_222 :
    canonicalPose7_222.boxKey 188160 (referenceBox7 (!canonicalBox7_222.bump)) = canonicalBox7_222 := by decide +kernel

theorem canonicalDecode7_222 : canonicalBox7_222.toKeyData 188160 = keys7Chunk6.get ⟨30, by decide⟩ := by
  change canonicalBox7_222.toKeyData 188160 = ⟨![(9 / 28), (2 / 7), (41 / 28), (10 / 7), (17 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_222 : keySolid (keys7Chunk6.get ⟨30, by decide⟩) = canonicalPose7_222.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_222 (box := canonicalBox7_222) (k := keys7Chunk6.get ⟨30, by decide⟩) (canonicalMatch7_222) (canonicalDecode7_222)

def canonicalPose7_223 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, true, true, true, false], ![0, 0, 2, 2, 1, 2, 2]⟩
def canonicalBox7_223 : BoxKey 7 :=
  ⟨![114240, 107520, 275520, 241920, 60480, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 274960, 241535, 60080, 254940, 376880], true⟩

theorem canonicalMatch7_223 :
    canonicalPose7_223.boxKey 188160 (referenceBox7 (!canonicalBox7_223.bump)) = canonicalBox7_223 := by decide +kernel

theorem canonicalDecode7_223 : canonicalBox7_223.toKeyData 188160 = keys7Chunk6.get ⟨31, by decide⟩ := by
  change canonicalBox7_223.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (41 / 28), (9 / 7), (9 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_223 : keySolid (keys7Chunk6.get ⟨31, by decide⟩) = canonicalPose7_223.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_223 (box := canonicalBox7_223) (k := keys7Chunk6.get ⟨31, by decide⟩) (canonicalMatch7_223) (canonicalDecode7_223)

theorem keys7Chunk6_canonical : ∀ k ∈ keys7Chunk6,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk6, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_192, canonicalSolid7_192⟩
  · exact ⟨canonicalPose7_193, canonicalSolid7_193⟩
  · exact ⟨canonicalPose7_194, canonicalSolid7_194⟩
  · exact ⟨canonicalPose7_195, canonicalSolid7_195⟩
  · exact ⟨canonicalPose7_196, canonicalSolid7_196⟩
  · exact ⟨canonicalPose7_197, canonicalSolid7_197⟩
  · exact ⟨canonicalPose7_198, canonicalSolid7_198⟩
  · exact ⟨canonicalPose7_199, canonicalSolid7_199⟩
  · exact ⟨canonicalPose7_200, canonicalSolid7_200⟩
  · exact ⟨canonicalPose7_201, canonicalSolid7_201⟩
  · exact ⟨canonicalPose7_202, canonicalSolid7_202⟩
  · exact ⟨canonicalPose7_203, canonicalSolid7_203⟩
  · exact ⟨canonicalPose7_204, canonicalSolid7_204⟩
  · exact ⟨canonicalPose7_205, canonicalSolid7_205⟩
  · exact ⟨canonicalPose7_206, canonicalSolid7_206⟩
  · exact ⟨canonicalPose7_207, canonicalSolid7_207⟩
  · exact ⟨canonicalPose7_208, canonicalSolid7_208⟩
  · exact ⟨canonicalPose7_209, canonicalSolid7_209⟩
  · exact ⟨canonicalPose7_210, canonicalSolid7_210⟩
  · exact ⟨canonicalPose7_211, canonicalSolid7_211⟩
  · exact ⟨canonicalPose7_212, canonicalSolid7_212⟩
  · exact ⟨canonicalPose7_213, canonicalSolid7_213⟩
  · exact ⟨canonicalPose7_214, canonicalSolid7_214⟩
  · exact ⟨canonicalPose7_215, canonicalSolid7_215⟩
  · exact ⟨canonicalPose7_216, canonicalSolid7_216⟩
  · exact ⟨canonicalPose7_217, canonicalSolid7_217⟩
  · exact ⟨canonicalPose7_218, canonicalSolid7_218⟩
  · exact ⟨canonicalPose7_219, canonicalSolid7_219⟩
  · exact ⟨canonicalPose7_220, canonicalSolid7_220⟩
  · exact ⟨canonicalPose7_221, canonicalSolid7_221⟩
  · exact ⟨canonicalPose7_222, canonicalSolid7_222⟩
  · exact ⟨canonicalPose7_223, canonicalSolid7_223⟩

#print axioms keys7Chunk6_canonical

end SparseMonotiles.Canonical
