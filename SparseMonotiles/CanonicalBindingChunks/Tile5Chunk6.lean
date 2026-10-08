module

public import SparseMonotiles.CanonicalReferenceKeys
public import SparseMonotiles.CanonicalPermutations5
public import SparseMonotiles.Tile5Data
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def canonicalPose5_192 : Pose 5 :=
  ⟨canonicalPerm5_15, ![false, true, false, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_192 : BoxKey 5 :=
  ⟨![32640, 0, 31680, 30720, 29760], ![420, 0, 360, 300, 240], ![32710, -80, 31752, 30795, 29840], true⟩

theorem canonicalMatch5_192 :
    canonicalPose5_192.boxKey 19200 (referenceBox5 (!canonicalBox5_192.bump)) = canonicalBox5_192 := by decide

theorem canonicalDecode5_192 : canonicalBox5_192.toKeyData 19200 = keys5Chunk6.get ⟨0, by decide⟩ := by
  change canonicalBox5_192.toKeyData 19200 = ⟨![(17 / 10), 0, (33 / 20), (8 / 5), (31 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(3271 / 1920), (-1 / 240), (1323 / 800), (2053 / 1280), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_192, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_192, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_192, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_192 : keySolid (keys5Chunk6.get ⟨0, by decide⟩) = canonicalPose5_192.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_192 (box := canonicalBox5_192) (k := keys5Chunk6.get ⟨0, by decide⟩) (canonicalMatch5_192) (canonicalDecode5_192)

def canonicalPose5_193 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, true, true, true, false], ![1, 1, 2, 2, 1]⟩
def canonicalBox5_193 : BoxKey 5 :=
  ⟨![31680, 19200, 24960, 27840, 30720], ![360, 0, 420, 240, 300], ![31752, 19120, 24890, 27760, 30795], false⟩

theorem canonicalMatch5_193 :
    canonicalPose5_193.boxKey 19200 (referenceBox5 (!canonicalBox5_193.bump)) = canonicalBox5_193 := by decide

theorem canonicalDecode5_193 : canonicalBox5_193.toKeyData 19200 = keys5Chunk6.get ⟨1, by decide⟩ := by
  change canonicalBox5_193.toKeyData 19200 = ⟨![(33 / 20), 1, (13 / 10), (29 / 20), (8 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(1323 / 800), (239 / 240), (2489 / 1920), (347 / 240), (2053 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_193, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_193, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_193, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_193 : keySolid (keys5Chunk6.get ⟨1, by decide⟩) = canonicalPose5_193.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_193 (box := canonicalBox5_193) (k := keys5Chunk6.get ⟨1, by decide⟩) (canonicalMatch5_193) (canonicalDecode5_193)

def canonicalPose5_194 : Pose 5 :=
  ⟨canonicalPerm5_5, ![true, false, false, false, false], ![2, 0, 2, 1, 1]⟩
def canonicalBox5_194 : BoxKey 5 :=
  ⟨![26880, 12480, 38400, 32640, 29760], ![300, 360, 0, 420, 240], ![26805, 12552, 38480, 32710, 29840], true⟩

theorem canonicalMatch5_194 :
    canonicalPose5_194.boxKey 19200 (referenceBox5 (!canonicalBox5_194.bump)) = canonicalBox5_194 := by decide

theorem canonicalDecode5_194 : canonicalBox5_194.toKeyData 19200 = keys5Chunk6.get ⟨2, by decide⟩ := by
  change canonicalBox5_194.toKeyData 19200 = ⟨![(7 / 5), (13 / 20), 2, (17 / 10), (31 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(1787 / 1280), (523 / 800), (481 / 240), (3271 / 1920), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_194, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_194, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_194, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_194 : keySolid (keys5Chunk6.get ⟨2, by decide⟩) = canonicalPose5_194.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_194 (box := canonicalBox5_194) (k := keys5Chunk6.get ⟨2, by decide⟩) (canonicalMatch5_194) (canonicalDecode5_194)

def canonicalPose5_195 : Pose 5 :=
  ⟨canonicalPerm5_14, ![false, false, false, true, true], ![1, 0, 1, 2, 2]⟩
def canonicalBox5_195 : BoxKey 5 :=
  ⟨![32640, 12480, 29760, 38400, 26880], ![420, 360, 240, 0, 300], ![32710, 12552, 29840, 38320, 26805], false⟩

theorem canonicalMatch5_195 :
    canonicalPose5_195.boxKey 19200 (referenceBox5 (!canonicalBox5_195.bump)) = canonicalBox5_195 := by decide

theorem canonicalDecode5_195 : canonicalBox5_195.toKeyData 19200 = keys5Chunk6.get ⟨3, by decide⟩ := by
  change canonicalBox5_195.toKeyData 19200 = ⟨![(17 / 10), (13 / 20), (31 / 20), 2, (7 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(3271 / 1920), (523 / 800), (373 / 240), (479 / 240), (1787 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_195, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_195, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_195, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_195 : keySolid (keys5Chunk6.get ⟨3, by decide⟩) = canonicalPose5_195.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_195 (box := canonicalBox5_195) (k := keys5Chunk6.get ⟨3, by decide⟩) (canonicalMatch5_195) (canonicalDecode5_195)

def canonicalPose5_196 : Pose 5 :=
  ⟨canonicalPerm5_1, ![false, false, false, true, true], ![1, 0, 1, 2, 2]⟩
def canonicalBox5_196 : BoxKey 5 :=
  ⟨![29760, 12480, 32640, 26880, 38400], ![240, 360, 420, 300, 0], ![29840, 12552, 32710, 26805, 38320], false⟩

theorem canonicalMatch5_196 :
    canonicalPose5_196.boxKey 19200 (referenceBox5 (!canonicalBox5_196.bump)) = canonicalBox5_196 := by decide

theorem canonicalDecode5_196 : canonicalBox5_196.toKeyData 19200 = keys5Chunk6.get ⟨4, by decide⟩ := by
  change canonicalBox5_196.toKeyData 19200 = ⟨![(31 / 20), (13 / 20), (17 / 10), (7 / 5), 2], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(373 / 240), (523 / 800), (3271 / 1920), (1787 / 1280), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_196, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_196, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_196, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_196 : keySolid (keys5Chunk6.get ⟨4, by decide⟩) = canonicalPose5_196.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_196 (box := canonicalBox5_196) (k := keys5Chunk6.get ⟨4, by decide⟩) (canonicalMatch5_196) (canonicalDecode5_196)

def canonicalPose5_197 : Pose 5 :=
  ⟨canonicalPerm5_17, ![true, true, true, false, true], ![2, 2, 1, 0, 1]⟩
def canonicalBox5_197 : BoxKey 5 :=
  ⟨![38400, 26880, 5760, 12480, 8640], ![0, 300, 420, 360, 240], ![38320, 26805, 5690, 12552, 8560], false⟩

theorem canonicalMatch5_197 :
    canonicalPose5_197.boxKey 19200 (referenceBox5 (!canonicalBox5_197.bump)) = canonicalBox5_197 := by decide

theorem canonicalDecode5_197 : canonicalBox5_197.toKeyData 19200 = keys5Chunk6.get ⟨5, by decide⟩ := by
  change canonicalBox5_197.toKeyData 19200 = ⟨![2, (7 / 5), (3 / 10), (13 / 20), (9 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(479 / 240), (1787 / 1280), (569 / 1920), (523 / 800), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_197, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_197, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_197, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_197 : keySolid (keys5Chunk6.get ⟨5, by decide⟩) = canonicalPose5_197.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_197 (box := canonicalBox5_197) (k := keys5Chunk6.get ⟨5, by decide⟩) (canonicalMatch5_197) (canonicalDecode5_197)

def canonicalPose5_198 : Pose 5 :=
  ⟨canonicalPerm5_7, ![true, true, true, false, true], ![2, 2, 1, 0, 1]⟩
def canonicalBox5_198 : BoxKey 5 :=
  ⟨![26880, 38400, 8640, 12480, 5760], ![300, 0, 240, 360, 420], ![26805, 38320, 8560, 12552, 5690], false⟩

theorem canonicalMatch5_198 :
    canonicalPose5_198.boxKey 19200 (referenceBox5 (!canonicalBox5_198.bump)) = canonicalBox5_198 := by decide

theorem canonicalDecode5_198 : canonicalBox5_198.toKeyData 19200 = keys5Chunk6.get ⟨6, by decide⟩ := by
  change canonicalBox5_198.toKeyData 19200 = ⟨![(7 / 5), 2, (9 / 20), (13 / 20), (3 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(1787 / 1280), (479 / 240), (107 / 240), (523 / 800), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_198, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_198, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_198, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_198 : keySolid (keys5Chunk6.get ⟨6, by decide⟩) = canonicalPose5_198.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_198 (box := canonicalBox5_198) (k := keys5Chunk6.get ⟨6, by decide⟩) (canonicalMatch5_198) (canonicalDecode5_198)

def canonicalPose5_199 : Pose 5 :=
  ⟨canonicalPerm5_2, ![false, false, true, false, false], ![1, 1, 0, 0, 0]⟩
def canonicalBox5_199 : BoxKey 5 :=
  ⟨![29760, 32640, 0, 12480, 11520], ![240, 420, 0, 360, 300], ![29840, 32710, -80, 12552, 11595], true⟩

theorem canonicalMatch5_199 :
    canonicalPose5_199.boxKey 19200 (referenceBox5 (!canonicalBox5_199.bump)) = canonicalBox5_199 := by decide

theorem canonicalDecode5_199 : canonicalBox5_199.toKeyData 19200 = keys5Chunk6.get ⟨7, by decide⟩ := by
  change canonicalBox5_199.toKeyData 19200 = ⟨![(31 / 20), (17 / 10), 0, (13 / 20), (3 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(373 / 240), (3271 / 1920), (-1 / 240), (523 / 800), (773 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_199, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_199, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_199, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_199 : keySolid (keys5Chunk6.get ⟨7, by decide⟩) = canonicalPose5_199.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_199 (box := canonicalBox5_199) (k := keys5Chunk6.get ⟨7, by decide⟩) (canonicalMatch5_199) (canonicalDecode5_199)

def canonicalPose5_200 : Pose 5 :=
  ⟨canonicalPerm5_0, ![false, false, true, true, true], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_200 : BoxKey 5 :=
  ⟨![29760, 30720, 6720, 0, 5760], ![240, 300, 360, 0, 420], ![29840, 30795, 6648, -80, 5690], true⟩

theorem canonicalMatch5_200 :
    canonicalPose5_200.boxKey 19200 (referenceBox5 (!canonicalBox5_200.bump)) = canonicalBox5_200 := by decide

theorem canonicalDecode5_200 : canonicalBox5_200.toKeyData 19200 = keys5Chunk6.get ⟨8, by decide⟩ := by
  change canonicalBox5_200.toKeyData 19200 = ⟨![(31 / 20), (8 / 5), (7 / 20), 0, (3 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(373 / 240), (2053 / 1280), (277 / 800), (-1 / 240), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_200, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_200, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_200, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_200 : keySolid (keys5Chunk6.get ⟨8, by decide⟩) = canonicalPose5_200.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_200 (box := canonicalBox5_200) (k := keys5Chunk6.get ⟨8, by decide⟩) (canonicalMatch5_200) (canonicalDecode5_200)

def canonicalPose5_201 : Pose 5 :=
  ⟨canonicalPerm5_4, ![false, false, true, true, true], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_201 : BoxKey 5 :=
  ⟨![30720, 29760, 5760, 0, 6720], ![300, 240, 420, 0, 360], ![30795, 29840, 5690, -80, 6648], true⟩

theorem canonicalMatch5_201 :
    canonicalPose5_201.boxKey 19200 (referenceBox5 (!canonicalBox5_201.bump)) = canonicalBox5_201 := by decide

theorem canonicalDecode5_201 : canonicalBox5_201.toKeyData 19200 = keys5Chunk6.get ⟨9, by decide⟩ := by
  change canonicalBox5_201.toKeyData 19200 = ⟨![(8 / 5), (31 / 20), (3 / 10), 0, (7 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(2053 / 1280), (373 / 240), (569 / 1920), (-1 / 240), (277 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_201, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_201, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_201, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_201 : keySolid (keys5Chunk6.get ⟨9, by decide⟩) = canonicalPose5_201.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_201 (box := canonicalBox5_201) (k := keys5Chunk6.get ⟨9, by decide⟩) (canonicalMatch5_201) (canonicalDecode5_201)

def canonicalPose5_202 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, false, true, false, true], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_202 : BoxKey 5 :=
  ⟨![31680, 32640, 7680, 0, 8640], ![360, 420, 300, 0, 240], ![31752, 32710, 7605, 80, 8560], false⟩

theorem canonicalMatch5_202 :
    canonicalPose5_202.boxKey 19200 (referenceBox5 (!canonicalBox5_202.bump)) = canonicalBox5_202 := by decide

theorem canonicalDecode5_202 : canonicalBox5_202.toKeyData 19200 = keys5Chunk6.get ⟨10, by decide⟩ := by
  change canonicalBox5_202.toKeyData 19200 = ⟨![(33 / 20), (17 / 10), (2 / 5), 0, (9 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(1323 / 800), (3271 / 1920), (507 / 1280), (1 / 240), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_202, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_202, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_202, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_202 : keySolid (keys5Chunk6.get ⟨10, by decide⟩) = canonicalPose5_202.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_202 (box := canonicalBox5_202) (k := keys5Chunk6.get ⟨10, by decide⟩) (canonicalMatch5_202) (canonicalDecode5_202)

def canonicalPose5_203 : Pose 5 :=
  ⟨canonicalPerm5_14, ![false, false, true, false, true], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_203 : BoxKey 5 :=
  ⟨![32640, 31680, 8640, 0, 7680], ![420, 360, 240, 0, 300], ![32710, 31752, 8560, 80, 7605], false⟩

theorem canonicalMatch5_203 :
    canonicalPose5_203.boxKey 19200 (referenceBox5 (!canonicalBox5_203.bump)) = canonicalBox5_203 := by decide

theorem canonicalDecode5_203 : canonicalBox5_203.toKeyData 19200 = keys5Chunk6.get ⟨11, by decide⟩ := by
  change canonicalBox5_203.toKeyData 19200 = ⟨![(17 / 10), (33 / 20), (9 / 20), 0, (2 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(3271 / 1920), (1323 / 800), (107 / 240), (1 / 240), (507 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_203, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_203, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_203, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_203 : keySolid (keys5Chunk6.get ⟨11, by decide⟩) = canonicalPose5_203.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_203 (box := canonicalBox5_203) (k := keys5Chunk6.get ⟨11, by decide⟩) (canonicalMatch5_203) (canonicalDecode5_203)

def canonicalPose5_204 : Pose 5 :=
  ⟨canonicalPerm5_12, ![false, false, false, false, true], ![1, 1, 0, 0, 0]⟩
def canonicalBox5_204 : BoxKey 5 :=
  ⟨![32640, 29760, 11520, 12480, 0], ![420, 240, 300, 360, 0], ![32710, 29840, 11595, 12552, -80], true⟩

theorem canonicalMatch5_204 :
    canonicalPose5_204.boxKey 19200 (referenceBox5 (!canonicalBox5_204.bump)) = canonicalBox5_204 := by decide

theorem canonicalDecode5_204 : canonicalBox5_204.toKeyData 19200 = keys5Chunk6.get ⟨12, by decide⟩ := by
  change canonicalBox5_204.toKeyData 19200 = ⟨![(17 / 10), (31 / 20), (3 / 5), (13 / 20), 0], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(3271 / 1920), (373 / 240), (773 / 1280), (523 / 800), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_204, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_204, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_204, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_204 : keySolid (keys5Chunk6.get ⟨12, by decide⟩) = canonicalPose5_204.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_204 (box := canonicalBox5_204) (k := keys5Chunk6.get ⟨12, by decide⟩) (canonicalMatch5_204) (canonicalDecode5_204)

def canonicalPose5_205 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, false, true, true, false], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_205 : BoxKey 5 :=
  ⟨![38400, 29760, 6720, 5760, 30720], ![0, 240, 360, 420, 300], ![38480, 29840, 6648, 5690, 30795], true⟩

theorem canonicalMatch5_205 :
    canonicalPose5_205.boxKey 19200 (referenceBox5 (!canonicalBox5_205.bump)) = canonicalBox5_205 := by decide

theorem canonicalDecode5_205 : canonicalBox5_205.toKeyData 19200 = keys5Chunk6.get ⟨13, by decide⟩ := by
  change canonicalBox5_205.toKeyData 19200 = ⟨![2, (31 / 20), (7 / 20), (3 / 10), (8 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(481 / 240), (373 / 240), (277 / 800), (569 / 1920), (2053 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_205, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_205, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_205, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_205 : keySolid (keys5Chunk6.get ⟨13, by decide⟩) = canonicalPose5_205.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_205 (box := canonicalBox5_205) (k := keys5Chunk6.get ⟨13, by decide⟩) (canonicalMatch5_205) (canonicalDecode5_205)

def canonicalPose5_206 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, false, true, true, false], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_206 : BoxKey 5 :=
  ⟨![38400, 30720, 5760, 6720, 29760], ![0, 300, 420, 360, 240], ![38480, 30795, 5690, 6648, 29840], true⟩

theorem canonicalMatch5_206 :
    canonicalPose5_206.boxKey 19200 (referenceBox5 (!canonicalBox5_206.bump)) = canonicalBox5_206 := by decide

theorem canonicalDecode5_206 : canonicalBox5_206.toKeyData 19200 = keys5Chunk6.get ⟨14, by decide⟩ := by
  change canonicalBox5_206.toKeyData 19200 = ⟨![2, (8 / 5), (3 / 10), (7 / 20), (31 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(481 / 240), (2053 / 1280), (569 / 1920), (277 / 800), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_206, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_206, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_206, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_206 : keySolid (keys5Chunk6.get ⟨14, by decide⟩) = canonicalPose5_206.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_206 (box := canonicalBox5_206) (k := keys5Chunk6.get ⟨14, by decide⟩) (canonicalMatch5_206) (canonicalDecode5_206)

def canonicalPose5_207 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, false, true, true, false], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_207 : BoxKey 5 :=
  ⟨![38400, 31680, 7680, 8640, 32640], ![0, 360, 300, 240, 420], ![38320, 31752, 7605, 8560, 32710], false⟩

theorem canonicalMatch5_207 :
    canonicalPose5_207.boxKey 19200 (referenceBox5 (!canonicalBox5_207.bump)) = canonicalBox5_207 := by decide

theorem canonicalDecode5_207 : canonicalBox5_207.toKeyData 19200 = keys5Chunk6.get ⟨15, by decide⟩ := by
  change canonicalBox5_207.toKeyData 19200 = ⟨![2, (33 / 20), (2 / 5), (9 / 20), (17 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(479 / 240), (1323 / 800), (507 / 1280), (107 / 240), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_207, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_207, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_207, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_207 : keySolid (keys5Chunk6.get ⟨15, by decide⟩) = canonicalPose5_207.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_207 (box := canonicalBox5_207) (k := keys5Chunk6.get ⟨15, by decide⟩) (canonicalMatch5_207) (canonicalDecode5_207)

def canonicalPose5_208 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, false, true, true, false], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_208 : BoxKey 5 :=
  ⟨![38400, 32640, 8640, 7680, 31680], ![0, 420, 240, 300, 360], ![38320, 32710, 8560, 7605, 31752], false⟩

theorem canonicalMatch5_208 :
    canonicalPose5_208.boxKey 19200 (referenceBox5 (!canonicalBox5_208.bump)) = canonicalBox5_208 := by decide

theorem canonicalDecode5_208 : canonicalBox5_208.toKeyData 19200 = keys5Chunk6.get ⟨16, by decide⟩ := by
  change canonicalBox5_208.toKeyData 19200 = ⟨![2, (17 / 10), (9 / 20), (2 / 5), (33 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(479 / 240), (3271 / 1920), (107 / 240), (507 / 1280), (1323 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_208, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_208, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_208, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_208 : keySolid (keys5Chunk6.get ⟨16, by decide⟩) = canonicalPose5_208.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_208 (box := canonicalBox5_208) (k := keys5Chunk6.get ⟨16, by decide⟩) (canonicalMatch5_208) (canonicalDecode5_208)

def canonicalPose5_209 : Pose 5 :=
  ⟨canonicalPerm5_11, ![true, true, true, true, true], ![2, 2, 1, 1, 2]⟩
def canonicalBox5_209 : BoxKey 5 :=
  ⟨![25920, 38400, 5760, 8640, 26880], ![360, 0, 420, 240, 300], ![25848, 38320, 5690, 8560, 26805], false⟩

theorem canonicalMatch5_209 :
    canonicalPose5_209.boxKey 19200 (referenceBox5 (!canonicalBox5_209.bump)) = canonicalBox5_209 := by decide

theorem canonicalDecode5_209 : canonicalBox5_209.toKeyData 19200 = keys5Chunk6.get ⟨17, by decide⟩ := by
  change canonicalBox5_209.toKeyData 19200 = ⟨![(27 / 20), 2, (3 / 10), (9 / 20), (7 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(1077 / 800), (479 / 240), (569 / 1920), (107 / 240), (1787 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_209, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_209, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_209, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_209 : keySolid (keys5Chunk6.get ⟨17, by decide⟩) = canonicalPose5_209.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_209 (box := canonicalBox5_209) (k := keys5Chunk6.get ⟨17, by decide⟩) (canonicalMatch5_209) (canonicalDecode5_209)

def canonicalPose5_210 : Pose 5 :=
  ⟨canonicalPerm5_8, ![true, false, true, false, false], ![2, 1, 0, 0, 1]⟩
def canonicalBox5_210 : BoxKey 5 :=
  ⟨![25920, 29760, 0, 11520, 32640], ![360, 240, 0, 300, 420], ![25848, 29840, -80, 11595, 32710], true⟩

theorem canonicalMatch5_210 :
    canonicalPose5_210.boxKey 19200 (referenceBox5 (!canonicalBox5_210.bump)) = canonicalBox5_210 := by decide

theorem canonicalDecode5_210 : canonicalBox5_210.toKeyData 19200 = keys5Chunk6.get ⟨18, by decide⟩ := by
  change canonicalBox5_210.toKeyData 19200 = ⟨![(27 / 20), (31 / 20), 0, (3 / 5), (17 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(1077 / 800), (373 / 240), (-1 / 240), (773 / 1280), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_210, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_210, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_210, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_210 : keySolid (keys5Chunk6.get ⟨18, by decide⟩) = canonicalPose5_210.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_210 (box := canonicalBox5_210) (k := keys5Chunk6.get ⟨18, by decide⟩) (canonicalMatch5_210) (canonicalDecode5_210)

def canonicalPose5_211 : Pose 5 :=
  ⟨canonicalPerm5_10, ![true, false, false, true, false], ![2, 1, 0, 0, 1]⟩
def canonicalBox5_211 : BoxKey 5 :=
  ⟨![25920, 32640, 11520, 0, 29760], ![360, 420, 300, 0, 240], ![25848, 32710, 11595, -80, 29840], true⟩

theorem canonicalMatch5_211 :
    canonicalPose5_211.boxKey 19200 (referenceBox5 (!canonicalBox5_211.bump)) = canonicalBox5_211 := by decide

theorem canonicalDecode5_211 : canonicalBox5_211.toKeyData 19200 = keys5Chunk6.get ⟨19, by decide⟩ := by
  change canonicalBox5_211.toKeyData 19200 = ⟨![(27 / 20), (17 / 10), (3 / 5), 0, (31 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(1077 / 800), (3271 / 1920), (773 / 1280), (-1 / 240), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_211, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_211, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_211, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_211 : keySolid (keys5Chunk6.get ⟨19, by decide⟩) = canonicalPose5_211.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_211 (box := canonicalBox5_211) (k := keys5Chunk6.get ⟨19, by decide⟩) (canonicalMatch5_211) (canonicalDecode5_211)

def canonicalPose5_212 : Pose 5 :=
  ⟨canonicalPerm5_9, ![true, true, true, true, true], ![2, 2, 1, 1, 2]⟩
def canonicalBox5_212 : BoxKey 5 :=
  ⟨![25920, 26880, 8640, 5760, 38400], ![360, 300, 240, 420, 0], ![25848, 26805, 8560, 5690, 38320], false⟩

theorem canonicalMatch5_212 :
    canonicalPose5_212.boxKey 19200 (referenceBox5 (!canonicalBox5_212.bump)) = canonicalBox5_212 := by decide

theorem canonicalDecode5_212 : canonicalBox5_212.toKeyData 19200 = keys5Chunk6.get ⟨20, by decide⟩ := by
  change canonicalBox5_212.toKeyData 19200 = ⟨![(27 / 20), (7 / 5), (9 / 20), (3 / 10), 2], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(1077 / 800), (1787 / 1280), (107 / 240), (569 / 1920), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_212, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_212, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_212, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_212 : keySolid (keys5Chunk6.get ⟨20, by decide⟩) = canonicalPose5_212.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_212 (box := canonicalBox5_212) (k := keys5Chunk6.get ⟨20, by decide⟩) (canonicalMatch5_212) (canonicalDecode5_212)

def canonicalPose5_213 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, true, true, true, true], ![2, 2, 1, 2, 1]⟩
def canonicalBox5_213 : BoxKey 5 :=
  ⟨![38400, 26880, 5760, 25920, 8640], ![0, 300, 420, 360, 240], ![38480, 26805, 5690, 25848, 8560], true⟩

theorem canonicalMatch5_213 :
    canonicalPose5_213.boxKey 19200 (referenceBox5 (!canonicalBox5_213.bump)) = canonicalBox5_213 := by decide

theorem canonicalDecode5_213 : canonicalBox5_213.toKeyData 19200 = keys5Chunk6.get ⟨21, by decide⟩ := by
  change canonicalBox5_213.toKeyData 19200 = ⟨![2, (7 / 5), (3 / 10), (27 / 20), (9 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(481 / 240), (1787 / 1280), (569 / 1920), (1077 / 800), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_213, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_213, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_213, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_213 : keySolid (keys5Chunk6.get ⟨21, by decide⟩) = canonicalPose5_213.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_213 (box := canonicalBox5_213) (k := keys5Chunk6.get ⟨21, by decide⟩) (canonicalMatch5_213) (canonicalDecode5_213)

def canonicalPose5_214 : Pose 5 :=
  ⟨canonicalPerm5_7, ![true, false, true, true, true], ![2, 2, 1, 2, 1]⟩
def canonicalBox5_214 : BoxKey 5 :=
  ⟨![26880, 38400, 8640, 25920, 5760], ![300, 0, 240, 360, 420], ![26805, 38480, 8560, 25848, 5690], true⟩

theorem canonicalMatch5_214 :
    canonicalPose5_214.boxKey 19200 (referenceBox5 (!canonicalBox5_214.bump)) = canonicalBox5_214 := by decide

theorem canonicalDecode5_214 : canonicalBox5_214.toKeyData 19200 = keys5Chunk6.get ⟨22, by decide⟩ := by
  change canonicalBox5_214.toKeyData 19200 = ⟨![(7 / 5), 2, (9 / 20), (27 / 20), (3 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(1787 / 1280), (481 / 240), (107 / 240), (1077 / 800), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_214, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_214, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_214, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_214 : keySolid (keys5Chunk6.get ⟨22, by decide⟩) = canonicalPose5_214.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_214 (box := canonicalBox5_214) (k := keys5Chunk6.get ⟨22, by decide⟩) (canonicalMatch5_214) (canonicalDecode5_214)

def canonicalPose5_215 : Pose 5 :=
  ⟨canonicalPerm5_2, ![false, false, false, true, false], ![1, 1, 0, 2, 0]⟩
def canonicalBox5_215 : BoxKey 5 :=
  ⟨![29760, 32640, 0, 25920, 11520], ![240, 420, 0, 360, 300], ![29840, 32710, 80, 25848, 11595], false⟩

theorem canonicalMatch5_215 :
    canonicalPose5_215.boxKey 19200 (referenceBox5 (!canonicalBox5_215.bump)) = canonicalBox5_215 := by decide

theorem canonicalDecode5_215 : canonicalBox5_215.toKeyData 19200 = keys5Chunk6.get ⟨23, by decide⟩ := by
  change canonicalBox5_215.toKeyData 19200 = ⟨![(31 / 20), (17 / 10), 0, (27 / 20), (3 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(373 / 240), (3271 / 1920), (1 / 240), (1077 / 800), (773 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_215, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_215, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_215, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_215 : keySolid (keys5Chunk6.get ⟨23, by decide⟩) = canonicalPose5_215.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_215 (box := canonicalBox5_215) (k := keys5Chunk6.get ⟨23, by decide⟩) (canonicalMatch5_215) (canonicalDecode5_215)

def canonicalPose5_216 : Pose 5 :=
  ⟨canonicalPerm5_0, ![false, false, true, true, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_216 : BoxKey 5 :=
  ⟨![29760, 30720, 6720, 38400, 5760], ![240, 300, 360, 0, 420], ![29840, 30795, 6648, 38320, 5690], false⟩

theorem canonicalMatch5_216 :
    canonicalPose5_216.boxKey 19200 (referenceBox5 (!canonicalBox5_216.bump)) = canonicalBox5_216 := by decide

theorem canonicalDecode5_216 : canonicalBox5_216.toKeyData 19200 = keys5Chunk6.get ⟨24, by decide⟩ := by
  change canonicalBox5_216.toKeyData 19200 = ⟨![(31 / 20), (8 / 5), (7 / 20), 2, (3 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(373 / 240), (2053 / 1280), (277 / 800), (479 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_216, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_216, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_216, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_216 : keySolid (keys5Chunk6.get ⟨24, by decide⟩) = canonicalPose5_216.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_216 (box := canonicalBox5_216) (k := keys5Chunk6.get ⟨24, by decide⟩) (canonicalMatch5_216) (canonicalDecode5_216)

def canonicalPose5_217 : Pose 5 :=
  ⟨canonicalPerm5_4, ![false, false, true, true, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_217 : BoxKey 5 :=
  ⟨![30720, 29760, 5760, 38400, 6720], ![300, 240, 420, 0, 360], ![30795, 29840, 5690, 38320, 6648], false⟩

theorem canonicalMatch5_217 :
    canonicalPose5_217.boxKey 19200 (referenceBox5 (!canonicalBox5_217.bump)) = canonicalBox5_217 := by decide

theorem canonicalDecode5_217 : canonicalBox5_217.toKeyData 19200 = keys5Chunk6.get ⟨25, by decide⟩ := by
  change canonicalBox5_217.toKeyData 19200 = ⟨![(8 / 5), (31 / 20), (3 / 10), 2, (7 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(2053 / 1280), (373 / 240), (569 / 1920), (479 / 240), (277 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_217, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_217, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_217, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_217 : keySolid (keys5Chunk6.get ⟨25, by decide⟩) = canonicalPose5_217.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_217 (box := canonicalBox5_217) (k := keys5Chunk6.get ⟨25, by decide⟩) (canonicalMatch5_217) (canonicalDecode5_217)

def canonicalPose5_218 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, false, true, false, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_218 : BoxKey 5 :=
  ⟨![31680, 32640, 7680, 38400, 8640], ![360, 420, 300, 0, 240], ![31752, 32710, 7605, 38480, 8560], true⟩

theorem canonicalMatch5_218 :
    canonicalPose5_218.boxKey 19200 (referenceBox5 (!canonicalBox5_218.bump)) = canonicalBox5_218 := by decide

theorem canonicalDecode5_218 : canonicalBox5_218.toKeyData 19200 = keys5Chunk6.get ⟨26, by decide⟩ := by
  change canonicalBox5_218.toKeyData 19200 = ⟨![(33 / 20), (17 / 10), (2 / 5), 2, (9 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(1323 / 800), (3271 / 1920), (507 / 1280), (481 / 240), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_218, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_218, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_218, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_218 : keySolid (keys5Chunk6.get ⟨26, by decide⟩) = canonicalPose5_218.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_218 (box := canonicalBox5_218) (k := keys5Chunk6.get ⟨26, by decide⟩) (canonicalMatch5_218) (canonicalDecode5_218)

def canonicalPose5_219 : Pose 5 :=
  ⟨canonicalPerm5_14, ![false, false, true, false, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_219 : BoxKey 5 :=
  ⟨![32640, 31680, 8640, 38400, 7680], ![420, 360, 240, 0, 300], ![32710, 31752, 8560, 38480, 7605], true⟩

theorem canonicalMatch5_219 :
    canonicalPose5_219.boxKey 19200 (referenceBox5 (!canonicalBox5_219.bump)) = canonicalBox5_219 := by decide

theorem canonicalDecode5_219 : canonicalBox5_219.toKeyData 19200 = keys5Chunk6.get ⟨27, by decide⟩ := by
  change canonicalBox5_219.toKeyData 19200 = ⟨![(17 / 10), (33 / 20), (9 / 20), 2, (2 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(3271 / 1920), (1323 / 800), (107 / 240), (481 / 240), (507 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_219, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_219, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_219, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_219 : keySolid (keys5Chunk6.get ⟨27, by decide⟩) = canonicalPose5_219.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_219 (box := canonicalBox5_219) (k := keys5Chunk6.get ⟨27, by decide⟩) (canonicalMatch5_219) (canonicalDecode5_219)

def canonicalPose5_220 : Pose 5 :=
  ⟨canonicalPerm5_12, ![false, false, false, true, false], ![1, 1, 0, 2, 0]⟩
def canonicalBox5_220 : BoxKey 5 :=
  ⟨![32640, 29760, 11520, 25920, 0], ![420, 240, 300, 360, 0], ![32710, 29840, 11595, 25848, 80], false⟩

theorem canonicalMatch5_220 :
    canonicalPose5_220.boxKey 19200 (referenceBox5 (!canonicalBox5_220.bump)) = canonicalBox5_220 := by decide

theorem canonicalDecode5_220 : canonicalBox5_220.toKeyData 19200 = keys5Chunk6.get ⟨28, by decide⟩ := by
  change canonicalBox5_220.toKeyData 19200 = ⟨![(17 / 10), (31 / 20), (3 / 5), (27 / 20), 0], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(3271 / 1920), (373 / 240), (773 / 1280), (1077 / 800), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_220, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_220, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_220, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_220 : keySolid (keys5Chunk6.get ⟨28, by decide⟩) = canonicalPose5_220.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_220 (box := canonicalBox5_220) (k := keys5Chunk6.get ⟨28, by decide⟩) (canonicalMatch5_220) (canonicalDecode5_220)

def canonicalPose5_221 : Pose 5 :=
  ⟨canonicalPerm5_16, ![true, false, false, false, true], ![2, 1, 0, 1, 2]⟩
def canonicalBox5_221 : BoxKey 5 :=
  ⟨![38400, 29760, 12480, 32640, 26880], ![0, 240, 360, 420, 300], ![38320, 29840, 12552, 32710, 26805], false⟩

theorem canonicalMatch5_221 :
    canonicalPose5_221.boxKey 19200 (referenceBox5 (!canonicalBox5_221.bump)) = canonicalBox5_221 := by decide

theorem canonicalDecode5_221 : canonicalBox5_221.toKeyData 19200 = keys5Chunk6.get ⟨29, by decide⟩ := by
  change canonicalBox5_221.toKeyData 19200 = ⟨![2, (31 / 20), (13 / 20), (17 / 10), (7 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(479 / 240), (373 / 240), (523 / 800), (3271 / 1920), (1787 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_221, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_221, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_221, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_221 : keySolid (keys5Chunk6.get ⟨29, by decide⟩) = canonicalPose5_221.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_221 (box := canonicalBox5_221) (k := keys5Chunk6.get ⟨29, by decide⟩) (canonicalMatch5_221) (canonicalDecode5_221)

def canonicalPose5_222 : Pose 5 :=
  ⟨canonicalPerm5_15, ![false, false, false, true, false], ![1, 2, 0, 2, 1]⟩
def canonicalBox5_222 : BoxKey 5 :=
  ⟨![32640, 38400, 12480, 26880, 29760], ![420, 0, 360, 300, 240], ![32710, 38480, 12552, 26805, 29840], true⟩

theorem canonicalMatch5_222 :
    canonicalPose5_222.boxKey 19200 (referenceBox5 (!canonicalBox5_222.bump)) = canonicalBox5_222 := by decide

theorem canonicalDecode5_222 : canonicalBox5_222.toKeyData 19200 = keys5Chunk6.get ⟨30, by decide⟩ := by
  change canonicalBox5_222.toKeyData 19200 = ⟨![(17 / 10), 2, (13 / 20), (7 / 5), (31 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(3271 / 1920), (481 / 240), (523 / 800), (1787 / 1280), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_222, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_222, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_222, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_222 : keySolid (keys5Chunk6.get ⟨30, by decide⟩) = canonicalPose5_222.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_222 (box := canonicalBox5_222) (k := keys5Chunk6.get ⟨30, by decide⟩) (canonicalMatch5_222) (canonicalDecode5_222)

def canonicalPose5_223 : Pose 5 :=
  ⟨canonicalPerm5_2, ![false, false, true, false, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_223 : BoxKey 5 :=
  ⟨![29760, 32640, 0, 31680, 30720], ![240, 420, 0, 360, 300], ![29840, 32710, -80, 31752, 30795], true⟩

theorem canonicalMatch5_223 :
    canonicalPose5_223.boxKey 19200 (referenceBox5 (!canonicalBox5_223.bump)) = canonicalBox5_223 := by decide

theorem canonicalDecode5_223 : canonicalBox5_223.toKeyData 19200 = keys5Chunk6.get ⟨31, by decide⟩ := by
  change canonicalBox5_223.toKeyData 19200 = ⟨![(31 / 20), (17 / 10), 0, (33 / 20), (8 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(373 / 240), (3271 / 1920), (-1 / 240), (1323 / 800), (2053 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_223, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_223, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_223, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_223 : keySolid (keys5Chunk6.get ⟨31, by decide⟩) = canonicalPose5_223.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_223 (box := canonicalBox5_223) (k := keys5Chunk6.get ⟨31, by decide⟩) (canonicalMatch5_223) (canonicalDecode5_223)

theorem keys5Chunk6_canonical : ∀ k ∈ keys5Chunk6,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk6, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_192, canonicalSolid5_192⟩
  · exact ⟨canonicalPose5_193, canonicalSolid5_193⟩
  · exact ⟨canonicalPose5_194, canonicalSolid5_194⟩
  · exact ⟨canonicalPose5_195, canonicalSolid5_195⟩
  · exact ⟨canonicalPose5_196, canonicalSolid5_196⟩
  · exact ⟨canonicalPose5_197, canonicalSolid5_197⟩
  · exact ⟨canonicalPose5_198, canonicalSolid5_198⟩
  · exact ⟨canonicalPose5_199, canonicalSolid5_199⟩
  · exact ⟨canonicalPose5_200, canonicalSolid5_200⟩
  · exact ⟨canonicalPose5_201, canonicalSolid5_201⟩
  · exact ⟨canonicalPose5_202, canonicalSolid5_202⟩
  · exact ⟨canonicalPose5_203, canonicalSolid5_203⟩
  · exact ⟨canonicalPose5_204, canonicalSolid5_204⟩
  · exact ⟨canonicalPose5_205, canonicalSolid5_205⟩
  · exact ⟨canonicalPose5_206, canonicalSolid5_206⟩
  · exact ⟨canonicalPose5_207, canonicalSolid5_207⟩
  · exact ⟨canonicalPose5_208, canonicalSolid5_208⟩
  · exact ⟨canonicalPose5_209, canonicalSolid5_209⟩
  · exact ⟨canonicalPose5_210, canonicalSolid5_210⟩
  · exact ⟨canonicalPose5_211, canonicalSolid5_211⟩
  · exact ⟨canonicalPose5_212, canonicalSolid5_212⟩
  · exact ⟨canonicalPose5_213, canonicalSolid5_213⟩
  · exact ⟨canonicalPose5_214, canonicalSolid5_214⟩
  · exact ⟨canonicalPose5_215, canonicalSolid5_215⟩
  · exact ⟨canonicalPose5_216, canonicalSolid5_216⟩
  · exact ⟨canonicalPose5_217, canonicalSolid5_217⟩
  · exact ⟨canonicalPose5_218, canonicalSolid5_218⟩
  · exact ⟨canonicalPose5_219, canonicalSolid5_219⟩
  · exact ⟨canonicalPose5_220, canonicalSolid5_220⟩
  · exact ⟨canonicalPose5_221, canonicalSolid5_221⟩
  · exact ⟨canonicalPose5_222, canonicalSolid5_222⟩
  · exact ⟨canonicalPose5_223, canonicalSolid5_223⟩

#print axioms keys5Chunk6_canonical

end SparseMonotiles.Canonical
