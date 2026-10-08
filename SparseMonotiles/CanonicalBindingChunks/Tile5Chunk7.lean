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

def canonicalPose5_224 : Pose 5 :=
  ⟨canonicalPerm5_5, ![false, false, true, false, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_224 : BoxKey 5 :=
  ⟨![30720, 31680, 0, 32640, 29760], ![300, 360, 0, 420, 240], ![30795, 31752, -80, 32710, 29840], true⟩

theorem canonicalMatch5_224 :
    canonicalPose5_224.boxKey 19200 (referenceBox5 (!canonicalBox5_224.bump)) = canonicalBox5_224 := by decide

theorem canonicalDecode5_224 : canonicalBox5_224.toKeyData 19200 = keys5Chunk7.get ⟨0, by decide⟩ := by
  change canonicalBox5_224.toKeyData 19200 = ⟨![(8 / 5), (33 / 20), 0, (17 / 10), (31 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(2053 / 1280), (1323 / 800), (-1 / 240), (3271 / 1920), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_224, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_224, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_224, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_224 : keySolid (keys5Chunk7.get ⟨0, by decide⟩) = canonicalPose5_224.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_224 (box := canonicalBox5_224) (k := keys5Chunk7.get ⟨0, by decide⟩) (canonicalMatch5_224) (canonicalDecode5_224)

def canonicalPose5_225 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, false, false, false, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_225 : BoxKey 5 :=
  ⟨![31680, 29760, 0, 30720, 32640], ![360, 240, 0, 300, 420], ![31752, 29840, 80, 30795, 32710], false⟩

theorem canonicalMatch5_225 :
    canonicalPose5_225.boxKey 19200 (referenceBox5 (!canonicalBox5_225.bump)) = canonicalBox5_225 := by decide

theorem canonicalDecode5_225 : canonicalBox5_225.toKeyData 19200 = keys5Chunk7.get ⟨1, by decide⟩ := by
  change canonicalBox5_225.toKeyData 19200 = ⟨![(33 / 20), (31 / 20), 0, (8 / 5), (17 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(1323 / 800), (373 / 240), (1 / 240), (2053 / 1280), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_225, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_225, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_225, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_225 : keySolid (keys5Chunk7.get ⟨1, by decide⟩) = canonicalPose5_225.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_225 (box := canonicalBox5_225) (k := keys5Chunk7.get ⟨1, by decide⟩) (canonicalMatch5_225) (canonicalDecode5_225)

def canonicalPose5_226 : Pose 5 :=
  ⟨canonicalPerm5_13, ![false, false, false, false, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_226 : BoxKey 5 :=
  ⟨![32640, 30720, 0, 29760, 31680], ![420, 300, 0, 240, 360], ![32710, 30795, 80, 29840, 31752], false⟩

theorem canonicalMatch5_226 :
    canonicalPose5_226.boxKey 19200 (referenceBox5 (!canonicalBox5_226.bump)) = canonicalBox5_226 := by decide

theorem canonicalDecode5_226 : canonicalBox5_226.toKeyData 19200 = keys5Chunk7.get ⟨2, by decide⟩ := by
  change canonicalBox5_226.toKeyData 19200 = ⟨![(17 / 10), (8 / 5), 0, (31 / 20), (33 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(3271 / 1920), (2053 / 1280), (1 / 240), (373 / 240), (1323 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_226, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_226, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_226, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_226 : keySolid (keys5Chunk7.get ⟨2, by decide⟩) = canonicalPose5_226.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_226 (box := canonicalBox5_226) (k := keys5Chunk7.get ⟨2, by decide⟩) (canonicalMatch5_226) (canonicalDecode5_226)

def canonicalPose5_227 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, true, false, false, true], ![1, 2, 1, 1, 2]⟩
def canonicalBox5_227 : BoxKey 5 :=
  ⟨![31680, 27840, 19200, 30720, 24960], ![360, 240, 0, 300, 420], ![31752, 27760, 19280, 30795, 24890], true⟩

theorem canonicalMatch5_227 :
    canonicalPose5_227.boxKey 19200 (referenceBox5 (!canonicalBox5_227.bump)) = canonicalBox5_227 := by decide

theorem canonicalDecode5_227 : canonicalBox5_227.toKeyData 19200 = keys5Chunk7.get ⟨3, by decide⟩ := by
  change canonicalBox5_227.toKeyData 19200 = ⟨![(33 / 20), (29 / 20), 1, (8 / 5), (13 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(1323 / 800), (347 / 240), (241 / 240), (2053 / 1280), (2489 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_227, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_227, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_227, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_227 : keySolid (keys5Chunk7.get ⟨3, by decide⟩) = canonicalPose5_227.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_227 (box := canonicalBox5_227) (k := keys5Chunk7.get ⟨3, by decide⟩) (canonicalMatch5_227) (canonicalDecode5_227)

def canonicalPose5_228 : Pose 5 :=
  ⟨canonicalPerm5_0, ![false, true, false, false, false], ![1, 2, 0, 2, 1]⟩
def canonicalBox5_228 : BoxKey 5 :=
  ⟨![29760, 26880, 12480, 38400, 32640], ![240, 300, 360, 0, 420], ![29840, 26805, 12552, 38480, 32710], true⟩

theorem canonicalMatch5_228 :
    canonicalPose5_228.boxKey 19200 (referenceBox5 (!canonicalBox5_228.bump)) = canonicalBox5_228 := by decide

theorem canonicalDecode5_228 : canonicalBox5_228.toKeyData 19200 = keys5Chunk7.get ⟨4, by decide⟩ := by
  change canonicalBox5_228.toKeyData 19200 = ⟨![(31 / 20), (7 / 5), (13 / 20), 2, (17 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(373 / 240), (1787 / 1280), (523 / 800), (481 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_228, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_228, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_228, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_228 : keySolid (keys5Chunk7.get ⟨4, by decide⟩) = canonicalPose5_228.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_228 (box := canonicalBox5_228) (k := keys5Chunk7.get ⟨4, by decide⟩) (canonicalMatch5_228) (canonicalDecode5_228)

def canonicalPose5_229 : Pose 5 :=
  ⟨canonicalPerm5_6, ![true, false, false, false, true], ![2, 1, 0, 1, 2]⟩
def canonicalBox5_229 : BoxKey 5 :=
  ⟨![26880, 32640, 12480, 29760, 38400], ![300, 420, 360, 240, 0], ![26805, 32710, 12552, 29840, 38320], false⟩

theorem canonicalMatch5_229 :
    canonicalPose5_229.boxKey 19200 (referenceBox5 (!canonicalBox5_229.bump)) = canonicalBox5_229 := by decide

theorem canonicalDecode5_229 : canonicalBox5_229.toKeyData 19200 = keys5Chunk7.get ⟨5, by decide⟩ := by
  change canonicalBox5_229.toKeyData 19200 = ⟨![(7 / 5), (17 / 10), (13 / 20), (31 / 20), 2], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(1787 / 1280), (3271 / 1920), (523 / 800), (373 / 240), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_229, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_229, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_229, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_229 : keySolid (keys5Chunk7.get ⟨5, by decide⟩) = canonicalPose5_229.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_229 (box := canonicalBox5_229) (k := keys5Chunk7.get ⟨5, by decide⟩) (canonicalMatch5_229) (canonicalDecode5_229)

def canonicalPose5_230 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, true, true, true, true], ![2, 2, 2, 1, 1]⟩
def canonicalBox5_230 : BoxKey 5 :=
  ⟨![38400, 25920, 26880, 8640, 5760], ![0, 360, 300, 240, 420], ![38320, 25848, 26805, 8560, 5690], false⟩

theorem canonicalMatch5_230 :
    canonicalPose5_230.boxKey 19200 (referenceBox5 (!canonicalBox5_230.bump)) = canonicalBox5_230 := by decide

theorem canonicalDecode5_230 : canonicalBox5_230.toKeyData 19200 = keys5Chunk7.get ⟨6, by decide⟩ := by
  change canonicalBox5_230.toKeyData 19200 = ⟨![2, (27 / 20), (7 / 5), (9 / 20), (3 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(479 / 240), (1077 / 800), (1787 / 1280), (107 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_230, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_230, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_230, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_230 : keySolid (keys5Chunk7.get ⟨6, by decide⟩) = canonicalPose5_230.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_230 (box := canonicalBox5_230) (k := keys5Chunk7.get ⟨6, by decide⟩) (canonicalMatch5_230) (canonicalDecode5_230)

def canonicalPose5_231 : Pose 5 :=
  ⟨canonicalPerm5_3, ![false, false, false, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_231 : BoxKey 5 :=
  ⟨![29760, 38400, 30720, 5760, 6720], ![240, 0, 300, 420, 360], ![29840, 38480, 30795, 5690, 6648], true⟩

theorem canonicalMatch5_231 :
    canonicalPose5_231.boxKey 19200 (referenceBox5 (!canonicalBox5_231.bump)) = canonicalBox5_231 := by decide

theorem canonicalDecode5_231 : canonicalBox5_231.toKeyData 19200 = keys5Chunk7.get ⟨7, by decide⟩ := by
  change canonicalBox5_231.toKeyData 19200 = ⟨![(31 / 20), 2, (8 / 5), (3 / 10), (7 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(373 / 240), (481 / 240), (2053 / 1280), (569 / 1920), (277 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_231, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_231, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_231, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_231 : keySolid (keys5Chunk7.get ⟨7, by decide⟩) = canonicalPose5_231.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_231 (box := canonicalBox5_231) (k := keys5Chunk7.get ⟨7, by decide⟩) (canonicalMatch5_231) (canonicalDecode5_231)

def canonicalPose5_232 : Pose 5 :=
  ⟨canonicalPerm5_7, ![false, false, false, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_232 : BoxKey 5 :=
  ⟨![30720, 38400, 29760, 6720, 5760], ![300, 0, 240, 360, 420], ![30795, 38480, 29840, 6648, 5690], true⟩

theorem canonicalMatch5_232 :
    canonicalPose5_232.boxKey 19200 (referenceBox5 (!canonicalBox5_232.bump)) = canonicalBox5_232 := by decide

theorem canonicalDecode5_232 : canonicalBox5_232.toKeyData 19200 = keys5Chunk7.get ⟨8, by decide⟩ := by
  change canonicalBox5_232.toKeyData 19200 = ⟨![(8 / 5), 2, (31 / 20), (7 / 20), (3 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(2053 / 1280), (481 / 240), (373 / 240), (277 / 800), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_232, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_232, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_232, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_232 : keySolid (keys5Chunk7.get ⟨8, by decide⟩) = canonicalPose5_232.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_232 (box := canonicalBox5_232) (k := keys5Chunk7.get ⟨8, by decide⟩) (canonicalMatch5_232) (canonicalDecode5_232)

def canonicalPose5_233 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, true, false, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_233 : BoxKey 5 :=
  ⟨![31680, 38400, 32640, 8640, 7680], ![360, 0, 420, 240, 300], ![31752, 38320, 32710, 8560, 7605], false⟩

theorem canonicalMatch5_233 :
    canonicalPose5_233.boxKey 19200 (referenceBox5 (!canonicalBox5_233.bump)) = canonicalBox5_233 := by decide

theorem canonicalDecode5_233 : canonicalBox5_233.toKeyData 19200 = keys5Chunk7.get ⟨9, by decide⟩ := by
  change canonicalBox5_233.toKeyData 19200 = ⟨![(33 / 20), 2, (17 / 10), (9 / 20), (2 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(1323 / 800), (479 / 240), (3271 / 1920), (107 / 240), (507 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_233, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_233, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_233, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_233 : keySolid (keys5Chunk7.get ⟨9, by decide⟩) = canonicalPose5_233.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_233 (box := canonicalBox5_233) (k := keys5Chunk7.get ⟨9, by decide⟩) (canonicalMatch5_233) (canonicalDecode5_233)

def canonicalPose5_234 : Pose 5 :=
  ⟨canonicalPerm5_15, ![false, true, false, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_234 : BoxKey 5 :=
  ⟨![32640, 38400, 31680, 7680, 8640], ![420, 0, 360, 300, 240], ![32710, 38320, 31752, 7605, 8560], false⟩

theorem canonicalMatch5_234 :
    canonicalPose5_234.boxKey 19200 (referenceBox5 (!canonicalBox5_234.bump)) = canonicalBox5_234 := by decide

theorem canonicalDecode5_234 : canonicalBox5_234.toKeyData 19200 = keys5Chunk7.get ⟨10, by decide⟩ := by
  change canonicalBox5_234.toKeyData 19200 = ⟨![(17 / 10), 2, (33 / 20), (2 / 5), (9 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(3271 / 1920), (479 / 240), (1323 / 800), (507 / 1280), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_234, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_234, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_234, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_234 : keySolid (keys5Chunk7.get ⟨10, by decide⟩) = canonicalPose5_234.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_234 (box := canonicalBox5_234) (k := keys5Chunk7.get ⟨10, by decide⟩) (canonicalMatch5_234) (canonicalDecode5_234)

def canonicalPose5_235 : Pose 5 :=
  ⟨canonicalPerm5_5, ![true, true, true, true, true], ![2, 2, 2, 1, 1]⟩
def canonicalBox5_235 : BoxKey 5 :=
  ⟨![26880, 25920, 38400, 5760, 8640], ![300, 360, 0, 420, 240], ![26805, 25848, 38320, 5690, 8560], false⟩

theorem canonicalMatch5_235 :
    canonicalPose5_235.boxKey 19200 (referenceBox5 (!canonicalBox5_235.bump)) = canonicalBox5_235 := by decide

theorem canonicalDecode5_235 : canonicalBox5_235.toKeyData 19200 = keys5Chunk7.get ⟨11, by decide⟩ := by
  change canonicalBox5_235.toKeyData 19200 = ⟨![(7 / 5), (27 / 20), 2, (3 / 10), (9 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(1787 / 1280), (1077 / 800), (479 / 240), (569 / 1920), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_235, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_235, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_235, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_235 : keySolid (keys5Chunk7.get ⟨11, by decide⟩) = canonicalPose5_235.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_235 (box := canonicalBox5_235) (k := keys5Chunk7.get ⟨11, by decide⟩) (canonicalMatch5_235) (canonicalDecode5_235)

def canonicalPose5_236 : Pose 5 :=
  ⟨canonicalPerm5_14, ![false, true, false, true, false], ![1, 2, 1, 0, 0]⟩
def canonicalBox5_236 : BoxKey 5 :=
  ⟨![32640, 25920, 29760, 0, 11520], ![420, 360, 240, 0, 300], ![32710, 25848, 29840, -80, 11595], true⟩

theorem canonicalMatch5_236 :
    canonicalPose5_236.boxKey 19200 (referenceBox5 (!canonicalBox5_236.bump)) = canonicalBox5_236 := by decide

theorem canonicalDecode5_236 : canonicalBox5_236.toKeyData 19200 = keys5Chunk7.get ⟨12, by decide⟩ := by
  change canonicalBox5_236.toKeyData 19200 = ⟨![(17 / 10), (27 / 20), (31 / 20), 0, (3 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(3271 / 1920), (1077 / 800), (373 / 240), (-1 / 240), (773 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_236, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_236, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_236, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_236 : keySolid (keys5Chunk7.get ⟨12, by decide⟩) = canonicalPose5_236.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_236 (box := canonicalBox5_236) (k := keys5Chunk7.get ⟨12, by decide⟩) (canonicalMatch5_236) (canonicalDecode5_236)

def canonicalPose5_237 : Pose 5 :=
  ⟨canonicalPerm5_1, ![false, true, false, false, true], ![1, 2, 1, 0, 0]⟩
def canonicalBox5_237 : BoxKey 5 :=
  ⟨![29760, 25920, 32640, 11520, 0], ![240, 360, 420, 300, 0], ![29840, 25848, 32710, 11595, -80], true⟩

theorem canonicalMatch5_237 :
    canonicalPose5_237.boxKey 19200 (referenceBox5 (!canonicalBox5_237.bump)) = canonicalBox5_237 := by decide

theorem canonicalDecode5_237 : canonicalBox5_237.toKeyData 19200 = keys5Chunk7.get ⟨13, by decide⟩ := by
  change canonicalBox5_237.toKeyData 19200 = ⟨![(31 / 20), (27 / 20), (17 / 10), (3 / 5), 0], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(373 / 240), (1077 / 800), (3271 / 1920), (773 / 1280), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_237, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_237, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_237, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_237 : keySolid (keys5Chunk7.get ⟨13, by decide⟩) = canonicalPose5_237.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_237 (box := canonicalBox5_237) (k := keys5Chunk7.get ⟨13, by decide⟩) (canonicalMatch5_237) (canonicalDecode5_237)

def canonicalPose5_238 : Pose 5 :=
  ⟨canonicalPerm5_17, ![true, true, false, false, false], ![2, 2, 1, 0, 1]⟩
def canonicalBox5_238 : BoxKey 5 :=
  ⟨![38400, 26880, 32640, 12480, 29760], ![0, 300, 420, 360, 240], ![38320, 26805, 32710, 12552, 29840], false⟩

theorem canonicalMatch5_238 :
    canonicalPose5_238.boxKey 19200 (referenceBox5 (!canonicalBox5_238.bump)) = canonicalBox5_238 := by decide

theorem canonicalDecode5_238 : canonicalBox5_238.toKeyData 19200 = keys5Chunk7.get ⟨14, by decide⟩ := by
  change canonicalBox5_238.toKeyData 19200 = ⟨![2, (7 / 5), (17 / 10), (13 / 20), (31 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(479 / 240), (1787 / 1280), (3271 / 1920), (523 / 800), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_238, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_238, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_238, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_238 : keySolid (keys5Chunk7.get ⟨14, by decide⟩) = canonicalPose5_238.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_238 (box := canonicalBox5_238) (k := keys5Chunk7.get ⟨14, by decide⟩) (canonicalMatch5_238) (canonicalDecode5_238)

def canonicalPose5_239 : Pose 5 :=
  ⟨canonicalPerm5_7, ![true, true, false, false, false], ![2, 2, 1, 0, 1]⟩
def canonicalBox5_239 : BoxKey 5 :=
  ⟨![26880, 38400, 29760, 12480, 32640], ![300, 0, 240, 360, 420], ![26805, 38320, 29840, 12552, 32710], false⟩

theorem canonicalMatch5_239 :
    canonicalPose5_239.boxKey 19200 (referenceBox5 (!canonicalBox5_239.bump)) = canonicalBox5_239 := by decide

theorem canonicalDecode5_239 : canonicalBox5_239.toKeyData 19200 = keys5Chunk7.get ⟨15, by decide⟩ := by
  change canonicalBox5_239.toKeyData 19200 = ⟨![(7 / 5), 2, (31 / 20), (13 / 20), (17 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(1787 / 1280), (479 / 240), (373 / 240), (523 / 800), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_239, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_239, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_239, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_239 : keySolid (keys5Chunk7.get ⟨15, by decide⟩) = canonicalPose5_239.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_239 (box := canonicalBox5_239) (k := keys5Chunk7.get ⟨15, by decide⟩) (canonicalMatch5_239) (canonicalDecode5_239)

def canonicalPose5_240 : Pose 5 :=
  ⟨canonicalPerm5_2, ![false, false, false, false, true], ![1, 1, 2, 0, 2]⟩
def canonicalBox5_240 : BoxKey 5 :=
  ⟨![29760, 32640, 38400, 12480, 26880], ![240, 420, 0, 360, 300], ![29840, 32710, 38480, 12552, 26805], true⟩

theorem canonicalMatch5_240 :
    canonicalPose5_240.boxKey 19200 (referenceBox5 (!canonicalBox5_240.bump)) = canonicalBox5_240 := by decide

theorem canonicalDecode5_240 : canonicalBox5_240.toKeyData 19200 = keys5Chunk7.get ⟨16, by decide⟩ := by
  change canonicalBox5_240.toKeyData 19200 = ⟨![(31 / 20), (17 / 10), 2, (13 / 20), (7 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(373 / 240), (3271 / 1920), (481 / 240), (523 / 800), (1787 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_240, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_240, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_240, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_240 : keySolid (keys5Chunk7.get ⟨16, by decide⟩) = canonicalPose5_240.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_240 (box := canonicalBox5_240) (k := keys5Chunk7.get ⟨16, by decide⟩) (canonicalMatch5_240) (canonicalDecode5_240)

def canonicalPose5_241 : Pose 5 :=
  ⟨canonicalPerm5_0, ![false, false, false, true, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_241 : BoxKey 5 :=
  ⟨![29760, 30720, 31680, 0, 32640], ![240, 300, 360, 0, 420], ![29840, 30795, 31752, -80, 32710], true⟩

theorem canonicalMatch5_241 :
    canonicalPose5_241.boxKey 19200 (referenceBox5 (!canonicalBox5_241.bump)) = canonicalBox5_241 := by decide

theorem canonicalDecode5_241 : canonicalBox5_241.toKeyData 19200 = keys5Chunk7.get ⟨17, by decide⟩ := by
  change canonicalBox5_241.toKeyData 19200 = ⟨![(31 / 20), (8 / 5), (33 / 20), 0, (17 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(373 / 240), (2053 / 1280), (1323 / 800), (-1 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_241, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_241, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_241, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_241 : keySolid (keys5Chunk7.get ⟨17, by decide⟩) = canonicalPose5_241.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_241 (box := canonicalBox5_241) (k := keys5Chunk7.get ⟨17, by decide⟩) (canonicalMatch5_241) (canonicalDecode5_241)

def canonicalPose5_242 : Pose 5 :=
  ⟨canonicalPerm5_4, ![false, false, false, true, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_242 : BoxKey 5 :=
  ⟨![30720, 29760, 32640, 0, 31680], ![300, 240, 420, 0, 360], ![30795, 29840, 32710, -80, 31752], true⟩

theorem canonicalMatch5_242 :
    canonicalPose5_242.boxKey 19200 (referenceBox5 (!canonicalBox5_242.bump)) = canonicalBox5_242 := by decide

theorem canonicalDecode5_242 : canonicalBox5_242.toKeyData 19200 = keys5Chunk7.get ⟨18, by decide⟩ := by
  change canonicalBox5_242.toKeyData 19200 = ⟨![(8 / 5), (31 / 20), (17 / 10), 0, (33 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(2053 / 1280), (373 / 240), (3271 / 1920), (-1 / 240), (1323 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_242, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_242, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_242, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_242 : keySolid (keys5Chunk7.get ⟨18, by decide⟩) = canonicalPose5_242.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_242 (box := canonicalBox5_242) (k := keys5Chunk7.get ⟨18, by decide⟩) (canonicalMatch5_242) (canonicalDecode5_242)

def canonicalPose5_243 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, false, false, false, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_243 : BoxKey 5 :=
  ⟨![31680, 32640, 30720, 0, 29760], ![360, 420, 300, 0, 240], ![31752, 32710, 30795, 80, 29840], false⟩

theorem canonicalMatch5_243 :
    canonicalPose5_243.boxKey 19200 (referenceBox5 (!canonicalBox5_243.bump)) = canonicalBox5_243 := by decide

theorem canonicalDecode5_243 : canonicalBox5_243.toKeyData 19200 = keys5Chunk7.get ⟨19, by decide⟩ := by
  change canonicalBox5_243.toKeyData 19200 = ⟨![(33 / 20), (17 / 10), (8 / 5), 0, (31 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(1323 / 800), (3271 / 1920), (2053 / 1280), (1 / 240), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_243, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_243, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_243, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_243 : keySolid (keys5Chunk7.get ⟨19, by decide⟩) = canonicalPose5_243.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_243 (box := canonicalBox5_243) (k := keys5Chunk7.get ⟨19, by decide⟩) (canonicalMatch5_243) (canonicalDecode5_243)

def canonicalPose5_244 : Pose 5 :=
  ⟨canonicalPerm5_14, ![false, false, false, false, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_244 : BoxKey 5 :=
  ⟨![32640, 31680, 29760, 0, 30720], ![420, 360, 240, 0, 300], ![32710, 31752, 29840, 80, 30795], false⟩

theorem canonicalMatch5_244 :
    canonicalPose5_244.boxKey 19200 (referenceBox5 (!canonicalBox5_244.bump)) = canonicalBox5_244 := by decide

theorem canonicalDecode5_244 : canonicalBox5_244.toKeyData 19200 = keys5Chunk7.get ⟨20, by decide⟩ := by
  change canonicalBox5_244.toKeyData 19200 = ⟨![(17 / 10), (33 / 20), (31 / 20), 0, (8 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(3271 / 1920), (1323 / 800), (373 / 240), (1 / 240), (2053 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_244, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_244, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_244, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_244 : keySolid (keys5Chunk7.get ⟨20, by decide⟩) = canonicalPose5_244.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_244 (box := canonicalBox5_244) (k := keys5Chunk7.get ⟨20, by decide⟩) (canonicalMatch5_244) (canonicalDecode5_244)

def canonicalPose5_245 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, true, false, false, true], ![1, 2, 1, 1, 2]⟩
def canonicalBox5_245 : BoxKey 5 :=
  ⟨![31680, 24960, 30720, 19200, 27840], ![360, 420, 300, 0, 240], ![31752, 24890, 30795, 19280, 27760], true⟩

theorem canonicalMatch5_245 :
    canonicalPose5_245.boxKey 19200 (referenceBox5 (!canonicalBox5_245.bump)) = canonicalBox5_245 := by decide

theorem canonicalDecode5_245 : canonicalBox5_245.toKeyData 19200 = keys5Chunk7.get ⟨21, by decide⟩ := by
  change canonicalBox5_245.toKeyData 19200 = ⟨![(33 / 20), (13 / 10), (8 / 5), 1, (29 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(1323 / 800), (2489 / 1920), (2053 / 1280), (241 / 240), (347 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_245, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_245, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_245, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_245 : keySolid (keys5Chunk7.get ⟨21, by decide⟩) = canonicalPose5_245.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_245 (box := canonicalBox5_245) (k := keys5Chunk7.get ⟨21, by decide⟩) (canonicalMatch5_245) (canonicalDecode5_245)

def canonicalPose5_246 : Pose 5 :=
  ⟨canonicalPerm5_12, ![false, false, true, false, false], ![1, 1, 2, 0, 2]⟩
def canonicalBox5_246 : BoxKey 5 :=
  ⟨![32640, 29760, 26880, 12480, 38400], ![420, 240, 300, 360, 0], ![32710, 29840, 26805, 12552, 38480], true⟩

theorem canonicalMatch5_246 :
    canonicalPose5_246.boxKey 19200 (referenceBox5 (!canonicalBox5_246.bump)) = canonicalBox5_246 := by decide

theorem canonicalDecode5_246 : canonicalBox5_246.toKeyData 19200 = keys5Chunk7.get ⟨22, by decide⟩ := by
  change canonicalBox5_246.toKeyData 19200 = ⟨![(17 / 10), (31 / 20), (7 / 5), (13 / 20), 2], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(3271 / 1920), (373 / 240), (1787 / 1280), (523 / 800), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_246, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_246, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_246, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_246 : keySolid (keys5Chunk7.get ⟨22, by decide⟩) = canonicalPose5_246.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_246 (box := canonicalBox5_246) (k := keys5Chunk7.get ⟨22, by decide⟩) (canonicalMatch5_246) (canonicalDecode5_246)

def canonicalPose5_247 : Pose 5 :=
  ⟨canonicalPerm5_19, ![false, false, false, true, false], ![2, 1, 1, 2, 0]⟩
def canonicalBox5_247 : BoxKey 5 :=
  ⟨![38400, 32640, 29760, 26880, 12480], ![0, 420, 240, 300, 360], ![38480, 32710, 29840, 26805, 12552], true⟩

theorem canonicalMatch5_247 :
    canonicalPose5_247.boxKey 19200 (referenceBox5 (!canonicalBox5_247.bump)) = canonicalBox5_247 := by decide

theorem canonicalDecode5_247 : canonicalBox5_247.toKeyData 19200 = keys5Chunk7.get ⟨23, by decide⟩ := by
  change canonicalBox5_247.toKeyData 19200 = ⟨![2, (17 / 10), (31 / 20), (7 / 5), (13 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(481 / 240), (3271 / 1920), (373 / 240), (1787 / 1280), (523 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_247, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_247, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_247, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_247 : keySolid (keys5Chunk7.get ⟨23, by decide⟩) = canonicalPose5_247.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_247 (box := canonicalBox5_247) (k := keys5Chunk7.get ⟨23, by decide⟩) (canonicalMatch5_247) (canonicalDecode5_247)

def canonicalPose5_248 : Pose 5 :=
  ⟨canonicalPerm5_3, ![false, true, true, false, false], ![1, 2, 2, 1, 0]⟩
def canonicalBox5_248 : BoxKey 5 :=
  ⟨![29760, 38400, 26880, 32640, 12480], ![240, 0, 300, 420, 360], ![29840, 38320, 26805, 32710, 12552], false⟩

theorem canonicalMatch5_248 :
    canonicalPose5_248.boxKey 19200 (referenceBox5 (!canonicalBox5_248.bump)) = canonicalBox5_248 := by decide

theorem canonicalDecode5_248 : canonicalBox5_248.toKeyData 19200 = keys5Chunk7.get ⟨24, by decide⟩ := by
  change canonicalBox5_248.toKeyData 19200 = ⟨![(31 / 20), 2, (7 / 5), (17 / 10), (13 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(373 / 240), (479 / 240), (1787 / 1280), (3271 / 1920), (523 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_248, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_248, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_248, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_248 : keySolid (keys5Chunk7.get ⟨24, by decide⟩) = canonicalPose5_248.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_248 (box := canonicalBox5_248) (k := keys5Chunk7.get ⟨24, by decide⟩) (canonicalMatch5_248) (canonicalDecode5_248)

def canonicalPose5_249 : Pose 5 :=
  ⟨canonicalPerm5_13, ![false, true, true, false, false], ![1, 2, 2, 1, 0]⟩
def canonicalBox5_249 : BoxKey 5 :=
  ⟨![32640, 26880, 38400, 29760, 12480], ![420, 300, 0, 240, 360], ![32710, 26805, 38320, 29840, 12552], false⟩

theorem canonicalMatch5_249 :
    canonicalPose5_249.boxKey 19200 (referenceBox5 (!canonicalBox5_249.bump)) = canonicalBox5_249 := by decide

theorem canonicalDecode5_249 : canonicalBox5_249.toKeyData 19200 = keys5Chunk7.get ⟨25, by decide⟩ := by
  change canonicalBox5_249.toKeyData 19200 = ⟨![(17 / 10), (7 / 5), 2, (31 / 20), (13 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(3271 / 1920), (1787 / 1280), (479 / 240), (373 / 240), (523 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_249, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_249, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_249, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_249 : keySolid (keys5Chunk7.get ⟨25, by decide⟩) = canonicalPose5_249.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_249 (box := canonicalBox5_249) (k := keys5Chunk7.get ⟨25, by decide⟩) (canonicalMatch5_249) (canonicalDecode5_249)

def canonicalPose5_250 : Pose 5 :=
  ⟨canonicalPerm5_4, ![true, false, false, false, false], ![2, 1, 1, 2, 0]⟩
def canonicalBox5_250 : BoxKey 5 :=
  ⟨![26880, 29760, 32640, 38400, 12480], ![300, 240, 420, 0, 360], ![26805, 29840, 32710, 38480, 12552], true⟩

theorem canonicalMatch5_250 :
    canonicalPose5_250.boxKey 19200 (referenceBox5 (!canonicalBox5_250.bump)) = canonicalBox5_250 := by decide

theorem canonicalDecode5_250 : canonicalBox5_250.toKeyData 19200 = keys5Chunk7.get ⟨26, by decide⟩ := by
  change canonicalBox5_250.toKeyData 19200 = ⟨![(7 / 5), (31 / 20), (17 / 10), 2, (13 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(1787 / 1280), (373 / 240), (3271 / 1920), (481 / 240), (523 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_250, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_250, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_250, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_250 : keySolid (keys5Chunk7.get ⟨26, by decide⟩) = canonicalPose5_250.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_250 (box := canonicalBox5_250) (k := keys5Chunk7.get ⟨26, by decide⟩) (canonicalMatch5_250) (canonicalDecode5_250)

def canonicalPose5_251 : Pose 5 :=
  ⟨canonicalPerm5_1, ![false, false, false, false, false], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_251 : BoxKey 5 :=
  ⟨![29760, 31680, 32640, 30720, 0], ![240, 360, 420, 300, 0], ![29840, 31752, 32710, 30795, 80], false⟩

theorem canonicalMatch5_251 :
    canonicalPose5_251.boxKey 19200 (referenceBox5 (!canonicalBox5_251.bump)) = canonicalBox5_251 := by decide

theorem canonicalDecode5_251 : canonicalBox5_251.toKeyData 19200 = keys5Chunk7.get ⟨27, by decide⟩ := by
  change canonicalBox5_251.toKeyData 19200 = ⟨![(31 / 20), (33 / 20), (17 / 10), (8 / 5), 0], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(373 / 240), (1323 / 800), (3271 / 1920), (2053 / 1280), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_251, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_251, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_251, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_251 : keySolid (keys5Chunk7.get ⟨27, by decide⟩) = canonicalPose5_251.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_251 (box := canonicalBox5_251) (k := keys5Chunk7.get ⟨27, by decide⟩) (canonicalMatch5_251) (canonicalDecode5_251)

def canonicalPose5_252 : Pose 5 :=
  ⟨canonicalPerm5_6, ![false, false, false, false, false], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_252 : BoxKey 5 :=
  ⟨![30720, 32640, 31680, 29760, 0], ![300, 420, 360, 240, 0], ![30795, 32710, 31752, 29840, 80], false⟩

theorem canonicalMatch5_252 :
    canonicalPose5_252.boxKey 19200 (referenceBox5 (!canonicalBox5_252.bump)) = canonicalBox5_252 := by decide

theorem canonicalDecode5_252 : canonicalBox5_252.toKeyData 19200 = keys5Chunk7.get ⟨28, by decide⟩ := by
  change canonicalBox5_252.toKeyData 19200 = ⟨![(8 / 5), (17 / 10), (33 / 20), (31 / 20), 0], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(2053 / 1280), (3271 / 1920), (1323 / 800), (373 / 240), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_252, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_252, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_252, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_252 : keySolid (keys5Chunk7.get ⟨28, by decide⟩) = canonicalPose5_252.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_252 (box := canonicalBox5_252) (k := keys5Chunk7.get ⟨28, by decide⟩) (canonicalMatch5_252) (canonicalDecode5_252)

def canonicalPose5_253 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, false, false, false, true], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_253 : BoxKey 5 :=
  ⟨![31680, 30720, 29760, 32640, 0], ![360, 300, 240, 420, 0], ![31752, 30795, 29840, 32710, -80], true⟩

theorem canonicalMatch5_253 :
    canonicalPose5_253.boxKey 19200 (referenceBox5 (!canonicalBox5_253.bump)) = canonicalBox5_253 := by decide

theorem canonicalDecode5_253 : canonicalBox5_253.toKeyData 19200 = keys5Chunk7.get ⟨29, by decide⟩ := by
  change canonicalBox5_253.toKeyData 19200 = ⟨![(33 / 20), (8 / 5), (31 / 20), (17 / 10), 0], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(1323 / 800), (2053 / 1280), (373 / 240), (3271 / 1920), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_253, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_253, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_253, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_253 : keySolid (keys5Chunk7.get ⟨29, by decide⟩) = canonicalPose5_253.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_253 (box := canonicalBox5_253) (k := keys5Chunk7.get ⟨29, by decide⟩) (canonicalMatch5_253) (canonicalDecode5_253)

def canonicalPose5_254 : Pose 5 :=
  ⟨canonicalPerm5_12, ![false, false, false, false, true], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_254 : BoxKey 5 :=
  ⟨![32640, 29760, 30720, 31680, 0], ![420, 240, 300, 360, 0], ![32710, 29840, 30795, 31752, -80], true⟩

theorem canonicalMatch5_254 :
    canonicalPose5_254.boxKey 19200 (referenceBox5 (!canonicalBox5_254.bump)) = canonicalBox5_254 := by decide

theorem canonicalDecode5_254 : canonicalBox5_254.toKeyData 19200 = keys5Chunk7.get ⟨30, by decide⟩ := by
  change canonicalBox5_254.toKeyData 19200 = ⟨![(17 / 10), (31 / 20), (8 / 5), (33 / 20), 0], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(3271 / 1920), (373 / 240), (2053 / 1280), (1323 / 800), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_254, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_254, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_254, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_254 : keySolid (keys5Chunk7.get ⟨30, by decide⟩) = canonicalPose5_254.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_254 (box := canonicalBox5_254) (k := keys5Chunk7.get ⟨30, by decide⟩) (canonicalMatch5_254) (canonicalDecode5_254)

def canonicalPose5_255 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, false, true, true, true], ![1, 1, 2, 2, 1]⟩
def canonicalBox5_255 : BoxKey 5 :=
  ⟨![31680, 30720, 27840, 24960, 19200], ![360, 300, 240, 420, 0], ![31752, 30795, 27760, 24890, 19120], false⟩

theorem canonicalMatch5_255 :
    canonicalPose5_255.boxKey 19200 (referenceBox5 (!canonicalBox5_255.bump)) = canonicalBox5_255 := by decide

theorem canonicalDecode5_255 : canonicalBox5_255.toKeyData 19200 = keys5Chunk7.get ⟨31, by decide⟩ := by
  change canonicalBox5_255.toKeyData 19200 = ⟨![(33 / 20), (8 / 5), (29 / 20), (13 / 10), 1], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(1323 / 800), (2053 / 1280), (347 / 240), (2489 / 1920), (239 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_255, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_255, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_255, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_255 : keySolid (keys5Chunk7.get ⟨31, by decide⟩) = canonicalPose5_255.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_255 (box := canonicalBox5_255) (k := keys5Chunk7.get ⟨31, by decide⟩) (canonicalMatch5_255) (canonicalDecode5_255)

theorem keys5Chunk7_canonical : ∀ k ∈ keys5Chunk7,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk7, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_224, canonicalSolid5_224⟩
  · exact ⟨canonicalPose5_225, canonicalSolid5_225⟩
  · exact ⟨canonicalPose5_226, canonicalSolid5_226⟩
  · exact ⟨canonicalPose5_227, canonicalSolid5_227⟩
  · exact ⟨canonicalPose5_228, canonicalSolid5_228⟩
  · exact ⟨canonicalPose5_229, canonicalSolid5_229⟩
  · exact ⟨canonicalPose5_230, canonicalSolid5_230⟩
  · exact ⟨canonicalPose5_231, canonicalSolid5_231⟩
  · exact ⟨canonicalPose5_232, canonicalSolid5_232⟩
  · exact ⟨canonicalPose5_233, canonicalSolid5_233⟩
  · exact ⟨canonicalPose5_234, canonicalSolid5_234⟩
  · exact ⟨canonicalPose5_235, canonicalSolid5_235⟩
  · exact ⟨canonicalPose5_236, canonicalSolid5_236⟩
  · exact ⟨canonicalPose5_237, canonicalSolid5_237⟩
  · exact ⟨canonicalPose5_238, canonicalSolid5_238⟩
  · exact ⟨canonicalPose5_239, canonicalSolid5_239⟩
  · exact ⟨canonicalPose5_240, canonicalSolid5_240⟩
  · exact ⟨canonicalPose5_241, canonicalSolid5_241⟩
  · exact ⟨canonicalPose5_242, canonicalSolid5_242⟩
  · exact ⟨canonicalPose5_243, canonicalSolid5_243⟩
  · exact ⟨canonicalPose5_244, canonicalSolid5_244⟩
  · exact ⟨canonicalPose5_245, canonicalSolid5_245⟩
  · exact ⟨canonicalPose5_246, canonicalSolid5_246⟩
  · exact ⟨canonicalPose5_247, canonicalSolid5_247⟩
  · exact ⟨canonicalPose5_248, canonicalSolid5_248⟩
  · exact ⟨canonicalPose5_249, canonicalSolid5_249⟩
  · exact ⟨canonicalPose5_250, canonicalSolid5_250⟩
  · exact ⟨canonicalPose5_251, canonicalSolid5_251⟩
  · exact ⟨canonicalPose5_252, canonicalSolid5_252⟩
  · exact ⟨canonicalPose5_253, canonicalSolid5_253⟩
  · exact ⟨canonicalPose5_254, canonicalSolid5_254⟩
  · exact ⟨canonicalPose5_255, canonicalSolid5_255⟩

#print axioms keys5Chunk7_canonical

end SparseMonotiles.Canonical
