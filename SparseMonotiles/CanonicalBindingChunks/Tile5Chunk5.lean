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

def canonicalPose5_160 : Pose 5 :=
  ⟨canonicalPerm5_1, ![false, true, true, false, false], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_160 : BoxKey 5 :=
  ⟨![29760, 6720, 5760, 30720, 38400], ![240, 360, 420, 300, 0], ![29840, 6648, 5690, 30795, 38480], true⟩

theorem canonicalMatch5_160 :
    canonicalPose5_160.boxKey 19200 (referenceBox5 (!canonicalBox5_160.bump)) = canonicalBox5_160 := by decide

theorem canonicalDecode5_160 : canonicalBox5_160.toKeyData 19200 = keys5Chunk5.get ⟨0, by decide⟩ := by
  change canonicalBox5_160.toKeyData 19200 = ⟨![(31 / 20), (7 / 20), (3 / 10), (8 / 5), 2], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(373 / 240), (277 / 800), (569 / 1920), (2053 / 1280), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_160, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_160, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_160, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_160 : keySolid (keys5Chunk5.get ⟨0, by decide⟩) = canonicalPose5_160.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_160 (box := canonicalBox5_160) (k := keys5Chunk5.get ⟨0, by decide⟩) (canonicalMatch5_160) (canonicalDecode5_160)

def canonicalPose5_161 : Pose 5 :=
  ⟨canonicalPerm5_6, ![false, true, true, false, false], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_161 : BoxKey 5 :=
  ⟨![30720, 5760, 6720, 29760, 38400], ![300, 420, 360, 240, 0], ![30795, 5690, 6648, 29840, 38480], true⟩

theorem canonicalMatch5_161 :
    canonicalPose5_161.boxKey 19200 (referenceBox5 (!canonicalBox5_161.bump)) = canonicalBox5_161 := by decide

theorem canonicalDecode5_161 : canonicalBox5_161.toKeyData 19200 = keys5Chunk5.get ⟨1, by decide⟩ := by
  change canonicalBox5_161.toKeyData 19200 = ⟨![(8 / 5), (3 / 10), (7 / 20), (31 / 20), 2], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(2053 / 1280), (569 / 1920), (277 / 800), (373 / 240), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_161, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_161, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_161, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_161 : keySolid (keys5Chunk5.get ⟨1, by decide⟩) = canonicalPose5_161.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_161 (box := canonicalBox5_161) (k := keys5Chunk5.get ⟨1, by decide⟩) (canonicalMatch5_161) (canonicalDecode5_161)

def canonicalPose5_162 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, true, true, false, true], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_162 : BoxKey 5 :=
  ⟨![31680, 7680, 8640, 32640, 38400], ![360, 300, 240, 420, 0], ![31752, 7605, 8560, 32710, 38320], false⟩

theorem canonicalMatch5_162 :
    canonicalPose5_162.boxKey 19200 (referenceBox5 (!canonicalBox5_162.bump)) = canonicalBox5_162 := by decide

theorem canonicalDecode5_162 : canonicalBox5_162.toKeyData 19200 = keys5Chunk5.get ⟨2, by decide⟩ := by
  change canonicalBox5_162.toKeyData 19200 = ⟨![(33 / 20), (2 / 5), (9 / 20), (17 / 10), 2], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(1323 / 800), (507 / 1280), (107 / 240), (3271 / 1920), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_162, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_162, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_162, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_162 : keySolid (keys5Chunk5.get ⟨2, by decide⟩) = canonicalPose5_162.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_162 (box := canonicalBox5_162) (k := keys5Chunk5.get ⟨2, by decide⟩) (canonicalMatch5_162) (canonicalDecode5_162)

def canonicalPose5_163 : Pose 5 :=
  ⟨canonicalPerm5_12, ![false, true, true, false, true], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_163 : BoxKey 5 :=
  ⟨![32640, 8640, 7680, 31680, 38400], ![420, 240, 300, 360, 0], ![32710, 8560, 7605, 31752, 38320], false⟩

theorem canonicalMatch5_163 :
    canonicalPose5_163.boxKey 19200 (referenceBox5 (!canonicalBox5_163.bump)) = canonicalBox5_163 := by decide

theorem canonicalDecode5_163 : canonicalBox5_163.toKeyData 19200 = keys5Chunk5.get ⟨3, by decide⟩ := by
  change canonicalBox5_163.toKeyData 19200 = ⟨![(17 / 10), (9 / 20), (2 / 5), (33 / 20), 2], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(3271 / 1920), (107 / 240), (507 / 1280), (1323 / 800), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_163, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_163, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_163, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_163 : keySolid (keys5Chunk5.get ⟨3, by decide⟩) = canonicalPose5_163.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_163 (box := canonicalBox5_163) (k := keys5Chunk5.get ⟨3, by decide⟩) (canonicalMatch5_163) (canonicalDecode5_163)

def canonicalPose5_164 : Pose 5 :=
  ⟨canonicalPerm5_18, ![false, false, true, true, true], ![2, 0, 2, 1, 1]⟩
def canonicalBox5_164 : BoxKey 5 :=
  ⟨![38400, 12480, 26880, 8640, 5760], ![0, 360, 300, 240, 420], ![38480, 12552, 26805, 8560, 5690], true⟩

theorem canonicalMatch5_164 :
    canonicalPose5_164.boxKey 19200 (referenceBox5 (!canonicalBox5_164.bump)) = canonicalBox5_164 := by decide

theorem canonicalDecode5_164 : canonicalBox5_164.toKeyData 19200 = keys5Chunk5.get ⟨4, by decide⟩ := by
  change canonicalBox5_164.toKeyData 19200 = ⟨![2, (13 / 20), (7 / 5), (9 / 20), (3 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(481 / 240), (523 / 800), (1787 / 1280), (107 / 240), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_164, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_164, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_164, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_164 : keySolid (keys5Chunk5.get ⟨4, by decide⟩) = canonicalPose5_164.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_164 (box := canonicalBox5_164) (k := keys5Chunk5.get ⟨4, by decide⟩) (canonicalMatch5_164) (canonicalDecode5_164)

def canonicalPose5_165 : Pose 5 :=
  ⟨canonicalPerm5_3, ![false, false, false, true, true], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_165 : BoxKey 5 :=
  ⟨![29760, 0, 30720, 5760, 6720], ![240, 0, 300, 420, 360], ![29840, 80, 30795, 5690, 6648], false⟩

theorem canonicalMatch5_165 :
    canonicalPose5_165.boxKey 19200 (referenceBox5 (!canonicalBox5_165.bump)) = canonicalBox5_165 := by decide

theorem canonicalDecode5_165 : canonicalBox5_165.toKeyData 19200 = keys5Chunk5.get ⟨5, by decide⟩ := by
  change canonicalBox5_165.toKeyData 19200 = ⟨![(31 / 20), 0, (8 / 5), (3 / 10), (7 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(373 / 240), (1 / 240), (2053 / 1280), (569 / 1920), (277 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_165, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_165, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_165, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_165 : keySolid (keys5Chunk5.get ⟨5, by decide⟩) = canonicalPose5_165.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_165 (box := canonicalBox5_165) (k := keys5Chunk5.get ⟨5, by decide⟩) (canonicalMatch5_165) (canonicalDecode5_165)

def canonicalPose5_166 : Pose 5 :=
  ⟨canonicalPerm5_7, ![false, false, false, true, true], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_166 : BoxKey 5 :=
  ⟨![30720, 0, 29760, 6720, 5760], ![300, 0, 240, 360, 420], ![30795, 80, 29840, 6648, 5690], false⟩

theorem canonicalMatch5_166 :
    canonicalPose5_166.boxKey 19200 (referenceBox5 (!canonicalBox5_166.bump)) = canonicalBox5_166 := by decide

theorem canonicalDecode5_166 : canonicalBox5_166.toKeyData 19200 = keys5Chunk5.get ⟨6, by decide⟩ := by
  change canonicalBox5_166.toKeyData 19200 = ⟨![(8 / 5), 0, (31 / 20), (7 / 20), (3 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(2053 / 1280), (1 / 240), (373 / 240), (277 / 800), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_166, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_166, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_166, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_166 : keySolid (keys5Chunk5.get ⟨6, by decide⟩) = canonicalPose5_166.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_166 (box := canonicalBox5_166) (k := keys5Chunk5.get ⟨6, by decide⟩) (canonicalMatch5_166) (canonicalDecode5_166)

def canonicalPose5_167 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, true, false, true, true], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_167 : BoxKey 5 :=
  ⟨![31680, 0, 32640, 8640, 7680], ![360, 0, 420, 240, 300], ![31752, -80, 32710, 8560, 7605], true⟩

theorem canonicalMatch5_167 :
    canonicalPose5_167.boxKey 19200 (referenceBox5 (!canonicalBox5_167.bump)) = canonicalBox5_167 := by decide

theorem canonicalDecode5_167 : canonicalBox5_167.toKeyData 19200 = keys5Chunk5.get ⟨7, by decide⟩ := by
  change canonicalBox5_167.toKeyData 19200 = ⟨![(33 / 20), 0, (17 / 10), (9 / 20), (2 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(1323 / 800), (-1 / 240), (3271 / 1920), (107 / 240), (507 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_167, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_167, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_167, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_167 : keySolid (keys5Chunk5.get ⟨7, by decide⟩) = canonicalPose5_167.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_167 (box := canonicalBox5_167) (k := keys5Chunk5.get ⟨7, by decide⟩) (canonicalMatch5_167) (canonicalDecode5_167)

def canonicalPose5_168 : Pose 5 :=
  ⟨canonicalPerm5_15, ![false, true, false, true, true], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_168 : BoxKey 5 :=
  ⟨![32640, 0, 31680, 7680, 8640], ![420, 0, 360, 300, 240], ![32710, -80, 31752, 7605, 8560], true⟩

theorem canonicalMatch5_168 :
    canonicalPose5_168.boxKey 19200 (referenceBox5 (!canonicalBox5_168.bump)) = canonicalBox5_168 := by decide

theorem canonicalDecode5_168 : canonicalBox5_168.toKeyData 19200 = keys5Chunk5.get ⟨8, by decide⟩ := by
  change canonicalBox5_168.toKeyData 19200 = ⟨![(17 / 10), 0, (33 / 20), (2 / 5), (9 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(3271 / 1920), (-1 / 240), (1323 / 800), (507 / 1280), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_168, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_168, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_168, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_168 : keySolid (keys5Chunk5.get ⟨8, by decide⟩) = canonicalPose5_168.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_168 (box := canonicalBox5_168) (k := keys5Chunk5.get ⟨8, by decide⟩) (canonicalMatch5_168) (canonicalDecode5_168)

def canonicalPose5_169 : Pose 5 :=
  ⟨canonicalPerm5_5, ![true, false, false, true, true], ![2, 0, 2, 1, 1]⟩
def canonicalBox5_169 : BoxKey 5 :=
  ⟨![26880, 12480, 38400, 5760, 8640], ![300, 360, 0, 420, 240], ![26805, 12552, 38480, 5690, 8560], true⟩

theorem canonicalMatch5_169 :
    canonicalPose5_169.boxKey 19200 (referenceBox5 (!canonicalBox5_169.bump)) = canonicalBox5_169 := by decide

theorem canonicalDecode5_169 : canonicalBox5_169.toKeyData 19200 = keys5Chunk5.get ⟨9, by decide⟩ := by
  change canonicalBox5_169.toKeyData 19200 = ⟨![(7 / 5), (13 / 20), 2, (3 / 10), (9 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(1787 / 1280), (523 / 800), (481 / 240), (569 / 1920), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_169, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_169, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_169, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_169 : keySolid (keys5Chunk5.get ⟨9, by decide⟩) = canonicalPose5_169.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_169 (box := canonicalBox5_169) (k := keys5Chunk5.get ⟨9, by decide⟩) (canonicalMatch5_169) (canonicalDecode5_169)

def canonicalPose5_170 : Pose 5 :=
  ⟨canonicalPerm5_14, ![false, false, false, false, false], ![1, 0, 1, 0, 0]⟩
def canonicalBox5_170 : BoxKey 5 :=
  ⟨![32640, 12480, 29760, 0, 11520], ![420, 360, 240, 0, 300], ![32710, 12552, 29840, 80, 11595], false⟩

theorem canonicalMatch5_170 :
    canonicalPose5_170.boxKey 19200 (referenceBox5 (!canonicalBox5_170.bump)) = canonicalBox5_170 := by decide

theorem canonicalDecode5_170 : canonicalBox5_170.toKeyData 19200 = keys5Chunk5.get ⟨10, by decide⟩ := by
  change canonicalBox5_170.toKeyData 19200 = ⟨![(17 / 10), (13 / 20), (31 / 20), 0, (3 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(3271 / 1920), (523 / 800), (373 / 240), (1 / 240), (773 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_170, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_170, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_170, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_170 : keySolid (keys5Chunk5.get ⟨10, by decide⟩) = canonicalPose5_170.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_170 (box := canonicalBox5_170) (k := keys5Chunk5.get ⟨10, by decide⟩) (canonicalMatch5_170) (canonicalDecode5_170)

def canonicalPose5_171 : Pose 5 :=
  ⟨canonicalPerm5_1, ![false, false, false, false, false], ![1, 0, 1, 0, 0]⟩
def canonicalBox5_171 : BoxKey 5 :=
  ⟨![29760, 12480, 32640, 11520, 0], ![240, 360, 420, 300, 0], ![29840, 12552, 32710, 11595, 80], false⟩

theorem canonicalMatch5_171 :
    canonicalPose5_171.boxKey 19200 (referenceBox5 (!canonicalBox5_171.bump)) = canonicalBox5_171 := by decide

theorem canonicalDecode5_171 : canonicalBox5_171.toKeyData 19200 = keys5Chunk5.get ⟨11, by decide⟩ := by
  change canonicalBox5_171.toKeyData 19200 = ⟨![(31 / 20), (13 / 20), (17 / 10), (3 / 5), 0], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(373 / 240), (523 / 800), (3271 / 1920), (773 / 1280), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_171, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_171, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_171, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_171 : keySolid (keys5Chunk5.get ⟨11, by decide⟩) = canonicalPose5_171.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_171 (box := canonicalBox5_171) (k := keys5Chunk5.get ⟨11, by decide⟩) (canonicalMatch5_171) (canonicalDecode5_171)

def canonicalPose5_172 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, true, true, true, true], ![2, 1, 2, 1, 2]⟩
def canonicalBox5_172 : BoxKey 5 :=
  ⟨![38400, 8640, 25920, 5760, 26880], ![0, 240, 360, 420, 300], ![38480, 8560, 25848, 5690, 26805], true⟩

theorem canonicalMatch5_172 :
    canonicalPose5_172.boxKey 19200 (referenceBox5 (!canonicalBox5_172.bump)) = canonicalBox5_172 := by decide

theorem canonicalDecode5_172 : canonicalBox5_172.toKeyData 19200 = keys5Chunk5.get ⟨12, by decide⟩ := by
  change canonicalBox5_172.toKeyData 19200 = ⟨![2, (9 / 20), (27 / 20), (3 / 10), (7 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(481 / 240), (107 / 240), (1077 / 800), (569 / 1920), (1787 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_172, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_172, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_172, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_172 : keySolid (keys5Chunk5.get ⟨12, by decide⟩) = canonicalPose5_172.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_172 (box := canonicalBox5_172) (k := keys5Chunk5.get ⟨12, by decide⟩) (canonicalMatch5_172) (canonicalDecode5_172)

def canonicalPose5_173 : Pose 5 :=
  ⟨canonicalPerm5_15, ![false, false, true, false, false], ![1, 0, 2, 0, 1]⟩
def canonicalBox5_173 : BoxKey 5 :=
  ⟨![32640, 0, 25920, 11520, 29760], ![420, 0, 360, 300, 240], ![32710, 80, 25848, 11595, 29840], false⟩

theorem canonicalMatch5_173 :
    canonicalPose5_173.boxKey 19200 (referenceBox5 (!canonicalBox5_173.bump)) = canonicalBox5_173 := by decide

theorem canonicalDecode5_173 : canonicalBox5_173.toKeyData 19200 = keys5Chunk5.get ⟨13, by decide⟩ := by
  change canonicalBox5_173.toKeyData 19200 = ⟨![(17 / 10), 0, (27 / 20), (3 / 5), (31 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(3271 / 1920), (1 / 240), (1077 / 800), (773 / 1280), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_173, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_173, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_173, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_173 : keySolid (keys5Chunk5.get ⟨13, by decide⟩) = canonicalPose5_173.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_173 (box := canonicalBox5_173) (k := keys5Chunk5.get ⟨13, by decide⟩) (canonicalMatch5_173) (canonicalDecode5_173)

def canonicalPose5_174 : Pose 5 :=
  ⟨canonicalPerm5_2, ![false, true, true, true, false], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_174 : BoxKey 5 :=
  ⟨![29760, 5760, 38400, 6720, 30720], ![240, 420, 0, 360, 300], ![29840, 5690, 38320, 6648, 30795], false⟩

theorem canonicalMatch5_174 :
    canonicalPose5_174.boxKey 19200 (referenceBox5 (!canonicalBox5_174.bump)) = canonicalBox5_174 := by decide

theorem canonicalDecode5_174 : canonicalBox5_174.toKeyData 19200 = keys5Chunk5.get ⟨14, by decide⟩ := by
  change canonicalBox5_174.toKeyData 19200 = ⟨![(31 / 20), (3 / 10), 2, (7 / 20), (8 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(373 / 240), (569 / 1920), (479 / 240), (277 / 800), (2053 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_174, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_174, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_174, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_174 : keySolid (keys5Chunk5.get ⟨14, by decide⟩) = canonicalPose5_174.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_174 (box := canonicalBox5_174) (k := keys5Chunk5.get ⟨14, by decide⟩) (canonicalMatch5_174) (canonicalDecode5_174)

def canonicalPose5_175 : Pose 5 :=
  ⟨canonicalPerm5_5, ![false, true, true, true, false], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_175 : BoxKey 5 :=
  ⟨![30720, 6720, 38400, 5760, 29760], ![300, 360, 0, 420, 240], ![30795, 6648, 38320, 5690, 29840], false⟩

theorem canonicalMatch5_175 :
    canonicalPose5_175.boxKey 19200 (referenceBox5 (!canonicalBox5_175.bump)) = canonicalBox5_175 := by decide

theorem canonicalDecode5_175 : canonicalBox5_175.toKeyData 19200 = keys5Chunk5.get ⟨15, by decide⟩ := by
  change canonicalBox5_175.toKeyData 19200 = ⟨![(8 / 5), (7 / 20), 2, (3 / 10), (31 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(2053 / 1280), (277 / 800), (479 / 240), (569 / 1920), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_175, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_175, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_175, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_175 : keySolid (keys5Chunk5.get ⟨15, by decide⟩) = canonicalPose5_175.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_175 (box := canonicalBox5_175) (k := keys5Chunk5.get ⟨15, by decide⟩) (canonicalMatch5_175) (canonicalDecode5_175)

def canonicalPose5_176 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, true, false, true, false], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_176 : BoxKey 5 :=
  ⟨![31680, 8640, 38400, 7680, 32640], ![360, 240, 0, 300, 420], ![31752, 8560, 38480, 7605, 32710], true⟩

theorem canonicalMatch5_176 :
    canonicalPose5_176.boxKey 19200 (referenceBox5 (!canonicalBox5_176.bump)) = canonicalBox5_176 := by decide

theorem canonicalDecode5_176 : canonicalBox5_176.toKeyData 19200 = keys5Chunk5.get ⟨16, by decide⟩ := by
  change canonicalBox5_176.toKeyData 19200 = ⟨![(33 / 20), (9 / 20), 2, (2 / 5), (17 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(1323 / 800), (107 / 240), (481 / 240), (507 / 1280), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_176, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_176, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_176, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_176 : keySolid (keys5Chunk5.get ⟨16, by decide⟩) = canonicalPose5_176.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_176 (box := canonicalBox5_176) (k := keys5Chunk5.get ⟨16, by decide⟩) (canonicalMatch5_176) (canonicalDecode5_176)

def canonicalPose5_177 : Pose 5 :=
  ⟨canonicalPerm5_13, ![false, true, false, true, false], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_177 : BoxKey 5 :=
  ⟨![32640, 7680, 38400, 8640, 31680], ![420, 300, 0, 240, 360], ![32710, 7605, 38480, 8560, 31752], true⟩

theorem canonicalMatch5_177 :
    canonicalPose5_177.boxKey 19200 (referenceBox5 (!canonicalBox5_177.bump)) = canonicalBox5_177 := by decide

theorem canonicalDecode5_177 : canonicalBox5_177.toKeyData 19200 = keys5Chunk5.get ⟨17, by decide⟩ := by
  change canonicalBox5_177.toKeyData 19200 = ⟨![(17 / 10), (2 / 5), 2, (9 / 20), (33 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(3271 / 1920), (507 / 1280), (481 / 240), (107 / 240), (1323 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_177, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_177, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_177, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_177 : keySolid (keys5Chunk5.get ⟨17, by decide⟩) = canonicalPose5_177.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_177 (box := canonicalBox5_177) (k := keys5Chunk5.get ⟨17, by decide⟩) (canonicalMatch5_177) (canonicalDecode5_177)

def canonicalPose5_178 : Pose 5 :=
  ⟨canonicalPerm5_0, ![false, false, true, false, false], ![1, 0, 2, 0, 1]⟩
def canonicalBox5_178 : BoxKey 5 :=
  ⟨![29760, 11520, 25920, 0, 32640], ![240, 300, 360, 0, 420], ![29840, 11595, 25848, 80, 32710], false⟩

theorem canonicalMatch5_178 :
    canonicalPose5_178.boxKey 19200 (referenceBox5 (!canonicalBox5_178.bump)) = canonicalBox5_178 := by decide

theorem canonicalDecode5_178 : canonicalBox5_178.toKeyData 19200 = keys5Chunk5.get ⟨18, by decide⟩ := by
  change canonicalBox5_178.toKeyData 19200 = ⟨![(31 / 20), (3 / 5), (27 / 20), 0, (17 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(373 / 240), (773 / 1280), (1077 / 800), (1 / 240), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_178, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_178, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_178, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_178 : keySolid (keys5Chunk5.get ⟨18, by decide⟩) = canonicalPose5_178.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_178 (box := canonicalBox5_178) (k := keys5Chunk5.get ⟨18, by decide⟩) (canonicalMatch5_178) (canonicalDecode5_178)

def canonicalPose5_179 : Pose 5 :=
  ⟨canonicalPerm5_6, ![true, true, true, true, false], ![2, 1, 2, 1, 2]⟩
def canonicalBox5_179 : BoxKey 5 :=
  ⟨![26880, 5760, 25920, 8640, 38400], ![300, 420, 360, 240, 0], ![26805, 5690, 25848, 8560, 38480], true⟩

theorem canonicalMatch5_179 :
    canonicalPose5_179.boxKey 19200 (referenceBox5 (!canonicalBox5_179.bump)) = canonicalBox5_179 := by decide

theorem canonicalDecode5_179 : canonicalBox5_179.toKeyData 19200 = keys5Chunk5.get ⟨19, by decide⟩ := by
  change canonicalBox5_179.toKeyData 19200 = ⟨![(7 / 5), (3 / 10), (27 / 20), (9 / 20), 2], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(1787 / 1280), (569 / 1920), (1077 / 800), (107 / 240), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_179, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_179, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_179, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_179 : keySolid (keys5Chunk5.get ⟨19, by decide⟩) = canonicalPose5_179.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_179 (box := canonicalBox5_179) (k := keys5Chunk5.get ⟨19, by decide⟩) (canonicalMatch5_179) (canonicalDecode5_179)

def canonicalPose5_180 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, true, false, false, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_180 : BoxKey 5 :=
  ⟨![38400, 5760, 29760, 30720, 6720], ![0, 420, 240, 300, 360], ![38320, 5690, 29840, 30795, 6648], false⟩

theorem canonicalMatch5_180 :
    canonicalPose5_180.boxKey 19200 (referenceBox5 (!canonicalBox5_180.bump)) = canonicalBox5_180 := by decide

theorem canonicalDecode5_180 : canonicalBox5_180.toKeyData 19200 = keys5Chunk5.get ⟨20, by decide⟩ := by
  change canonicalBox5_180.toKeyData 19200 = ⟨![2, (3 / 10), (31 / 20), (8 / 5), (7 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(479 / 240), (569 / 1920), (373 / 240), (2053 / 1280), (277 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_180, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_180, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_180, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_180 : keySolid (keys5Chunk5.get ⟨20, by decide⟩) = canonicalPose5_180.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_180 (box := canonicalBox5_180) (k := keys5Chunk5.get ⟨20, by decide⟩) (canonicalMatch5_180) (canonicalDecode5_180)

def canonicalPose5_181 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, true, false, false, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_181 : BoxKey 5 :=
  ⟨![38400, 6720, 30720, 29760, 5760], ![0, 360, 300, 240, 420], ![38320, 6648, 30795, 29840, 5690], false⟩

theorem canonicalMatch5_181 :
    canonicalPose5_181.boxKey 19200 (referenceBox5 (!canonicalBox5_181.bump)) = canonicalBox5_181 := by decide

theorem canonicalDecode5_181 : canonicalBox5_181.toKeyData 19200 = keys5Chunk5.get ⟨21, by decide⟩ := by
  change canonicalBox5_181.toKeyData 19200 = ⟨![2, (7 / 20), (8 / 5), (31 / 20), (3 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(479 / 240), (277 / 800), (2053 / 1280), (373 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_181, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_181, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_181, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_181 : keySolid (keys5Chunk5.get ⟨21, by decide⟩) = canonicalPose5_181.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_181 (box := canonicalBox5_181) (k := keys5Chunk5.get ⟨21, by decide⟩) (canonicalMatch5_181) (canonicalDecode5_181)

def canonicalPose5_182 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, true, false, false, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_182 : BoxKey 5 :=
  ⟨![38400, 7680, 32640, 31680, 8640], ![0, 300, 420, 360, 240], ![38480, 7605, 32710, 31752, 8560], true⟩

theorem canonicalMatch5_182 :
    canonicalPose5_182.boxKey 19200 (referenceBox5 (!canonicalBox5_182.bump)) = canonicalBox5_182 := by decide

theorem canonicalDecode5_182 : canonicalBox5_182.toKeyData 19200 = keys5Chunk5.get ⟨22, by decide⟩ := by
  change canonicalBox5_182.toKeyData 19200 = ⟨![2, (2 / 5), (17 / 10), (33 / 20), (9 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(481 / 240), (507 / 1280), (3271 / 1920), (1323 / 800), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_182, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_182, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_182, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_182 : keySolid (keys5Chunk5.get ⟨22, by decide⟩) = canonicalPose5_182.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_182 (box := canonicalBox5_182) (k := keys5Chunk5.get ⟨22, by decide⟩) (canonicalMatch5_182) (canonicalDecode5_182)

def canonicalPose5_183 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, true, false, false, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_183 : BoxKey 5 :=
  ⟨![38400, 8640, 31680, 32640, 7680], ![0, 240, 360, 420, 300], ![38480, 8560, 31752, 32710, 7605], true⟩

theorem canonicalMatch5_183 :
    canonicalPose5_183.boxKey 19200 (referenceBox5 (!canonicalBox5_183.bump)) = canonicalBox5_183 := by decide

theorem canonicalDecode5_183 : canonicalBox5_183.toKeyData 19200 = keys5Chunk5.get ⟨23, by decide⟩ := by
  change canonicalBox5_183.toKeyData 19200 = ⟨![2, (9 / 20), (33 / 20), (17 / 10), (2 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(481 / 240), (107 / 240), (1323 / 800), (3271 / 1920), (507 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_183, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_183, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_183, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_183 : keySolid (keys5Chunk5.get ⟨23, by decide⟩) = canonicalPose5_183.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_183 (box := canonicalBox5_183) (k := keys5Chunk5.get ⟨23, by decide⟩) (canonicalMatch5_183) (canonicalDecode5_183)

def canonicalPose5_184 : Pose 5 :=
  ⟨canonicalPerm5_11, ![true, false, false, false, false], ![2, 0, 1, 1, 0]⟩
def canonicalBox5_184 : BoxKey 5 :=
  ⟨![25920, 0, 32640, 29760, 11520], ![360, 0, 420, 240, 300], ![25848, 80, 32710, 29840, 11595], false⟩

theorem canonicalMatch5_184 :
    canonicalPose5_184.boxKey 19200 (referenceBox5 (!canonicalBox5_184.bump)) = canonicalBox5_184 := by decide

theorem canonicalDecode5_184 : canonicalBox5_184.toKeyData 19200 = keys5Chunk5.get ⟨24, by decide⟩ := by
  change canonicalBox5_184.toKeyData 19200 = ⟨![(27 / 20), 0, (17 / 10), (31 / 20), (3 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(1077 / 800), (1 / 240), (3271 / 1920), (373 / 240), (773 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_184, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_184, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_184, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_184 : keySolid (keys5Chunk5.get ⟨24, by decide⟩) = canonicalPose5_184.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_184 (box := canonicalBox5_184) (k := keys5Chunk5.get ⟨24, by decide⟩) (canonicalMatch5_184) (canonicalDecode5_184)

def canonicalPose5_185 : Pose 5 :=
  ⟨canonicalPerm5_8, ![true, true, false, true, true], ![2, 1, 2, 2, 1]⟩
def canonicalBox5_185 : BoxKey 5 :=
  ⟨![25920, 8640, 38400, 26880, 5760], ![360, 240, 0, 300, 420], ![25848, 8560, 38480, 26805, 5690], true⟩

theorem canonicalMatch5_185 :
    canonicalPose5_185.boxKey 19200 (referenceBox5 (!canonicalBox5_185.bump)) = canonicalBox5_185 := by decide

theorem canonicalDecode5_185 : canonicalBox5_185.toKeyData 19200 = keys5Chunk5.get ⟨25, by decide⟩ := by
  change canonicalBox5_185.toKeyData 19200 = ⟨![(27 / 20), (9 / 20), 2, (7 / 5), (3 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(1077 / 800), (107 / 240), (481 / 240), (1787 / 1280), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_185, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_185, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_185, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_185 : keySolid (keys5Chunk5.get ⟨25, by decide⟩) = canonicalPose5_185.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_185 (box := canonicalBox5_185) (k := keys5Chunk5.get ⟨25, by decide⟩) (canonicalMatch5_185) (canonicalDecode5_185)

def canonicalPose5_186 : Pose 5 :=
  ⟨canonicalPerm5_10, ![true, true, true, false, true], ![2, 1, 2, 2, 1]⟩
def canonicalBox5_186 : BoxKey 5 :=
  ⟨![25920, 5760, 26880, 38400, 8640], ![360, 420, 300, 0, 240], ![25848, 5690, 26805, 38480, 8560], true⟩

theorem canonicalMatch5_186 :
    canonicalPose5_186.boxKey 19200 (referenceBox5 (!canonicalBox5_186.bump)) = canonicalBox5_186 := by decide

theorem canonicalDecode5_186 : canonicalBox5_186.toKeyData 19200 = keys5Chunk5.get ⟨26, by decide⟩ := by
  change canonicalBox5_186.toKeyData 19200 = ⟨![(27 / 20), (3 / 10), (7 / 5), 2, (9 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(1077 / 800), (569 / 1920), (1787 / 1280), (481 / 240), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_186, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_186, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_186, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_186 : keySolid (keys5Chunk5.get ⟨26, by decide⟩) = canonicalPose5_186.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_186 (box := canonicalBox5_186) (k := keys5Chunk5.get ⟨26, by decide⟩) (canonicalMatch5_186) (canonicalDecode5_186)

def canonicalPose5_187 : Pose 5 :=
  ⟨canonicalPerm5_9, ![true, false, false, false, false], ![2, 0, 1, 1, 0]⟩
def canonicalBox5_187 : BoxKey 5 :=
  ⟨![25920, 11520, 29760, 32640, 0], ![360, 300, 240, 420, 0], ![25848, 11595, 29840, 32710, 80], false⟩

theorem canonicalMatch5_187 :
    canonicalPose5_187.boxKey 19200 (referenceBox5 (!canonicalBox5_187.bump)) = canonicalBox5_187 := by decide

theorem canonicalDecode5_187 : canonicalBox5_187.toKeyData 19200 = keys5Chunk5.get ⟨27, by decide⟩ := by
  change canonicalBox5_187.toKeyData 19200 = ⟨![(27 / 20), (3 / 5), (31 / 20), (17 / 10), 0], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(1077 / 800), (773 / 1280), (373 / 240), (3271 / 1920), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_187, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_187, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_187, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_187 : keySolid (keys5Chunk5.get ⟨27, by decide⟩) = canonicalPose5_187.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_187 (box := canonicalBox5_187) (k := keys5Chunk5.get ⟨27, by decide⟩) (canonicalMatch5_187) (canonicalDecode5_187)

def canonicalPose5_188 : Pose 5 :=
  ⟨canonicalPerm5_18, ![false, false, true, false, false], ![2, 0, 2, 1, 1]⟩
def canonicalBox5_188 : BoxKey 5 :=
  ⟨![38400, 12480, 26880, 29760, 32640], ![0, 360, 300, 240, 420], ![38480, 12552, 26805, 29840, 32710], true⟩

theorem canonicalMatch5_188 :
    canonicalPose5_188.boxKey 19200 (referenceBox5 (!canonicalBox5_188.bump)) = canonicalBox5_188 := by decide

theorem canonicalDecode5_188 : canonicalBox5_188.toKeyData 19200 = keys5Chunk5.get ⟨28, by decide⟩ := by
  change canonicalBox5_188.toKeyData 19200 = ⟨![2, (13 / 20), (7 / 5), (31 / 20), (17 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(481 / 240), (523 / 800), (1787 / 1280), (373 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_188, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_188, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_188, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_188 : keySolid (keys5Chunk5.get ⟨28, by decide⟩) = canonicalPose5_188.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_188 (box := canonicalBox5_188) (k := keys5Chunk5.get ⟨28, by decide⟩) (canonicalMatch5_188) (canonicalDecode5_188)

def canonicalPose5_189 : Pose 5 :=
  ⟨canonicalPerm5_3, ![false, false, false, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_189 : BoxKey 5 :=
  ⟨![29760, 0, 30720, 32640, 31680], ![240, 0, 300, 420, 360], ![29840, 80, 30795, 32710, 31752], false⟩

theorem canonicalMatch5_189 :
    canonicalPose5_189.boxKey 19200 (referenceBox5 (!canonicalBox5_189.bump)) = canonicalBox5_189 := by decide

theorem canonicalDecode5_189 : canonicalBox5_189.toKeyData 19200 = keys5Chunk5.get ⟨29, by decide⟩ := by
  change canonicalBox5_189.toKeyData 19200 = ⟨![(31 / 20), 0, (8 / 5), (17 / 10), (33 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(373 / 240), (1 / 240), (2053 / 1280), (3271 / 1920), (1323 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_189, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_189, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_189, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_189 : keySolid (keys5Chunk5.get ⟨29, by decide⟩) = canonicalPose5_189.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_189 (box := canonicalBox5_189) (k := keys5Chunk5.get ⟨29, by decide⟩) (canonicalMatch5_189) (canonicalDecode5_189)

def canonicalPose5_190 : Pose 5 :=
  ⟨canonicalPerm5_7, ![false, false, false, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_190 : BoxKey 5 :=
  ⟨![30720, 0, 29760, 31680, 32640], ![300, 0, 240, 360, 420], ![30795, 80, 29840, 31752, 32710], false⟩

theorem canonicalMatch5_190 :
    canonicalPose5_190.boxKey 19200 (referenceBox5 (!canonicalBox5_190.bump)) = canonicalBox5_190 := by decide

theorem canonicalDecode5_190 : canonicalBox5_190.toKeyData 19200 = keys5Chunk5.get ⟨30, by decide⟩ := by
  change canonicalBox5_190.toKeyData 19200 = ⟨![(8 / 5), 0, (31 / 20), (33 / 20), (17 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(2053 / 1280), (1 / 240), (373 / 240), (1323 / 800), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_190, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_190, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_190, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_190 : keySolid (keys5Chunk5.get ⟨30, by decide⟩) = canonicalPose5_190.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_190 (box := canonicalBox5_190) (k := keys5Chunk5.get ⟨30, by decide⟩) (canonicalMatch5_190) (canonicalDecode5_190)

def canonicalPose5_191 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, true, false, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_191 : BoxKey 5 :=
  ⟨![31680, 0, 32640, 29760, 30720], ![360, 0, 420, 240, 300], ![31752, -80, 32710, 29840, 30795], true⟩

theorem canonicalMatch5_191 :
    canonicalPose5_191.boxKey 19200 (referenceBox5 (!canonicalBox5_191.bump)) = canonicalBox5_191 := by decide

theorem canonicalDecode5_191 : canonicalBox5_191.toKeyData 19200 = keys5Chunk5.get ⟨31, by decide⟩ := by
  change canonicalBox5_191.toKeyData 19200 = ⟨![(33 / 20), 0, (17 / 10), (31 / 20), (8 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(1323 / 800), (-1 / 240), (3271 / 1920), (373 / 240), (2053 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_191, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_191, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_191, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_191 : keySolid (keys5Chunk5.get ⟨31, by decide⟩) = canonicalPose5_191.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_191 (box := canonicalBox5_191) (k := keys5Chunk5.get ⟨31, by decide⟩) (canonicalMatch5_191) (canonicalDecode5_191)

theorem keys5Chunk5_canonical : ∀ k ∈ keys5Chunk5,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk5, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_160, canonicalSolid5_160⟩
  · exact ⟨canonicalPose5_161, canonicalSolid5_161⟩
  · exact ⟨canonicalPose5_162, canonicalSolid5_162⟩
  · exact ⟨canonicalPose5_163, canonicalSolid5_163⟩
  · exact ⟨canonicalPose5_164, canonicalSolid5_164⟩
  · exact ⟨canonicalPose5_165, canonicalSolid5_165⟩
  · exact ⟨canonicalPose5_166, canonicalSolid5_166⟩
  · exact ⟨canonicalPose5_167, canonicalSolid5_167⟩
  · exact ⟨canonicalPose5_168, canonicalSolid5_168⟩
  · exact ⟨canonicalPose5_169, canonicalSolid5_169⟩
  · exact ⟨canonicalPose5_170, canonicalSolid5_170⟩
  · exact ⟨canonicalPose5_171, canonicalSolid5_171⟩
  · exact ⟨canonicalPose5_172, canonicalSolid5_172⟩
  · exact ⟨canonicalPose5_173, canonicalSolid5_173⟩
  · exact ⟨canonicalPose5_174, canonicalSolid5_174⟩
  · exact ⟨canonicalPose5_175, canonicalSolid5_175⟩
  · exact ⟨canonicalPose5_176, canonicalSolid5_176⟩
  · exact ⟨canonicalPose5_177, canonicalSolid5_177⟩
  · exact ⟨canonicalPose5_178, canonicalSolid5_178⟩
  · exact ⟨canonicalPose5_179, canonicalSolid5_179⟩
  · exact ⟨canonicalPose5_180, canonicalSolid5_180⟩
  · exact ⟨canonicalPose5_181, canonicalSolid5_181⟩
  · exact ⟨canonicalPose5_182, canonicalSolid5_182⟩
  · exact ⟨canonicalPose5_183, canonicalSolid5_183⟩
  · exact ⟨canonicalPose5_184, canonicalSolid5_184⟩
  · exact ⟨canonicalPose5_185, canonicalSolid5_185⟩
  · exact ⟨canonicalPose5_186, canonicalSolid5_186⟩
  · exact ⟨canonicalPose5_187, canonicalSolid5_187⟩
  · exact ⟨canonicalPose5_188, canonicalSolid5_188⟩
  · exact ⟨canonicalPose5_189, canonicalSolid5_189⟩
  · exact ⟨canonicalPose5_190, canonicalSolid5_190⟩
  · exact ⟨canonicalPose5_191, canonicalSolid5_191⟩

#print axioms keys5Chunk5_canonical

end SparseMonotiles.Canonical
