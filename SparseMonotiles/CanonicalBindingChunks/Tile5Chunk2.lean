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

def canonicalPose5_64 : Pose 5 :=
  ⟨canonicalPerm5_18, ![false, true, false, true, true], ![0, 2, 0, 1, 1]⟩
def canonicalBox5_64 : BoxKey 5 :=
  ⟨![0, 25920, 11520, 8640, 5760], ![0, 360, 300, 240, 420], ![80, 25848, 11595, 8560, 5690], false⟩

theorem canonicalMatch5_64 :
    canonicalPose5_64.boxKey 19200 (referenceBox5 (!canonicalBox5_64.bump)) = canonicalBox5_64 := by decide

theorem canonicalDecode5_64 : canonicalBox5_64.toKeyData 19200 = keys5Chunk2.get ⟨0, by decide⟩ := by
  change canonicalBox5_64.toKeyData 19200 = ⟨![0, (27 / 20), (3 / 5), (9 / 20), (3 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(1 / 240), (1077 / 800), (773 / 1280), (107 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_64, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_64, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_64, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_64 : keySolid (keys5Chunk2.get ⟨0, by decide⟩) = canonicalPose5_64.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_64 (box := canonicalBox5_64) (k := keys5Chunk2.get ⟨0, by decide⟩) (canonicalMatch5_64) (canonicalDecode5_64)

def canonicalPose5_65 : Pose 5 :=
  ⟨canonicalPerm5_15, ![true, true, true, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_65 : BoxKey 5 :=
  ⟨![5760, 38400, 6720, 7680, 8640], ![420, 0, 360, 300, 240], ![5690, 38320, 6648, 7605, 8560], false⟩

theorem canonicalMatch5_65 :
    canonicalPose5_65.boxKey 19200 (referenceBox5 (!canonicalBox5_65.bump)) = canonicalBox5_65 := by decide

theorem canonicalDecode5_65 : canonicalBox5_65.toKeyData 19200 = keys5Chunk2.get ⟨1, by decide⟩ := by
  change canonicalBox5_65.toKeyData 19200 = ⟨![(3 / 10), 2, (7 / 20), (2 / 5), (9 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(569 / 1920), (479 / 240), (277 / 800), (507 / 1280), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_65, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_65, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_65, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_65 : keySolid (keys5Chunk2.get ⟨1, by decide⟩) = canonicalPose5_65.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_65 (box := canonicalBox5_65) (k := keys5Chunk2.get ⟨1, by decide⟩) (canonicalMatch5_65) (canonicalDecode5_65)

def canonicalPose5_66 : Pose 5 :=
  ⟨canonicalPerm5_11, ![true, true, true, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_66 : BoxKey 5 :=
  ⟨![6720, 38400, 5760, 8640, 7680], ![360, 0, 420, 240, 300], ![6648, 38320, 5690, 8560, 7605], false⟩

theorem canonicalMatch5_66 :
    canonicalPose5_66.boxKey 19200 (referenceBox5 (!canonicalBox5_66.bump)) = canonicalBox5_66 := by decide

theorem canonicalDecode5_66 : canonicalBox5_66.toKeyData 19200 = keys5Chunk2.get ⟨2, by decide⟩ := by
  change canonicalBox5_66.toKeyData 19200 = ⟨![(7 / 20), 2, (3 / 10), (9 / 20), (2 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(277 / 800), (479 / 240), (569 / 1920), (107 / 240), (507 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_66, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_66, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_66, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_66 : keySolid (keys5Chunk2.get ⟨2, by decide⟩) = canonicalPose5_66.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_66 (box := canonicalBox5_66) (k := keys5Chunk2.get ⟨2, by decide⟩) (canonicalMatch5_66) (canonicalDecode5_66)

def canonicalPose5_67 : Pose 5 :=
  ⟨canonicalPerm5_7, ![true, false, true, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_67 : BoxKey 5 :=
  ⟨![7680, 38400, 8640, 6720, 5760], ![300, 0, 240, 360, 420], ![7605, 38480, 8560, 6648, 5690], true⟩

theorem canonicalMatch5_67 :
    canonicalPose5_67.boxKey 19200 (referenceBox5 (!canonicalBox5_67.bump)) = canonicalBox5_67 := by decide

theorem canonicalDecode5_67 : canonicalBox5_67.toKeyData 19200 = keys5Chunk2.get ⟨3, by decide⟩ := by
  change canonicalBox5_67.toKeyData 19200 = ⟨![(2 / 5), 2, (9 / 20), (7 / 20), (3 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(507 / 1280), (481 / 240), (107 / 240), (277 / 800), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_67, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_67, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_67, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_67 : keySolid (keys5Chunk2.get ⟨3, by decide⟩) = canonicalPose5_67.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_67 (box := canonicalBox5_67) (k := keys5Chunk2.get ⟨3, by decide⟩) (canonicalMatch5_67) (canonicalDecode5_67)

def canonicalPose5_68 : Pose 5 :=
  ⟨canonicalPerm5_3, ![true, false, true, true, true], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_68 : BoxKey 5 :=
  ⟨![8640, 38400, 7680, 5760, 6720], ![240, 0, 300, 420, 360], ![8560, 38480, 7605, 5690, 6648], true⟩

theorem canonicalMatch5_68 :
    canonicalPose5_68.boxKey 19200 (referenceBox5 (!canonicalBox5_68.bump)) = canonicalBox5_68 := by decide

theorem canonicalDecode5_68 : canonicalBox5_68.toKeyData 19200 = keys5Chunk2.get ⟨4, by decide⟩ := by
  change canonicalBox5_68.toKeyData 19200 = ⟨![(9 / 20), 2, (2 / 5), (3 / 10), (7 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(107 / 240), (481 / 240), (507 / 1280), (569 / 1920), (277 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_68, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_68, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_68, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_68 : keySolid (keys5Chunk2.get ⟨4, by decide⟩) = canonicalPose5_68.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_68 (box := canonicalBox5_68) (k := keys5Chunk2.get ⟨4, by decide⟩) (canonicalMatch5_68) (canonicalDecode5_68)

def canonicalPose5_69 : Pose 5 :=
  ⟨canonicalPerm5_5, ![false, true, false, true, true], ![0, 2, 0, 1, 1]⟩
def canonicalBox5_69 : BoxKey 5 :=
  ⟨![11520, 25920, 0, 5760, 8640], ![300, 360, 0, 420, 240], ![11595, 25848, 80, 5690, 8560], false⟩

theorem canonicalMatch5_69 :
    canonicalPose5_69.boxKey 19200 (referenceBox5 (!canonicalBox5_69.bump)) = canonicalBox5_69 := by decide

theorem canonicalDecode5_69 : canonicalBox5_69.toKeyData 19200 = keys5Chunk2.get ⟨5, by decide⟩ := by
  change canonicalBox5_69.toKeyData 19200 = ⟨![(3 / 5), (27 / 20), 0, (3 / 10), (9 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(773 / 1280), (1077 / 800), (1 / 240), (569 / 1920), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_69, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_69, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_69, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_69 : keySolid (keys5Chunk2.get ⟨5, by decide⟩) = canonicalPose5_69.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_69 (box := canonicalBox5_69) (k := keys5Chunk2.get ⟨5, by decide⟩) (canonicalMatch5_69) (canonicalDecode5_69)

def canonicalPose5_70 : Pose 5 :=
  ⟨canonicalPerm5_14, ![true, true, true, true, false], ![1, 2, 1, 0, 0]⟩
def canonicalBox5_70 : BoxKey 5 :=
  ⟨![5760, 25920, 8640, 0, 11520], ![420, 360, 240, 0, 300], ![5690, 25848, 8560, -80, 11595], true⟩

theorem canonicalMatch5_70 :
    canonicalPose5_70.boxKey 19200 (referenceBox5 (!canonicalBox5_70.bump)) = canonicalBox5_70 := by decide

theorem canonicalDecode5_70 : canonicalBox5_70.toKeyData 19200 = keys5Chunk2.get ⟨6, by decide⟩ := by
  change canonicalBox5_70.toKeyData 19200 = ⟨![(3 / 10), (27 / 20), (9 / 20), 0, (3 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(569 / 1920), (1077 / 800), (107 / 240), (-1 / 240), (773 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_70, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_70, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_70, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_70 : keySolid (keys5Chunk2.get ⟨6, by decide⟩) = canonicalPose5_70.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_70 (box := canonicalBox5_70) (k := keys5Chunk2.get ⟨6, by decide⟩) (canonicalMatch5_70) (canonicalDecode5_70)

def canonicalPose5_71 : Pose 5 :=
  ⟨canonicalPerm5_1, ![true, true, true, false, true], ![1, 2, 1, 0, 0]⟩
def canonicalBox5_71 : BoxKey 5 :=
  ⟨![8640, 25920, 5760, 11520, 0], ![240, 360, 420, 300, 0], ![8560, 25848, 5690, 11595, -80], true⟩

theorem canonicalMatch5_71 :
    canonicalPose5_71.boxKey 19200 (referenceBox5 (!canonicalBox5_71.bump)) = canonicalBox5_71 := by decide

theorem canonicalDecode5_71 : canonicalBox5_71.toKeyData 19200 = keys5Chunk2.get ⟨7, by decide⟩ := by
  change canonicalBox5_71.toKeyData 19200 = ⟨![(9 / 20), (27 / 20), (3 / 10), (3 / 5), 0], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(107 / 240), (1077 / 800), (569 / 1920), (773 / 1280), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_71, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_71, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_71, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_71 : keySolid (keys5Chunk2.get ⟨7, by decide⟩) = canonicalPose5_71.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_71 (box := canonicalBox5_71) (k := keys5Chunk2.get ⟨7, by decide⟩) (canonicalMatch5_71) (canonicalDecode5_71)

def canonicalPose5_72 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, false, true, true, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_72 : BoxKey 5 :=
  ⟨![0, 29760, 6720, 5760, 30720], ![0, 240, 360, 420, 300], ![80, 29840, 6648, 5690, 30795], false⟩

theorem canonicalMatch5_72 :
    canonicalPose5_72.boxKey 19200 (referenceBox5 (!canonicalBox5_72.bump)) = canonicalBox5_72 := by decide

theorem canonicalDecode5_72 : canonicalBox5_72.toKeyData 19200 = keys5Chunk2.get ⟨8, by decide⟩ := by
  change canonicalBox5_72.toKeyData 19200 = ⟨![0, (31 / 20), (7 / 20), (3 / 10), (8 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(1 / 240), (373 / 240), (277 / 800), (569 / 1920), (2053 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_72, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_72, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_72, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_72 : keySolid (keys5Chunk2.get ⟨8, by decide⟩) = canonicalPose5_72.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_72 (box := canonicalBox5_72) (k := keys5Chunk2.get ⟨8, by decide⟩) (canonicalMatch5_72) (canonicalDecode5_72)

def canonicalPose5_73 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, false, true, true, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_73 : BoxKey 5 :=
  ⟨![0, 30720, 5760, 6720, 29760], ![0, 300, 420, 360, 240], ![80, 30795, 5690, 6648, 29840], false⟩

theorem canonicalMatch5_73 :
    canonicalPose5_73.boxKey 19200 (referenceBox5 (!canonicalBox5_73.bump)) = canonicalBox5_73 := by decide

theorem canonicalDecode5_73 : canonicalBox5_73.toKeyData 19200 = keys5Chunk2.get ⟨9, by decide⟩ := by
  change canonicalBox5_73.toKeyData 19200 = ⟨![0, (8 / 5), (3 / 10), (7 / 20), (31 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(1 / 240), (2053 / 1280), (569 / 1920), (277 / 800), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_73, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_73, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_73, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_73 : keySolid (keys5Chunk2.get ⟨9, by decide⟩) = canonicalPose5_73.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_73 (box := canonicalBox5_73) (k := keys5Chunk2.get ⟨9, by decide⟩) (canonicalMatch5_73) (canonicalDecode5_73)

def canonicalPose5_74 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, false, true, true, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_74 : BoxKey 5 :=
  ⟨![0, 31680, 7680, 8640, 32640], ![0, 360, 300, 240, 420], ![-80, 31752, 7605, 8560, 32710], true⟩

theorem canonicalMatch5_74 :
    canonicalPose5_74.boxKey 19200 (referenceBox5 (!canonicalBox5_74.bump)) = canonicalBox5_74 := by decide

theorem canonicalDecode5_74 : canonicalBox5_74.toKeyData 19200 = keys5Chunk2.get ⟨10, by decide⟩ := by
  change canonicalBox5_74.toKeyData 19200 = ⟨![0, (33 / 20), (2 / 5), (9 / 20), (17 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(-1 / 240), (1323 / 800), (507 / 1280), (107 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_74, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_74, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_74, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_74 : keySolid (keys5Chunk2.get ⟨10, by decide⟩) = canonicalPose5_74.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_74 (box := canonicalBox5_74) (k := keys5Chunk2.get ⟨10, by decide⟩) (canonicalMatch5_74) (canonicalDecode5_74)

def canonicalPose5_75 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, false, true, true, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_75 : BoxKey 5 :=
  ⟨![0, 32640, 8640, 7680, 31680], ![0, 420, 240, 300, 360], ![-80, 32710, 8560, 7605, 31752], true⟩

theorem canonicalMatch5_75 :
    canonicalPose5_75.boxKey 19200 (referenceBox5 (!canonicalBox5_75.bump)) = canonicalBox5_75 := by decide

theorem canonicalDecode5_75 : canonicalBox5_75.toKeyData 19200 = keys5Chunk2.get ⟨11, by decide⟩ := by
  change canonicalBox5_75.toKeyData 19200 = ⟨![0, (17 / 10), (9 / 20), (2 / 5), (33 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(-1 / 240), (3271 / 1920), (107 / 240), (507 / 1280), (1323 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_75, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_75, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_75, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_75 : keySolid (keys5Chunk2.get ⟨11, by decide⟩) = canonicalPose5_75.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_75 (box := canonicalBox5_75) (k := keys5Chunk2.get ⟨11, by decide⟩) (canonicalMatch5_75) (canonicalDecode5_75)

def canonicalPose5_76 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, false, true, true, true], ![0, 2, 1, 1, 2]⟩
def canonicalBox5_76 : BoxKey 5 :=
  ⟨![12480, 38400, 5760, 8640, 26880], ![360, 0, 420, 240, 300], ![12552, 38480, 5690, 8560, 26805], true⟩

theorem canonicalMatch5_76 :
    canonicalPose5_76.boxKey 19200 (referenceBox5 (!canonicalBox5_76.bump)) = canonicalBox5_76 := by decide

theorem canonicalDecode5_76 : canonicalBox5_76.toKeyData 19200 = keys5Chunk2.get ⟨12, by decide⟩ := by
  change canonicalBox5_76.toKeyData 19200 = ⟨![(13 / 20), 2, (3 / 10), (9 / 20), (7 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(523 / 800), (481 / 240), (569 / 1920), (107 / 240), (1787 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_76, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_76, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_76, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_76 : keySolid (keys5Chunk2.get ⟨12, by decide⟩) = canonicalPose5_76.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_76 (box := canonicalBox5_76) (k := keys5Chunk2.get ⟨12, by decide⟩) (canonicalMatch5_76) (canonicalDecode5_76)

def canonicalPose5_77 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, false, false, false, false], ![0, 1, 0, 0, 1]⟩
def canonicalBox5_77 : BoxKey 5 :=
  ⟨![12480, 29760, 0, 11520, 32640], ![360, 240, 0, 300, 420], ![12552, 29840, 80, 11595, 32710], false⟩

theorem canonicalMatch5_77 :
    canonicalPose5_77.boxKey 19200 (referenceBox5 (!canonicalBox5_77.bump)) = canonicalBox5_77 := by decide

theorem canonicalDecode5_77 : canonicalBox5_77.toKeyData 19200 = keys5Chunk2.get ⟨13, by decide⟩ := by
  change canonicalBox5_77.toKeyData 19200 = ⟨![(13 / 20), (31 / 20), 0, (3 / 5), (17 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(523 / 800), (373 / 240), (1 / 240), (773 / 1280), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_77, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_77, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_77, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_77 : keySolid (keys5Chunk2.get ⟨13, by decide⟩) = canonicalPose5_77.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_77 (box := canonicalBox5_77) (k := keys5Chunk2.get ⟨13, by decide⟩) (canonicalMatch5_77) (canonicalDecode5_77)

def canonicalPose5_78 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, false, false, false, false], ![0, 1, 0, 0, 1]⟩
def canonicalBox5_78 : BoxKey 5 :=
  ⟨![12480, 32640, 11520, 0, 29760], ![360, 420, 300, 0, 240], ![12552, 32710, 11595, 80, 29840], false⟩

theorem canonicalMatch5_78 :
    canonicalPose5_78.boxKey 19200 (referenceBox5 (!canonicalBox5_78.bump)) = canonicalBox5_78 := by decide

theorem canonicalDecode5_78 : canonicalBox5_78.toKeyData 19200 = keys5Chunk2.get ⟨14, by decide⟩ := by
  change canonicalBox5_78.toKeyData 19200 = ⟨![(13 / 20), (17 / 10), (3 / 5), 0, (31 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(523 / 800), (3271 / 1920), (773 / 1280), (1 / 240), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_78, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_78, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_78, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_78 : keySolid (keys5Chunk2.get ⟨14, by decide⟩) = canonicalPose5_78.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_78 (box := canonicalBox5_78) (k := keys5Chunk2.get ⟨14, by decide⟩) (canonicalMatch5_78) (canonicalDecode5_78)

def canonicalPose5_79 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, true, true, true, false], ![0, 2, 1, 1, 2]⟩
def canonicalBox5_79 : BoxKey 5 :=
  ⟨![12480, 26880, 8640, 5760, 38400], ![360, 300, 240, 420, 0], ![12552, 26805, 8560, 5690, 38480], true⟩

theorem canonicalMatch5_79 :
    canonicalPose5_79.boxKey 19200 (referenceBox5 (!canonicalBox5_79.bump)) = canonicalBox5_79 := by decide

theorem canonicalDecode5_79 : canonicalBox5_79.toKeyData 19200 = keys5Chunk2.get ⟨15, by decide⟩ := by
  change canonicalBox5_79.toKeyData 19200 = ⟨![(13 / 20), (7 / 5), (9 / 20), (3 / 10), 2], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(523 / 800), (1787 / 1280), (107 / 240), (569 / 1920), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_79, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_79, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_79, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_79 : keySolid (keys5Chunk2.get ⟨15, by decide⟩) = canonicalPose5_79.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_79 (box := canonicalBox5_79) (k := keys5Chunk2.get ⟨15, by decide⟩) (canonicalMatch5_79) (canonicalDecode5_79)

def canonicalPose5_80 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, false, false, false, false], ![0, 1, 0, 1, 0]⟩
def canonicalBox5_80 : BoxKey 5 :=
  ⟨![0, 29760, 12480, 32640, 11520], ![0, 240, 360, 420, 300], ![80, 29840, 12552, 32710, 11595], false⟩

theorem canonicalMatch5_80 :
    canonicalPose5_80.boxKey 19200 (referenceBox5 (!canonicalBox5_80.bump)) = canonicalBox5_80 := by decide

theorem canonicalDecode5_80 : canonicalBox5_80.toKeyData 19200 = keys5Chunk2.get ⟨16, by decide⟩ := by
  change canonicalBox5_80.toKeyData 19200 = ⟨![0, (31 / 20), (13 / 20), (17 / 10), (3 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(1 / 240), (373 / 240), (523 / 800), (3271 / 1920), (773 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_80, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_80, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_80, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_80 : keySolid (keys5Chunk2.get ⟨16, by decide⟩) = canonicalPose5_80.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_80 (box := canonicalBox5_80) (k := keys5Chunk2.get ⟨16, by decide⟩) (canonicalMatch5_80) (canonicalDecode5_80)

def canonicalPose5_81 : Pose 5 :=
  ⟨canonicalPerm5_15, ![true, false, false, true, true], ![1, 2, 0, 2, 1]⟩
def canonicalBox5_81 : BoxKey 5 :=
  ⟨![5760, 38400, 12480, 26880, 8640], ![420, 0, 360, 300, 240], ![5690, 38480, 12552, 26805, 8560], true⟩

theorem canonicalMatch5_81 :
    canonicalPose5_81.boxKey 19200 (referenceBox5 (!canonicalBox5_81.bump)) = canonicalBox5_81 := by decide

theorem canonicalDecode5_81 : canonicalBox5_81.toKeyData 19200 = keys5Chunk2.get ⟨17, by decide⟩ := by
  change canonicalBox5_81.toKeyData 19200 = ⟨![(3 / 10), 2, (13 / 20), (7 / 5), (9 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(569 / 1920), (481 / 240), (523 / 800), (1787 / 1280), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_81, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_81, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_81, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_81 : keySolid (keys5Chunk2.get ⟨17, by decide⟩) = canonicalPose5_81.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_81 (box := canonicalBox5_81) (k := keys5Chunk2.get ⟨17, by decide⟩) (canonicalMatch5_81) (canonicalDecode5_81)

def canonicalPose5_82 : Pose 5 :=
  ⟨canonicalPerm5_13, ![true, false, false, false, true], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_82 : BoxKey 5 :=
  ⟨![5760, 30720, 0, 29760, 6720], ![420, 300, 0, 240, 360], ![5690, 30795, 80, 29840, 6648], false⟩

theorem canonicalMatch5_82 :
    canonicalPose5_82.boxKey 19200 (referenceBox5 (!canonicalBox5_82.bump)) = canonicalBox5_82 := by decide

theorem canonicalDecode5_82 : canonicalBox5_82.toKeyData 19200 = keys5Chunk2.get ⟨18, by decide⟩ := by
  change canonicalBox5_82.toKeyData 19200 = ⟨![(3 / 10), (8 / 5), 0, (31 / 20), (7 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(569 / 1920), (2053 / 1280), (1 / 240), (373 / 240), (277 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_82, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_82, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_82, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_82 : keySolid (keys5Chunk2.get ⟨18, by decide⟩) = canonicalPose5_82.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_82 (box := canonicalBox5_82) (k := keys5Chunk2.get ⟨18, by decide⟩) (canonicalMatch5_82) (canonicalDecode5_82)

def canonicalPose5_83 : Pose 5 :=
  ⟨canonicalPerm5_8, ![true, false, false, false, true], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_83 : BoxKey 5 :=
  ⟨![6720, 29760, 0, 30720, 5760], ![360, 240, 0, 300, 420], ![6648, 29840, 80, 30795, 5690], false⟩

theorem canonicalMatch5_83 :
    canonicalPose5_83.boxKey 19200 (referenceBox5 (!canonicalBox5_83.bump)) = canonicalBox5_83 := by decide

theorem canonicalDecode5_83 : canonicalBox5_83.toKeyData 19200 = keys5Chunk2.get ⟨19, by decide⟩ := by
  change canonicalBox5_83.toKeyData 19200 = ⟨![(7 / 20), (31 / 20), 0, (8 / 5), (3 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(277 / 800), (373 / 240), (1 / 240), (2053 / 1280), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_83, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_83, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_83, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_83 : keySolid (keys5Chunk2.get ⟨19, by decide⟩) = canonicalPose5_83.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_83 (box := canonicalBox5_83) (k := keys5Chunk2.get ⟨19, by decide⟩) (canonicalMatch5_83) (canonicalDecode5_83)

def canonicalPose5_84 : Pose 5 :=
  ⟨canonicalPerm5_5, ![true, false, true, false, true], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_84 : BoxKey 5 :=
  ⟨![7680, 31680, 0, 32640, 8640], ![300, 360, 0, 420, 240], ![7605, 31752, -80, 32710, 8560], true⟩

theorem canonicalMatch5_84 :
    canonicalPose5_84.boxKey 19200 (referenceBox5 (!canonicalBox5_84.bump)) = canonicalBox5_84 := by decide

theorem canonicalDecode5_84 : canonicalBox5_84.toKeyData 19200 = keys5Chunk2.get ⟨20, by decide⟩ := by
  change canonicalBox5_84.toKeyData 19200 = ⟨![(2 / 5), (33 / 20), 0, (17 / 10), (9 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(507 / 1280), (1323 / 800), (-1 / 240), (3271 / 1920), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_84, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_84, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_84, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_84 : keySolid (keys5Chunk2.get ⟨20, by decide⟩) = canonicalPose5_84.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_84 (box := canonicalBox5_84) (k := keys5Chunk2.get ⟨20, by decide⟩) (canonicalMatch5_84) (canonicalDecode5_84)

def canonicalPose5_85 : Pose 5 :=
  ⟨canonicalPerm5_2, ![true, false, true, false, true], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_85 : BoxKey 5 :=
  ⟨![8640, 32640, 0, 31680, 7680], ![240, 420, 0, 360, 300], ![8560, 32710, -80, 31752, 7605], true⟩

theorem canonicalMatch5_85 :
    canonicalPose5_85.boxKey 19200 (referenceBox5 (!canonicalBox5_85.bump)) = canonicalBox5_85 := by decide

theorem canonicalDecode5_85 : canonicalBox5_85.toKeyData 19200 = keys5Chunk2.get ⟨21, by decide⟩ := by
  change canonicalBox5_85.toKeyData 19200 = ⟨![(9 / 20), (17 / 10), 0, (33 / 20), (2 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(107 / 240), (3271 / 1920), (-1 / 240), (1323 / 800), (507 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_85, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_85, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_85, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_85 : keySolid (keys5Chunk2.get ⟨21, by decide⟩) = canonicalPose5_85.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_85 (box := canonicalBox5_85) (k := keys5Chunk2.get ⟨21, by decide⟩) (canonicalMatch5_85) (canonicalDecode5_85)

def canonicalPose5_86 : Pose 5 :=
  ⟨canonicalPerm5_0, ![true, true, false, false, true], ![1, 2, 0, 2, 1]⟩
def canonicalBox5_86 : BoxKey 5 :=
  ⟨![8640, 26880, 12480, 38400, 5760], ![240, 300, 360, 0, 420], ![8560, 26805, 12552, 38480, 5690], true⟩

theorem canonicalMatch5_86 :
    canonicalPose5_86.boxKey 19200 (referenceBox5 (!canonicalBox5_86.bump)) = canonicalBox5_86 := by decide

theorem canonicalDecode5_86 : canonicalBox5_86.toKeyData 19200 = keys5Chunk2.get ⟨22, by decide⟩ := by
  change canonicalBox5_86.toKeyData 19200 = ⟨![(9 / 20), (7 / 5), (13 / 20), 2, (3 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(107 / 240), (1787 / 1280), (523 / 800), (481 / 240), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_86, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_86, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_86, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_86 : keySolid (keys5Chunk2.get ⟨22, by decide⟩) = canonicalPose5_86.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_86 (box := canonicalBox5_86) (k := keys5Chunk2.get ⟨22, by decide⟩) (canonicalMatch5_86) (canonicalDecode5_86)

def canonicalPose5_87 : Pose 5 :=
  ⟨canonicalPerm5_6, ![false, false, false, false, false], ![0, 1, 0, 1, 0]⟩
def canonicalBox5_87 : BoxKey 5 :=
  ⟨![11520, 32640, 12480, 29760, 0], ![300, 420, 360, 240, 0], ![11595, 32710, 12552, 29840, 80], false⟩

theorem canonicalMatch5_87 :
    canonicalPose5_87.boxKey 19200 (referenceBox5 (!canonicalBox5_87.bump)) = canonicalBox5_87 := by decide

theorem canonicalDecode5_87 : canonicalBox5_87.toKeyData 19200 = keys5Chunk2.get ⟨23, by decide⟩ := by
  change canonicalBox5_87.toKeyData 19200 = ⟨![(3 / 5), (17 / 10), (13 / 20), (31 / 20), 0], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(773 / 1280), (3271 / 1920), (523 / 800), (373 / 240), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_87, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_87, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_87, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_87 : keySolid (keys5Chunk2.get ⟨23, by decide⟩) = canonicalPose5_87.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_87 (box := canonicalBox5_87) (k := keys5Chunk2.get ⟨23, by decide⟩) (canonicalMatch5_87) (canonicalDecode5_87)

def canonicalPose5_88 : Pose 5 :=
  ⟨canonicalPerm5_18, ![false, true, false, false, false], ![0, 2, 0, 1, 1]⟩
def canonicalBox5_88 : BoxKey 5 :=
  ⟨![0, 25920, 11520, 29760, 32640], ![0, 360, 300, 240, 420], ![80, 25848, 11595, 29840, 32710], false⟩

theorem canonicalMatch5_88 :
    canonicalPose5_88.boxKey 19200 (referenceBox5 (!canonicalBox5_88.bump)) = canonicalBox5_88 := by decide

theorem canonicalDecode5_88 : canonicalBox5_88.toKeyData 19200 = keys5Chunk2.get ⟨24, by decide⟩ := by
  change canonicalBox5_88.toKeyData 19200 = ⟨![0, (27 / 20), (3 / 5), (31 / 20), (17 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(1 / 240), (1077 / 800), (773 / 1280), (373 / 240), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_88, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_88, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_88, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_88 : keySolid (keys5Chunk2.get ⟨24, by decide⟩) = canonicalPose5_88.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_88 (box := canonicalBox5_88) (k := keys5Chunk2.get ⟨24, by decide⟩) (canonicalMatch5_88) (canonicalDecode5_88)

def canonicalPose5_89 : Pose 5 :=
  ⟨canonicalPerm5_15, ![true, true, true, false, false], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_89 : BoxKey 5 :=
  ⟨![5760, 38400, 6720, 30720, 29760], ![420, 0, 360, 300, 240], ![5690, 38320, 6648, 30795, 29840], false⟩

theorem canonicalMatch5_89 :
    canonicalPose5_89.boxKey 19200 (referenceBox5 (!canonicalBox5_89.bump)) = canonicalBox5_89 := by decide

theorem canonicalDecode5_89 : canonicalBox5_89.toKeyData 19200 = keys5Chunk2.get ⟨25, by decide⟩ := by
  change canonicalBox5_89.toKeyData 19200 = ⟨![(3 / 10), 2, (7 / 20), (8 / 5), (31 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(569 / 1920), (479 / 240), (277 / 800), (2053 / 1280), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_89, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_89, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_89, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_89 : keySolid (keys5Chunk2.get ⟨25, by decide⟩) = canonicalPose5_89.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_89 (box := canonicalBox5_89) (k := keys5Chunk2.get ⟨25, by decide⟩) (canonicalMatch5_89) (canonicalDecode5_89)

def canonicalPose5_90 : Pose 5 :=
  ⟨canonicalPerm5_11, ![true, true, true, false, false], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_90 : BoxKey 5 :=
  ⟨![6720, 38400, 5760, 29760, 30720], ![360, 0, 420, 240, 300], ![6648, 38320, 5690, 29840, 30795], false⟩

theorem canonicalMatch5_90 :
    canonicalPose5_90.boxKey 19200 (referenceBox5 (!canonicalBox5_90.bump)) = canonicalBox5_90 := by decide

theorem canonicalDecode5_90 : canonicalBox5_90.toKeyData 19200 = keys5Chunk2.get ⟨26, by decide⟩ := by
  change canonicalBox5_90.toKeyData 19200 = ⟨![(7 / 20), 2, (3 / 10), (31 / 20), (8 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(277 / 800), (479 / 240), (569 / 1920), (373 / 240), (2053 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_90, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_90, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_90, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_90 : keySolid (keys5Chunk2.get ⟨26, by decide⟩) = canonicalPose5_90.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_90 (box := canonicalBox5_90) (k := keys5Chunk2.get ⟨26, by decide⟩) (canonicalMatch5_90) (canonicalDecode5_90)

def canonicalPose5_91 : Pose 5 :=
  ⟨canonicalPerm5_7, ![true, false, true, false, false], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_91 : BoxKey 5 :=
  ⟨![7680, 38400, 8640, 31680, 32640], ![300, 0, 240, 360, 420], ![7605, 38480, 8560, 31752, 32710], true⟩

theorem canonicalMatch5_91 :
    canonicalPose5_91.boxKey 19200 (referenceBox5 (!canonicalBox5_91.bump)) = canonicalBox5_91 := by decide

theorem canonicalDecode5_91 : canonicalBox5_91.toKeyData 19200 = keys5Chunk2.get ⟨27, by decide⟩ := by
  change canonicalBox5_91.toKeyData 19200 = ⟨![(2 / 5), 2, (9 / 20), (33 / 20), (17 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(507 / 1280), (481 / 240), (107 / 240), (1323 / 800), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_91, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_91, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_91, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_91 : keySolid (keys5Chunk2.get ⟨27, by decide⟩) = canonicalPose5_91.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_91 (box := canonicalBox5_91) (k := keys5Chunk2.get ⟨27, by decide⟩) (canonicalMatch5_91) (canonicalDecode5_91)

def canonicalPose5_92 : Pose 5 :=
  ⟨canonicalPerm5_3, ![true, false, true, false, false], ![1, 2, 1, 1, 1]⟩
def canonicalBox5_92 : BoxKey 5 :=
  ⟨![8640, 38400, 7680, 32640, 31680], ![240, 0, 300, 420, 360], ![8560, 38480, 7605, 32710, 31752], true⟩

theorem canonicalMatch5_92 :
    canonicalPose5_92.boxKey 19200 (referenceBox5 (!canonicalBox5_92.bump)) = canonicalBox5_92 := by decide

theorem canonicalDecode5_92 : canonicalBox5_92.toKeyData 19200 = keys5Chunk2.get ⟨28, by decide⟩ := by
  change canonicalBox5_92.toKeyData 19200 = ⟨![(9 / 20), 2, (2 / 5), (17 / 10), (33 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(107 / 240), (481 / 240), (507 / 1280), (3271 / 1920), (1323 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_92, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_92, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_92, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_92 : keySolid (keys5Chunk2.get ⟨28, by decide⟩) = canonicalPose5_92.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_92 (box := canonicalBox5_92) (k := keys5Chunk2.get ⟨28, by decide⟩) (canonicalMatch5_92) (canonicalDecode5_92)

def canonicalPose5_93 : Pose 5 :=
  ⟨canonicalPerm5_5, ![false, true, false, false, false], ![0, 2, 0, 1, 1]⟩
def canonicalBox5_93 : BoxKey 5 :=
  ⟨![11520, 25920, 0, 32640, 29760], ![300, 360, 0, 420, 240], ![11595, 25848, 80, 32710, 29840], false⟩

theorem canonicalMatch5_93 :
    canonicalPose5_93.boxKey 19200 (referenceBox5 (!canonicalBox5_93.bump)) = canonicalBox5_93 := by decide

theorem canonicalDecode5_93 : canonicalBox5_93.toKeyData 19200 = keys5Chunk2.get ⟨29, by decide⟩ := by
  change canonicalBox5_93.toKeyData 19200 = ⟨![(3 / 5), (27 / 20), 0, (17 / 10), (31 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(773 / 1280), (1077 / 800), (1 / 240), (3271 / 1920), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_93, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_93, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_93, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_93 : keySolid (keys5Chunk2.get ⟨29, by decide⟩) = canonicalPose5_93.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_93 (box := canonicalBox5_93) (k := keys5Chunk2.get ⟨29, by decide⟩) (canonicalMatch5_93) (canonicalDecode5_93)

def canonicalPose5_94 : Pose 5 :=
  ⟨canonicalPerm5_14, ![true, true, true, false, true], ![1, 2, 1, 2, 2]⟩
def canonicalBox5_94 : BoxKey 5 :=
  ⟨![5760, 25920, 8640, 38400, 26880], ![420, 360, 240, 0, 300], ![5690, 25848, 8560, 38480, 26805], true⟩

theorem canonicalMatch5_94 :
    canonicalPose5_94.boxKey 19200 (referenceBox5 (!canonicalBox5_94.bump)) = canonicalBox5_94 := by decide

theorem canonicalDecode5_94 : canonicalBox5_94.toKeyData 19200 = keys5Chunk2.get ⟨30, by decide⟩ := by
  change canonicalBox5_94.toKeyData 19200 = ⟨![(3 / 10), (27 / 20), (9 / 20), 2, (7 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(569 / 1920), (1077 / 800), (107 / 240), (481 / 240), (1787 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_94, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_94, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_94, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_94 : keySolid (keys5Chunk2.get ⟨30, by decide⟩) = canonicalPose5_94.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_94 (box := canonicalBox5_94) (k := keys5Chunk2.get ⟨30, by decide⟩) (canonicalMatch5_94) (canonicalDecode5_94)

def canonicalPose5_95 : Pose 5 :=
  ⟨canonicalPerm5_1, ![true, true, true, true, false], ![1, 2, 1, 2, 2]⟩
def canonicalBox5_95 : BoxKey 5 :=
  ⟨![8640, 25920, 5760, 26880, 38400], ![240, 360, 420, 300, 0], ![8560, 25848, 5690, 26805, 38480], true⟩

theorem canonicalMatch5_95 :
    canonicalPose5_95.boxKey 19200 (referenceBox5 (!canonicalBox5_95.bump)) = canonicalBox5_95 := by decide

theorem canonicalDecode5_95 : canonicalBox5_95.toKeyData 19200 = keys5Chunk2.get ⟨31, by decide⟩ := by
  change canonicalBox5_95.toKeyData 19200 = ⟨![(9 / 20), (27 / 20), (3 / 10), (7 / 5), 2], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(107 / 240), (1077 / 800), (569 / 1920), (1787 / 1280), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_95, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_95, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_95, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_95 : keySolid (keys5Chunk2.get ⟨31, by decide⟩) = canonicalPose5_95.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_95 (box := canonicalBox5_95) (k := keys5Chunk2.get ⟨31, by decide⟩) (canonicalMatch5_95) (canonicalDecode5_95)

theorem keys5Chunk2_canonical : ∀ k ∈ keys5Chunk2,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk2, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_64, canonicalSolid5_64⟩
  · exact ⟨canonicalPose5_65, canonicalSolid5_65⟩
  · exact ⟨canonicalPose5_66, canonicalSolid5_66⟩
  · exact ⟨canonicalPose5_67, canonicalSolid5_67⟩
  · exact ⟨canonicalPose5_68, canonicalSolid5_68⟩
  · exact ⟨canonicalPose5_69, canonicalSolid5_69⟩
  · exact ⟨canonicalPose5_70, canonicalSolid5_70⟩
  · exact ⟨canonicalPose5_71, canonicalSolid5_71⟩
  · exact ⟨canonicalPose5_72, canonicalSolid5_72⟩
  · exact ⟨canonicalPose5_73, canonicalSolid5_73⟩
  · exact ⟨canonicalPose5_74, canonicalSolid5_74⟩
  · exact ⟨canonicalPose5_75, canonicalSolid5_75⟩
  · exact ⟨canonicalPose5_76, canonicalSolid5_76⟩
  · exact ⟨canonicalPose5_77, canonicalSolid5_77⟩
  · exact ⟨canonicalPose5_78, canonicalSolid5_78⟩
  · exact ⟨canonicalPose5_79, canonicalSolid5_79⟩
  · exact ⟨canonicalPose5_80, canonicalSolid5_80⟩
  · exact ⟨canonicalPose5_81, canonicalSolid5_81⟩
  · exact ⟨canonicalPose5_82, canonicalSolid5_82⟩
  · exact ⟨canonicalPose5_83, canonicalSolid5_83⟩
  · exact ⟨canonicalPose5_84, canonicalSolid5_84⟩
  · exact ⟨canonicalPose5_85, canonicalSolid5_85⟩
  · exact ⟨canonicalPose5_86, canonicalSolid5_86⟩
  · exact ⟨canonicalPose5_87, canonicalSolid5_87⟩
  · exact ⟨canonicalPose5_88, canonicalSolid5_88⟩
  · exact ⟨canonicalPose5_89, canonicalSolid5_89⟩
  · exact ⟨canonicalPose5_90, canonicalSolid5_90⟩
  · exact ⟨canonicalPose5_91, canonicalSolid5_91⟩
  · exact ⟨canonicalPose5_92, canonicalSolid5_92⟩
  · exact ⟨canonicalPose5_93, canonicalSolid5_93⟩
  · exact ⟨canonicalPose5_94, canonicalSolid5_94⟩
  · exact ⟨canonicalPose5_95, canonicalSolid5_95⟩

#print axioms keys5Chunk2_canonical

end SparseMonotiles.Canonical
