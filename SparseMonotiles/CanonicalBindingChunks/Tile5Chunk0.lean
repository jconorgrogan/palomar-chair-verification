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

def canonicalPose5_0 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, true, true, true, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_0 : BoxKey 5 :=
  ⟨![0, 5760, 8640, 7680, 6720], ![0, 420, 240, 300, 360], ![-80, 5690, 8560, 7605, 6648], true⟩

theorem canonicalMatch5_0 :
    canonicalPose5_0.boxKey 19200 (referenceBox5 (!canonicalBox5_0.bump)) = canonicalBox5_0 := by decide

theorem canonicalDecode5_0 : canonicalBox5_0.toKeyData 19200 = keys5Chunk0.get ⟨0, by decide⟩ := by
  change canonicalBox5_0.toKeyData 19200 = ⟨![0, (3 / 10), (9 / 20), (2 / 5), (7 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(-1 / 240), (569 / 1920), (107 / 240), (507 / 1280), (277 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_0, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_0, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_0, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_0 : keySolid (keys5Chunk0.get ⟨0, by decide⟩) = canonicalPose5_0.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_0 (box := canonicalBox5_0) (k := keys5Chunk0.get ⟨0, by decide⟩) (canonicalMatch5_0) (canonicalDecode5_0)

def canonicalPose5_1 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, true, true, true, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_1 : BoxKey 5 :=
  ⟨![0, 6720, 7680, 8640, 5760], ![0, 360, 300, 240, 420], ![-80, 6648, 7605, 8560, 5690], true⟩

theorem canonicalMatch5_1 :
    canonicalPose5_1.boxKey 19200 (referenceBox5 (!canonicalBox5_1.bump)) = canonicalBox5_1 := by decide

theorem canonicalDecode5_1 : canonicalBox5_1.toKeyData 19200 = keys5Chunk0.get ⟨1, by decide⟩ := by
  change canonicalBox5_1.toKeyData 19200 = ⟨![0, (7 / 20), (2 / 5), (9 / 20), (3 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(-1 / 240), (277 / 800), (507 / 1280), (107 / 240), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_1, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_1, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_1, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_1 : keySolid (keys5Chunk0.get ⟨1, by decide⟩) = canonicalPose5_1.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_1 (box := canonicalBox5_1) (k := keys5Chunk0.get ⟨1, by decide⟩) (canonicalMatch5_1) (canonicalDecode5_1)

def canonicalPose5_2 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, true, true, true, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_2 : BoxKey 5 :=
  ⟨![0, 7680, 5760, 6720, 8640], ![0, 300, 420, 360, 240], ![80, 7605, 5690, 6648, 8560], false⟩

theorem canonicalMatch5_2 :
    canonicalPose5_2.boxKey 19200 (referenceBox5 (!canonicalBox5_2.bump)) = canonicalBox5_2 := by decide

theorem canonicalDecode5_2 : canonicalBox5_2.toKeyData 19200 = keys5Chunk0.get ⟨2, by decide⟩ := by
  change canonicalBox5_2.toKeyData 19200 = ⟨![0, (2 / 5), (3 / 10), (7 / 20), (9 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(1 / 240), (507 / 1280), (569 / 1920), (277 / 800), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_2, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_2, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_2, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_2 : keySolid (keys5Chunk0.get ⟨2, by decide⟩) = canonicalPose5_2.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_2 (box := canonicalBox5_2) (k := keys5Chunk0.get ⟨2, by decide⟩) (canonicalMatch5_2) (canonicalDecode5_2)

def canonicalPose5_3 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, true, true, true, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_3 : BoxKey 5 :=
  ⟨![0, 8640, 6720, 5760, 7680], ![0, 240, 360, 420, 300], ![80, 8560, 6648, 5690, 7605], false⟩

theorem canonicalMatch5_3 :
    canonicalPose5_3.boxKey 19200 (referenceBox5 (!canonicalBox5_3.bump)) = canonicalBox5_3 := by decide

theorem canonicalDecode5_3 : canonicalBox5_3.toKeyData 19200 = keys5Chunk0.get ⟨3, by decide⟩ := by
  change canonicalBox5_3.toKeyData 19200 = ⟨![0, (9 / 20), (7 / 20), (3 / 10), (2 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(1 / 240), (107 / 240), (277 / 800), (569 / 1920), (507 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_3, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_3, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_3, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_3 : keySolid (keys5Chunk0.get ⟨3, by decide⟩) = canonicalPose5_3.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_3 (box := canonicalBox5_3) (k := keys5Chunk0.get ⟨3, by decide⟩) (canonicalMatch5_3) (canonicalDecode5_3)

def canonicalPose5_4 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, true, true, true, false], ![0, 0, 1, 1, 0]⟩
def canonicalBox5_4 : BoxKey 5 :=
  ⟨![12480, 0, 5760, 8640, 11520], ![360, 0, 420, 240, 300], ![12552, -80, 5690, 8560, 11595], true⟩

theorem canonicalMatch5_4 :
    canonicalPose5_4.boxKey 19200 (referenceBox5 (!canonicalBox5_4.bump)) = canonicalBox5_4 := by decide

theorem canonicalDecode5_4 : canonicalBox5_4.toKeyData 19200 = keys5Chunk0.get ⟨4, by decide⟩ := by
  change canonicalBox5_4.toKeyData 19200 = ⟨![(13 / 20), 0, (3 / 10), (9 / 20), (3 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(523 / 800), (-1 / 240), (569 / 1920), (107 / 240), (773 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_4, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_4, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_4, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_4 : keySolid (keys5Chunk0.get ⟨4, by decide⟩) = canonicalPose5_4.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_4 (box := canonicalBox5_4) (k := keys5Chunk0.get ⟨4, by decide⟩) (canonicalMatch5_4) (canonicalDecode5_4)

def canonicalPose5_5 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, true, false, false, true], ![0, 1, 0, 0, 1]⟩
def canonicalBox5_5 : BoxKey 5 :=
  ⟨![12480, 8640, 0, 11520, 5760], ![360, 240, 0, 300, 420], ![12552, 8560, 80, 11595, 5690], false⟩

theorem canonicalMatch5_5 :
    canonicalPose5_5.boxKey 19200 (referenceBox5 (!canonicalBox5_5.bump)) = canonicalBox5_5 := by decide

theorem canonicalDecode5_5 : canonicalBox5_5.toKeyData 19200 = keys5Chunk0.get ⟨5, by decide⟩ := by
  change canonicalBox5_5.toKeyData 19200 = ⟨![(13 / 20), (9 / 20), 0, (3 / 5), (3 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(523 / 800), (107 / 240), (1 / 240), (773 / 1280), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_5, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_5, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_5, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_5 : keySolid (keys5Chunk0.get ⟨5, by decide⟩) = canonicalPose5_5.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_5 (box := canonicalBox5_5) (k := keys5Chunk0.get ⟨5, by decide⟩) (canonicalMatch5_5) (canonicalDecode5_5)

def canonicalPose5_6 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, true, false, false, true], ![0, 1, 0, 0, 1]⟩
def canonicalBox5_6 : BoxKey 5 :=
  ⟨![12480, 5760, 11520, 0, 8640], ![360, 420, 300, 0, 240], ![12552, 5690, 11595, 80, 8560], false⟩

theorem canonicalMatch5_6 :
    canonicalPose5_6.boxKey 19200 (referenceBox5 (!canonicalBox5_6.bump)) = canonicalBox5_6 := by decide

theorem canonicalDecode5_6 : canonicalBox5_6.toKeyData 19200 = keys5Chunk0.get ⟨6, by decide⟩ := by
  change canonicalBox5_6.toKeyData 19200 = ⟨![(13 / 20), (3 / 10), (3 / 5), 0, (9 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(523 / 800), (569 / 1920), (773 / 1280), (1 / 240), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_6, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_6, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_6, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_6 : keySolid (keys5Chunk0.get ⟨6, by decide⟩) = canonicalPose5_6.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_6 (box := canonicalBox5_6) (k := keys5Chunk0.get ⟨6, by decide⟩) (canonicalMatch5_6) (canonicalDecode5_6)

def canonicalPose5_7 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, false, true, true, true], ![0, 0, 1, 1, 0]⟩
def canonicalBox5_7 : BoxKey 5 :=
  ⟨![12480, 11520, 8640, 5760, 0], ![360, 300, 240, 420, 0], ![12552, 11595, 8560, 5690, -80], true⟩

theorem canonicalMatch5_7 :
    canonicalPose5_7.boxKey 19200 (referenceBox5 (!canonicalBox5_7.bump)) = canonicalBox5_7 := by decide

theorem canonicalDecode5_7 : canonicalBox5_7.toKeyData 19200 = keys5Chunk0.get ⟨7, by decide⟩ := by
  change canonicalBox5_7.toKeyData 19200 = ⟨![(13 / 20), (3 / 5), (9 / 20), (3 / 10), 0], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(523 / 800), (773 / 1280), (107 / 240), (569 / 1920), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_7, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_7, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_7, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_7 : keySolid (keys5Chunk0.get ⟨7, by decide⟩) = canonicalPose5_7.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_7 (box := canonicalBox5_7) (k := keys5Chunk0.get ⟨7, by decide⟩) (canonicalMatch5_7) (canonicalDecode5_7)

def canonicalPose5_8 : Pose 5 :=
  ⟨canonicalPerm5_19, ![false, true, true, false, true], ![0, 1, 1, 0, 2]⟩
def canonicalBox5_8 : BoxKey 5 :=
  ⟨![0, 5760, 8640, 11520, 25920], ![0, 420, 240, 300, 360], ![80, 5690, 8560, 11595, 25848], false⟩

theorem canonicalMatch5_8 :
    canonicalPose5_8.boxKey 19200 (referenceBox5 (!canonicalBox5_8.bump)) = canonicalBox5_8 := by decide

theorem canonicalDecode5_8 : canonicalBox5_8.toKeyData 19200 = keys5Chunk0.get ⟨8, by decide⟩ := by
  change canonicalBox5_8.toKeyData 19200 = ⟨![0, (3 / 10), (9 / 20), (3 / 5), (27 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(1 / 240), (569 / 1920), (107 / 240), (773 / 1280), (1077 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_8, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_8, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_8, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_8 : keySolid (keys5Chunk0.get ⟨8, by decide⟩) = canonicalPose5_8.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_8 (box := canonicalBox5_8) (k := keys5Chunk0.get ⟨8, by decide⟩) (canonicalMatch5_8) (canonicalDecode5_8)

def canonicalPose5_9 : Pose 5 :=
  ⟨canonicalPerm5_3, ![true, true, false, true, true], ![1, 0, 0, 1, 2]⟩
def canonicalBox5_9 : BoxKey 5 :=
  ⟨![8640, 0, 11520, 5760, 25920], ![240, 0, 300, 420, 360], ![8560, -80, 11595, 5690, 25848], true⟩

theorem canonicalMatch5_9 :
    canonicalPose5_9.boxKey 19200 (referenceBox5 (!canonicalBox5_9.bump)) = canonicalBox5_9 := by decide

theorem canonicalDecode5_9 : canonicalBox5_9.toKeyData 19200 = keys5Chunk0.get ⟨9, by decide⟩ := by
  change canonicalBox5_9.toKeyData 19200 = ⟨![(9 / 20), 0, (3 / 5), (3 / 10), (27 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(107 / 240), (-1 / 240), (773 / 1280), (569 / 1920), (1077 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_9, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_9, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_9, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_9 : keySolid (keys5Chunk0.get ⟨9, by decide⟩) = canonicalPose5_9.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_9 (box := canonicalBox5_9) (k := keys5Chunk0.get ⟨9, by decide⟩) (canonicalMatch5_9) (canonicalDecode5_9)

def canonicalPose5_10 : Pose 5 :=
  ⟨canonicalPerm5_13, ![true, false, true, true, true], ![1, 0, 0, 1, 2]⟩
def canonicalBox5_10 : BoxKey 5 :=
  ⟨![5760, 11520, 0, 8640, 25920], ![420, 300, 0, 240, 360], ![5690, 11595, -80, 8560, 25848], true⟩

theorem canonicalMatch5_10 :
    canonicalPose5_10.boxKey 19200 (referenceBox5 (!canonicalBox5_10.bump)) = canonicalBox5_10 := by decide

theorem canonicalDecode5_10 : canonicalBox5_10.toKeyData 19200 = keys5Chunk0.get ⟨10, by decide⟩ := by
  change canonicalBox5_10.toKeyData 19200 = ⟨![(3 / 10), (3 / 5), 0, (9 / 20), (27 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(569 / 1920), (773 / 1280), (-1 / 240), (107 / 240), (1077 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_10, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_10, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_10, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_10 : keySolid (keys5Chunk0.get ⟨10, by decide⟩) = canonicalPose5_10.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_10 (box := canonicalBox5_10) (k := keys5Chunk0.get ⟨10, by decide⟩) (canonicalMatch5_10) (canonicalDecode5_10)

def canonicalPose5_11 : Pose 5 :=
  ⟨canonicalPerm5_4, ![false, true, true, false, true], ![0, 1, 1, 0, 2]⟩
def canonicalBox5_11 : BoxKey 5 :=
  ⟨![11520, 8640, 5760, 0, 25920], ![300, 240, 420, 0, 360], ![11595, 8560, 5690, 80, 25848], false⟩

theorem canonicalMatch5_11 :
    canonicalPose5_11.boxKey 19200 (referenceBox5 (!canonicalBox5_11.bump)) = canonicalBox5_11 := by decide

theorem canonicalDecode5_11 : canonicalBox5_11.toKeyData 19200 = keys5Chunk0.get ⟨11, by decide⟩ := by
  change canonicalBox5_11.toKeyData 19200 = ⟨![(3 / 5), (9 / 20), (3 / 10), 0, (27 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(773 / 1280), (107 / 240), (569 / 1920), (1 / 240), (1077 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_11, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_11, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_11, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_11 : keySolid (keys5Chunk0.get ⟨11, by decide⟩) = canonicalPose5_11.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_11 (box := canonicalBox5_11) (k := keys5Chunk0.get ⟨11, by decide⟩) (canonicalMatch5_11) (canonicalDecode5_11)

def canonicalPose5_12 : Pose 5 :=
  ⟨canonicalPerm5_12, ![true, true, true, true, true], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_12 : BoxKey 5 :=
  ⟨![5760, 8640, 7680, 6720, 38400], ![420, 240, 300, 360, 0], ![5690, 8560, 7605, 6648, 38320], false⟩

theorem canonicalMatch5_12 :
    canonicalPose5_12.boxKey 19200 (referenceBox5 (!canonicalBox5_12.bump)) = canonicalBox5_12 := by decide

theorem canonicalDecode5_12 : canonicalBox5_12.toKeyData 19200 = keys5Chunk0.get ⟨12, by decide⟩ := by
  change canonicalBox5_12.toKeyData 19200 = ⟨![(3 / 10), (9 / 20), (2 / 5), (7 / 20), 2], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(569 / 1920), (107 / 240), (507 / 1280), (277 / 800), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_12, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_12, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_12, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_12 : keySolid (keys5Chunk0.get ⟨12, by decide⟩) = canonicalPose5_12.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_12 (box := canonicalBox5_12) (k := keys5Chunk0.get ⟨12, by decide⟩) (canonicalMatch5_12) (canonicalDecode5_12)

def canonicalPose5_13 : Pose 5 :=
  ⟨canonicalPerm5_9, ![true, true, true, true, true], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_13 : BoxKey 5 :=
  ⟨![6720, 7680, 8640, 5760, 38400], ![360, 300, 240, 420, 0], ![6648, 7605, 8560, 5690, 38320], false⟩

theorem canonicalMatch5_13 :
    canonicalPose5_13.boxKey 19200 (referenceBox5 (!canonicalBox5_13.bump)) = canonicalBox5_13 := by decide

theorem canonicalDecode5_13 : canonicalBox5_13.toKeyData 19200 = keys5Chunk0.get ⟨13, by decide⟩ := by
  change canonicalBox5_13.toKeyData 19200 = ⟨![(7 / 20), (2 / 5), (9 / 20), (3 / 10), 2], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(277 / 800), (507 / 1280), (107 / 240), (569 / 1920), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_13, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_13, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_13, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_13 : keySolid (keys5Chunk0.get ⟨13, by decide⟩) = canonicalPose5_13.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_13 (box := canonicalBox5_13) (k := keys5Chunk0.get ⟨13, by decide⟩) (canonicalMatch5_13) (canonicalDecode5_13)

def canonicalPose5_14 : Pose 5 :=
  ⟨canonicalPerm5_6, ![true, true, true, true, false], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_14 : BoxKey 5 :=
  ⟨![7680, 5760, 6720, 8640, 38400], ![300, 420, 360, 240, 0], ![7605, 5690, 6648, 8560, 38480], true⟩

theorem canonicalMatch5_14 :
    canonicalPose5_14.boxKey 19200 (referenceBox5 (!canonicalBox5_14.bump)) = canonicalBox5_14 := by decide

theorem canonicalDecode5_14 : canonicalBox5_14.toKeyData 19200 = keys5Chunk0.get ⟨14, by decide⟩ := by
  change canonicalBox5_14.toKeyData 19200 = ⟨![(2 / 5), (3 / 10), (7 / 20), (9 / 20), 2], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(507 / 1280), (569 / 1920), (277 / 800), (107 / 240), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_14, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_14, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_14, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_14 : keySolid (keys5Chunk0.get ⟨14, by decide⟩) = canonicalPose5_14.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_14 (box := canonicalBox5_14) (k := keys5Chunk0.get ⟨14, by decide⟩) (canonicalMatch5_14) (canonicalDecode5_14)

def canonicalPose5_15 : Pose 5 :=
  ⟨canonicalPerm5_1, ![true, true, true, true, false], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_15 : BoxKey 5 :=
  ⟨![8640, 6720, 5760, 7680, 38400], ![240, 360, 420, 300, 0], ![8560, 6648, 5690, 7605, 38480], true⟩

theorem canonicalMatch5_15 :
    canonicalPose5_15.boxKey 19200 (referenceBox5 (!canonicalBox5_15.bump)) = canonicalBox5_15 := by decide

theorem canonicalDecode5_15 : canonicalBox5_15.toKeyData 19200 = keys5Chunk0.get ⟨15, by decide⟩ := by
  change canonicalBox5_15.toKeyData 19200 = ⟨![(9 / 20), (7 / 20), (3 / 10), (2 / 5), 2], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(107 / 240), (277 / 800), (569 / 1920), (507 / 1280), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_15, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_15, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_15, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_15 : keySolid (keys5Chunk0.get ⟨15, by decide⟩) = canonicalPose5_15.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_15 (box := canonicalBox5_15) (k := keys5Chunk0.get ⟨15, by decide⟩) (canonicalMatch5_15) (canonicalDecode5_15)

def canonicalPose5_16 : Pose 5 :=
  ⟨canonicalPerm5_17, ![true, false, true, true, true], ![0, 0, 1, 2, 1]⟩
def canonicalBox5_16 : BoxKey 5 :=
  ⟨![0, 11520, 5760, 25920, 8640], ![0, 300, 420, 360, 240], ![-80, 11595, 5690, 25848, 8560], true⟩

theorem canonicalMatch5_16 :
    canonicalPose5_16.boxKey 19200 (referenceBox5 (!canonicalBox5_16.bump)) = canonicalBox5_16 := by decide

theorem canonicalDecode5_16 : canonicalBox5_16.toKeyData 19200 = keys5Chunk0.get ⟨16, by decide⟩ := by
  change canonicalBox5_16.toKeyData 19200 = ⟨![0, (3 / 5), (3 / 10), (27 / 20), (9 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(-1 / 240), (773 / 1280), (569 / 1920), (1077 / 800), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_16, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_16, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_16, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_16 : keySolid (keys5Chunk0.get ⟨16, by decide⟩) = canonicalPose5_16.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_16 (box := canonicalBox5_16) (k := keys5Chunk0.get ⟨16, by decide⟩) (canonicalMatch5_16) (canonicalDecode5_16)

def canonicalPose5_17 : Pose 5 :=
  ⟨canonicalPerm5_7, ![false, true, true, true, true], ![0, 0, 1, 2, 1]⟩
def canonicalBox5_17 : BoxKey 5 :=
  ⟨![11520, 0, 8640, 25920, 5760], ![300, 0, 240, 360, 420], ![11595, -80, 8560, 25848, 5690], true⟩

theorem canonicalMatch5_17 :
    canonicalPose5_17.boxKey 19200 (referenceBox5 (!canonicalBox5_17.bump)) = canonicalBox5_17 := by decide

theorem canonicalDecode5_17 : canonicalBox5_17.toKeyData 19200 = keys5Chunk0.get ⟨17, by decide⟩ := by
  change canonicalBox5_17.toKeyData 19200 = ⟨![(3 / 5), 0, (9 / 20), (27 / 20), (3 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(773 / 1280), (-1 / 240), (107 / 240), (1077 / 800), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_17, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_17, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_17, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_17 : keySolid (keys5Chunk0.get ⟨17, by decide⟩) = canonicalPose5_17.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_17 (box := canonicalBox5_17) (k := keys5Chunk0.get ⟨17, by decide⟩) (canonicalMatch5_17) (canonicalDecode5_17)

def canonicalPose5_18 : Pose 5 :=
  ⟨canonicalPerm5_2, ![true, true, false, true, false], ![1, 1, 0, 2, 0]⟩
def canonicalBox5_18 : BoxKey 5 :=
  ⟨![8640, 5760, 0, 25920, 11520], ![240, 420, 0, 360, 300], ![8560, 5690, 80, 25848, 11595], false⟩

theorem canonicalMatch5_18 :
    canonicalPose5_18.boxKey 19200 (referenceBox5 (!canonicalBox5_18.bump)) = canonicalBox5_18 := by decide

theorem canonicalDecode5_18 : canonicalBox5_18.toKeyData 19200 = keys5Chunk0.get ⟨18, by decide⟩ := by
  change canonicalBox5_18.toKeyData 19200 = ⟨![(9 / 20), (3 / 10), 0, (27 / 20), (3 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(107 / 240), (569 / 1920), (1 / 240), (1077 / 800), (773 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_18, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_18, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_18, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_18 : keySolid (keys5Chunk0.get ⟨18, by decide⟩) = canonicalPose5_18.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_18 (box := canonicalBox5_18) (k := keys5Chunk0.get ⟨18, by decide⟩) (canonicalMatch5_18) (canonicalDecode5_18)

def canonicalPose5_19 : Pose 5 :=
  ⟨canonicalPerm5_14, ![true, true, true, false, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_19 : BoxKey 5 :=
  ⟨![5760, 6720, 8640, 38400, 7680], ![420, 360, 240, 0, 300], ![5690, 6648, 8560, 38480, 7605], true⟩

theorem canonicalMatch5_19 :
    canonicalPose5_19.boxKey 19200 (referenceBox5 (!canonicalBox5_19.bump)) = canonicalBox5_19 := by decide

theorem canonicalDecode5_19 : canonicalBox5_19.toKeyData 19200 = keys5Chunk0.get ⟨19, by decide⟩ := by
  change canonicalBox5_19.toKeyData 19200 = ⟨![(3 / 10), (7 / 20), (9 / 20), 2, (2 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(569 / 1920), (277 / 800), (107 / 240), (481 / 240), (507 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_19, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_19, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_19, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_19 : keySolid (keys5Chunk0.get ⟨19, by decide⟩) = canonicalPose5_19.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_19 (box := canonicalBox5_19) (k := keys5Chunk0.get ⟨19, by decide⟩) (canonicalMatch5_19) (canonicalDecode5_19)

def canonicalPose5_20 : Pose 5 :=
  ⟨canonicalPerm5_10, ![true, true, true, false, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_20 : BoxKey 5 :=
  ⟨![6720, 5760, 7680, 38400, 8640], ![360, 420, 300, 0, 240], ![6648, 5690, 7605, 38480, 8560], true⟩

theorem canonicalMatch5_20 :
    canonicalPose5_20.boxKey 19200 (referenceBox5 (!canonicalBox5_20.bump)) = canonicalBox5_20 := by decide

theorem canonicalDecode5_20 : canonicalBox5_20.toKeyData 19200 = keys5Chunk0.get ⟨20, by decide⟩ := by
  change canonicalBox5_20.toKeyData 19200 = ⟨![(7 / 20), (3 / 10), (2 / 5), 2, (9 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(277 / 800), (569 / 1920), (507 / 1280), (481 / 240), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_20, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_20, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_20, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_20 : keySolid (keys5Chunk0.get ⟨20, by decide⟩) = canonicalPose5_20.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_20 (box := canonicalBox5_20) (k := keys5Chunk0.get ⟨20, by decide⟩) (canonicalMatch5_20) (canonicalDecode5_20)

def canonicalPose5_21 : Pose 5 :=
  ⟨canonicalPerm5_4, ![true, true, true, true, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_21 : BoxKey 5 :=
  ⟨![7680, 8640, 5760, 38400, 6720], ![300, 240, 420, 0, 360], ![7605, 8560, 5690, 38320, 6648], false⟩

theorem canonicalMatch5_21 :
    canonicalPose5_21.boxKey 19200 (referenceBox5 (!canonicalBox5_21.bump)) = canonicalBox5_21 := by decide

theorem canonicalDecode5_21 : canonicalBox5_21.toKeyData 19200 = keys5Chunk0.get ⟨21, by decide⟩ := by
  change canonicalBox5_21.toKeyData 19200 = ⟨![(2 / 5), (9 / 20), (3 / 10), 2, (7 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(507 / 1280), (107 / 240), (569 / 1920), (479 / 240), (277 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_21, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_21, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_21, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_21 : keySolid (keys5Chunk0.get ⟨21, by decide⟩) = canonicalPose5_21.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_21 (box := canonicalBox5_21) (k := keys5Chunk0.get ⟨21, by decide⟩) (canonicalMatch5_21) (canonicalDecode5_21)

def canonicalPose5_22 : Pose 5 :=
  ⟨canonicalPerm5_0, ![true, true, true, true, true], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_22 : BoxKey 5 :=
  ⟨![8640, 7680, 6720, 38400, 5760], ![240, 300, 360, 0, 420], ![8560, 7605, 6648, 38320, 5690], false⟩

theorem canonicalMatch5_22 :
    canonicalPose5_22.boxKey 19200 (referenceBox5 (!canonicalBox5_22.bump)) = canonicalBox5_22 := by decide

theorem canonicalDecode5_22 : canonicalBox5_22.toKeyData 19200 = keys5Chunk0.get ⟨22, by decide⟩ := by
  change canonicalBox5_22.toKeyData 19200 = ⟨![(9 / 20), (2 / 5), (7 / 20), 2, (3 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(107 / 240), (507 / 1280), (277 / 800), (479 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_22, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_22, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_22, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_22 : keySolid (keys5Chunk0.get ⟨22, by decide⟩) = canonicalPose5_22.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_22 (box := canonicalBox5_22) (k := keys5Chunk0.get ⟨22, by decide⟩) (canonicalMatch5_22) (canonicalDecode5_22)

def canonicalPose5_23 : Pose 5 :=
  ⟨canonicalPerm5_12, ![true, true, false, true, false], ![1, 1, 0, 2, 0]⟩
def canonicalBox5_23 : BoxKey 5 :=
  ⟨![5760, 8640, 11520, 25920, 0], ![420, 240, 300, 360, 0], ![5690, 8560, 11595, 25848, 80], false⟩

theorem canonicalMatch5_23 :
    canonicalPose5_23.boxKey 19200 (referenceBox5 (!canonicalBox5_23.bump)) = canonicalBox5_23 := by decide

theorem canonicalDecode5_23 : canonicalBox5_23.toKeyData 19200 = keys5Chunk0.get ⟨23, by decide⟩ := by
  change canonicalBox5_23.toKeyData 19200 = ⟨![(3 / 10), (9 / 20), (3 / 5), (27 / 20), 0], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(569 / 1920), (107 / 240), (773 / 1280), (1077 / 800), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_23, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_23, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_23, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_23 : keySolid (keys5Chunk0.get ⟨23, by decide⟩) = canonicalPose5_23.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_23 (box := canonicalBox5_23) (k := keys5Chunk0.get ⟨23, by decide⟩) (canonicalMatch5_23) (canonicalDecode5_23)

def canonicalPose5_24 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, false, false, false, false], ![0, 0, 0, 1, 1]⟩
def canonicalBox5_24 : BoxKey 5 :=
  ⟨![0, 12480, 11520, 29760, 32640], ![0, 360, 300, 240, 420], ![-80, 12552, 11595, 29840, 32710], true⟩

theorem canonicalMatch5_24 :
    canonicalPose5_24.boxKey 19200 (referenceBox5 (!canonicalBox5_24.bump)) = canonicalBox5_24 := by decide

theorem canonicalDecode5_24 : canonicalBox5_24.toKeyData 19200 = keys5Chunk0.get ⟨24, by decide⟩ := by
  change canonicalBox5_24.toKeyData 19200 = ⟨![0, (13 / 20), (3 / 5), (31 / 20), (17 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(-1 / 240), (523 / 800), (773 / 1280), (373 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_24, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_24, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_24, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_24 : keySolid (keys5Chunk0.get ⟨24, by decide⟩) = canonicalPose5_24.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_24 (box := canonicalBox5_24) (k := keys5Chunk0.get ⟨24, by decide⟩) (canonicalMatch5_24) (canonicalDecode5_24)

def canonicalPose5_25 : Pose 5 :=
  ⟨canonicalPerm5_15, ![true, true, true, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_25 : BoxKey 5 :=
  ⟨![5760, 0, 6720, 30720, 29760], ![420, 0, 360, 300, 240], ![5690, -80, 6648, 30795, 29840], true⟩

theorem canonicalMatch5_25 :
    canonicalPose5_25.boxKey 19200 (referenceBox5 (!canonicalBox5_25.bump)) = canonicalBox5_25 := by decide

theorem canonicalDecode5_25 : canonicalBox5_25.toKeyData 19200 = keys5Chunk0.get ⟨25, by decide⟩ := by
  change canonicalBox5_25.toKeyData 19200 = ⟨![(3 / 10), 0, (7 / 20), (8 / 5), (31 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(569 / 1920), (-1 / 240), (277 / 800), (2053 / 1280), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_25, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_25, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_25, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_25 : keySolid (keys5Chunk0.get ⟨25, by decide⟩) = canonicalPose5_25.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_25 (box := canonicalBox5_25) (k := keys5Chunk0.get ⟨25, by decide⟩) (canonicalMatch5_25) (canonicalDecode5_25)

def canonicalPose5_26 : Pose 5 :=
  ⟨canonicalPerm5_11, ![true, true, true, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_26 : BoxKey 5 :=
  ⟨![6720, 0, 5760, 29760, 30720], ![360, 0, 420, 240, 300], ![6648, -80, 5690, 29840, 30795], true⟩

theorem canonicalMatch5_26 :
    canonicalPose5_26.boxKey 19200 (referenceBox5 (!canonicalBox5_26.bump)) = canonicalBox5_26 := by decide

theorem canonicalDecode5_26 : canonicalBox5_26.toKeyData 19200 = keys5Chunk0.get ⟨26, by decide⟩ := by
  change canonicalBox5_26.toKeyData 19200 = ⟨![(7 / 20), 0, (3 / 10), (31 / 20), (8 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(277 / 800), (-1 / 240), (569 / 1920), (373 / 240), (2053 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_26, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_26, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_26, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_26 : keySolid (keys5Chunk0.get ⟨26, by decide⟩) = canonicalPose5_26.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_26 (box := canonicalBox5_26) (k := keys5Chunk0.get ⟨26, by decide⟩) (canonicalMatch5_26) (canonicalDecode5_26)

def canonicalPose5_27 : Pose 5 :=
  ⟨canonicalPerm5_7, ![true, false, true, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_27 : BoxKey 5 :=
  ⟨![7680, 0, 8640, 31680, 32640], ![300, 0, 240, 360, 420], ![7605, 80, 8560, 31752, 32710], false⟩

theorem canonicalMatch5_27 :
    canonicalPose5_27.boxKey 19200 (referenceBox5 (!canonicalBox5_27.bump)) = canonicalBox5_27 := by decide

theorem canonicalDecode5_27 : canonicalBox5_27.toKeyData 19200 = keys5Chunk0.get ⟨27, by decide⟩ := by
  change canonicalBox5_27.toKeyData 19200 = ⟨![(2 / 5), 0, (9 / 20), (33 / 20), (17 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(507 / 1280), (1 / 240), (107 / 240), (1323 / 800), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_27, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_27, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_27, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_27 : keySolid (keys5Chunk0.get ⟨27, by decide⟩) = canonicalPose5_27.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_27 (box := canonicalBox5_27) (k := keys5Chunk0.get ⟨27, by decide⟩) (canonicalMatch5_27) (canonicalDecode5_27)

def canonicalPose5_28 : Pose 5 :=
  ⟨canonicalPerm5_3, ![true, false, true, false, false], ![1, 0, 1, 1, 1]⟩
def canonicalBox5_28 : BoxKey 5 :=
  ⟨![8640, 0, 7680, 32640, 31680], ![240, 0, 300, 420, 360], ![8560, 80, 7605, 32710, 31752], false⟩

theorem canonicalMatch5_28 :
    canonicalPose5_28.boxKey 19200 (referenceBox5 (!canonicalBox5_28.bump)) = canonicalBox5_28 := by decide

theorem canonicalDecode5_28 : canonicalBox5_28.toKeyData 19200 = keys5Chunk0.get ⟨28, by decide⟩ := by
  change canonicalBox5_28.toKeyData 19200 = ⟨![(9 / 20), 0, (2 / 5), (17 / 10), (33 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(107 / 240), (1 / 240), (507 / 1280), (3271 / 1920), (1323 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_28, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_28, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_28, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_28 : keySolid (keys5Chunk0.get ⟨28, by decide⟩) = canonicalPose5_28.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_28 (box := canonicalBox5_28) (k := keys5Chunk0.get ⟨28, by decide⟩) (canonicalMatch5_28) (canonicalDecode5_28)

def canonicalPose5_29 : Pose 5 :=
  ⟨canonicalPerm5_5, ![false, false, true, false, false], ![0, 0, 0, 1, 1]⟩
def canonicalBox5_29 : BoxKey 5 :=
  ⟨![11520, 12480, 0, 32640, 29760], ![300, 360, 0, 420, 240], ![11595, 12552, -80, 32710, 29840], true⟩

theorem canonicalMatch5_29 :
    canonicalPose5_29.boxKey 19200 (referenceBox5 (!canonicalBox5_29.bump)) = canonicalBox5_29 := by decide

theorem canonicalDecode5_29 : canonicalBox5_29.toKeyData 19200 = keys5Chunk0.get ⟨29, by decide⟩ := by
  change canonicalBox5_29.toKeyData 19200 = ⟨![(3 / 5), (13 / 20), 0, (17 / 10), (31 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(773 / 1280), (523 / 800), (-1 / 240), (3271 / 1920), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_29, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_29, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_29, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_29 : keySolid (keys5Chunk0.get ⟨29, by decide⟩) = canonicalPose5_29.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_29 (box := canonicalBox5_29) (k := keys5Chunk0.get ⟨29, by decide⟩) (canonicalMatch5_29) (canonicalDecode5_29)

def canonicalPose5_30 : Pose 5 :=
  ⟨canonicalPerm5_14, ![true, false, true, true, true], ![1, 0, 1, 2, 2]⟩
def canonicalBox5_30 : BoxKey 5 :=
  ⟨![5760, 12480, 8640, 38400, 26880], ![420, 360, 240, 0, 300], ![5690, 12552, 8560, 38320, 26805], false⟩

theorem canonicalMatch5_30 :
    canonicalPose5_30.boxKey 19200 (referenceBox5 (!canonicalBox5_30.bump)) = canonicalBox5_30 := by decide

theorem canonicalDecode5_30 : canonicalBox5_30.toKeyData 19200 = keys5Chunk0.get ⟨30, by decide⟩ := by
  change canonicalBox5_30.toKeyData 19200 = ⟨![(3 / 10), (13 / 20), (9 / 20), 2, (7 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(569 / 1920), (523 / 800), (107 / 240), (479 / 240), (1787 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_30, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_30, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_30, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_30 : keySolid (keys5Chunk0.get ⟨30, by decide⟩) = canonicalPose5_30.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_30 (box := canonicalBox5_30) (k := keys5Chunk0.get ⟨30, by decide⟩) (canonicalMatch5_30) (canonicalDecode5_30)

def canonicalPose5_31 : Pose 5 :=
  ⟨canonicalPerm5_1, ![true, false, true, true, true], ![1, 0, 1, 2, 2]⟩
def canonicalBox5_31 : BoxKey 5 :=
  ⟨![8640, 12480, 5760, 26880, 38400], ![240, 360, 420, 300, 0], ![8560, 12552, 5690, 26805, 38320], false⟩

theorem canonicalMatch5_31 :
    canonicalPose5_31.boxKey 19200 (referenceBox5 (!canonicalBox5_31.bump)) = canonicalBox5_31 := by decide

theorem canonicalDecode5_31 : canonicalBox5_31.toKeyData 19200 = keys5Chunk0.get ⟨31, by decide⟩ := by
  change canonicalBox5_31.toKeyData 19200 = ⟨![(9 / 20), (13 / 20), (3 / 10), (7 / 5), 2], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(107 / 240), (523 / 800), (569 / 1920), (1787 / 1280), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_31, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_31, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_31, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_31 : keySolid (keys5Chunk0.get ⟨31, by decide⟩) = canonicalPose5_31.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_31 (box := canonicalBox5_31) (k := keys5Chunk0.get ⟨31, by decide⟩) (canonicalMatch5_31) (canonicalDecode5_31)

theorem keys5Chunk0_canonical : ∀ k ∈ keys5Chunk0,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_0, canonicalSolid5_0⟩
  · exact ⟨canonicalPose5_1, canonicalSolid5_1⟩
  · exact ⟨canonicalPose5_2, canonicalSolid5_2⟩
  · exact ⟨canonicalPose5_3, canonicalSolid5_3⟩
  · exact ⟨canonicalPose5_4, canonicalSolid5_4⟩
  · exact ⟨canonicalPose5_5, canonicalSolid5_5⟩
  · exact ⟨canonicalPose5_6, canonicalSolid5_6⟩
  · exact ⟨canonicalPose5_7, canonicalSolid5_7⟩
  · exact ⟨canonicalPose5_8, canonicalSolid5_8⟩
  · exact ⟨canonicalPose5_9, canonicalSolid5_9⟩
  · exact ⟨canonicalPose5_10, canonicalSolid5_10⟩
  · exact ⟨canonicalPose5_11, canonicalSolid5_11⟩
  · exact ⟨canonicalPose5_12, canonicalSolid5_12⟩
  · exact ⟨canonicalPose5_13, canonicalSolid5_13⟩
  · exact ⟨canonicalPose5_14, canonicalSolid5_14⟩
  · exact ⟨canonicalPose5_15, canonicalSolid5_15⟩
  · exact ⟨canonicalPose5_16, canonicalSolid5_16⟩
  · exact ⟨canonicalPose5_17, canonicalSolid5_17⟩
  · exact ⟨canonicalPose5_18, canonicalSolid5_18⟩
  · exact ⟨canonicalPose5_19, canonicalSolid5_19⟩
  · exact ⟨canonicalPose5_20, canonicalSolid5_20⟩
  · exact ⟨canonicalPose5_21, canonicalSolid5_21⟩
  · exact ⟨canonicalPose5_22, canonicalSolid5_22⟩
  · exact ⟨canonicalPose5_23, canonicalSolid5_23⟩
  · exact ⟨canonicalPose5_24, canonicalSolid5_24⟩
  · exact ⟨canonicalPose5_25, canonicalSolid5_25⟩
  · exact ⟨canonicalPose5_26, canonicalSolid5_26⟩
  · exact ⟨canonicalPose5_27, canonicalSolid5_27⟩
  · exact ⟨canonicalPose5_28, canonicalSolid5_28⟩
  · exact ⟨canonicalPose5_29, canonicalSolid5_29⟩
  · exact ⟨canonicalPose5_30, canonicalSolid5_30⟩
  · exact ⟨canonicalPose5_31, canonicalSolid5_31⟩

#print axioms keys5Chunk0_canonical

end SparseMonotiles.Canonical
