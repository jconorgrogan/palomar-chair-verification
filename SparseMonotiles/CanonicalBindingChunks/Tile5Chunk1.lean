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

def canonicalPose5_32 : Pose 5 :=
  ⟨canonicalPerm5_16, ![true, true, true, true, false], ![0, 1, 2, 1, 0]⟩
def canonicalBox5_32 : BoxKey 5 :=
  ⟨![0, 8640, 25920, 5760, 11520], ![0, 240, 360, 420, 300], ![-80, 8560, 25848, 5690, 11595], true⟩

theorem canonicalMatch5_32 :
    canonicalPose5_32.boxKey 19200 (referenceBox5 (!canonicalBox5_32.bump)) = canonicalBox5_32 := by decide

theorem canonicalDecode5_32 : canonicalBox5_32.toKeyData 19200 = keys5Chunk1.get ⟨0, by decide⟩ := by
  change canonicalBox5_32.toKeyData 19200 = ⟨![0, (9 / 20), (27 / 20), (3 / 10), (3 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(-1 / 240), (107 / 240), (1077 / 800), (569 / 1920), (773 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_32, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_32, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_32, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_32 : keySolid (keys5Chunk1.get ⟨0, by decide⟩) = canonicalPose5_32.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_32 (box := canonicalBox5_32) (k := keys5Chunk1.get ⟨0, by decide⟩) (canonicalMatch5_32) (canonicalDecode5_32)

def canonicalPose5_33 : Pose 5 :=
  ⟨canonicalPerm5_15, ![true, false, true, false, true], ![1, 0, 2, 0, 1]⟩
def canonicalBox5_33 : BoxKey 5 :=
  ⟨![5760, 0, 25920, 11520, 8640], ![420, 0, 360, 300, 240], ![5690, 80, 25848, 11595, 8560], false⟩

theorem canonicalMatch5_33 :
    canonicalPose5_33.boxKey 19200 (referenceBox5 (!canonicalBox5_33.bump)) = canonicalBox5_33 := by decide

theorem canonicalDecode5_33 : canonicalBox5_33.toKeyData 19200 = keys5Chunk1.get ⟨1, by decide⟩ := by
  change canonicalBox5_33.toKeyData 19200 = ⟨![(3 / 10), 0, (27 / 20), (3 / 5), (9 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(569 / 1920), (1 / 240), (1077 / 800), (773 / 1280), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_33, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_33, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_33, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_33 : keySolid (keys5Chunk1.get ⟨1, by decide⟩) = canonicalPose5_33.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_33 (box := canonicalBox5_33) (k := keys5Chunk1.get ⟨1, by decide⟩) (canonicalMatch5_33) (canonicalDecode5_33)

def canonicalPose5_34 : Pose 5 :=
  ⟨canonicalPerm5_13, ![true, true, false, true, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_34 : BoxKey 5 :=
  ⟨![5760, 7680, 38400, 8640, 6720], ![420, 300, 0, 240, 360], ![5690, 7605, 38480, 8560, 6648], true⟩

theorem canonicalMatch5_34 :
    canonicalPose5_34.boxKey 19200 (referenceBox5 (!canonicalBox5_34.bump)) = canonicalBox5_34 := by decide

theorem canonicalDecode5_34 : canonicalBox5_34.toKeyData 19200 = keys5Chunk1.get ⟨2, by decide⟩ := by
  change canonicalBox5_34.toKeyData 19200 = ⟨![(3 / 10), (2 / 5), 2, (9 / 20), (7 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(569 / 1920), (507 / 1280), (481 / 240), (107 / 240), (277 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_34, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_34, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_34, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_34 : keySolid (keys5Chunk1.get ⟨2, by decide⟩) = canonicalPose5_34.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_34 (box := canonicalBox5_34) (k := keys5Chunk1.get ⟨2, by decide⟩) (canonicalMatch5_34) (canonicalDecode5_34)

def canonicalPose5_35 : Pose 5 :=
  ⟨canonicalPerm5_8, ![true, true, false, true, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_35 : BoxKey 5 :=
  ⟨![6720, 8640, 38400, 7680, 5760], ![360, 240, 0, 300, 420], ![6648, 8560, 38480, 7605, 5690], true⟩

theorem canonicalMatch5_35 :
    canonicalPose5_35.boxKey 19200 (referenceBox5 (!canonicalBox5_35.bump)) = canonicalBox5_35 := by decide

theorem canonicalDecode5_35 : canonicalBox5_35.toKeyData 19200 = keys5Chunk1.get ⟨3, by decide⟩ := by
  change canonicalBox5_35.toKeyData 19200 = ⟨![(7 / 20), (9 / 20), 2, (2 / 5), (3 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(277 / 800), (107 / 240), (481 / 240), (507 / 1280), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_35, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_35, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_35, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_35 : keySolid (keys5Chunk1.get ⟨3, by decide⟩) = canonicalPose5_35.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_35 (box := canonicalBox5_35) (k := keys5Chunk1.get ⟨3, by decide⟩) (canonicalMatch5_35) (canonicalDecode5_35)

def canonicalPose5_36 : Pose 5 :=
  ⟨canonicalPerm5_5, ![true, true, true, true, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_36 : BoxKey 5 :=
  ⟨![7680, 6720, 38400, 5760, 8640], ![300, 360, 0, 420, 240], ![7605, 6648, 38320, 5690, 8560], false⟩

theorem canonicalMatch5_36 :
    canonicalPose5_36.boxKey 19200 (referenceBox5 (!canonicalBox5_36.bump)) = canonicalBox5_36 := by decide

theorem canonicalDecode5_36 : canonicalBox5_36.toKeyData 19200 = keys5Chunk1.get ⟨4, by decide⟩ := by
  change canonicalBox5_36.toKeyData 19200 = ⟨![(2 / 5), (7 / 20), 2, (3 / 10), (9 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(507 / 1280), (277 / 800), (479 / 240), (569 / 1920), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_36, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_36, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_36, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_36 : keySolid (keys5Chunk1.get ⟨4, by decide⟩) = canonicalPose5_36.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_36 (box := canonicalBox5_36) (k := keys5Chunk1.get ⟨4, by decide⟩) (canonicalMatch5_36) (canonicalDecode5_36)

def canonicalPose5_37 : Pose 5 :=
  ⟨canonicalPerm5_2, ![true, true, true, true, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_37 : BoxKey 5 :=
  ⟨![8640, 5760, 38400, 6720, 7680], ![240, 420, 0, 360, 300], ![8560, 5690, 38320, 6648, 7605], false⟩

theorem canonicalMatch5_37 :
    canonicalPose5_37.boxKey 19200 (referenceBox5 (!canonicalBox5_37.bump)) = canonicalBox5_37 := by decide

theorem canonicalDecode5_37 : canonicalBox5_37.toKeyData 19200 = keys5Chunk1.get ⟨5, by decide⟩ := by
  change canonicalBox5_37.toKeyData 19200 = ⟨![(9 / 20), (3 / 10), 2, (7 / 20), (2 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(107 / 240), (569 / 1920), (479 / 240), (277 / 800), (507 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_37, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_37, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_37, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_37 : keySolid (keys5Chunk1.get ⟨5, by decide⟩) = canonicalPose5_37.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_37 (box := canonicalBox5_37) (k := keys5Chunk1.get ⟨5, by decide⟩) (canonicalMatch5_37) (canonicalDecode5_37)

def canonicalPose5_38 : Pose 5 :=
  ⟨canonicalPerm5_0, ![true, false, true, false, true], ![1, 0, 2, 0, 1]⟩
def canonicalBox5_38 : BoxKey 5 :=
  ⟨![8640, 11520, 25920, 0, 5760], ![240, 300, 360, 0, 420], ![8560, 11595, 25848, 80, 5690], false⟩

theorem canonicalMatch5_38 :
    canonicalPose5_38.boxKey 19200 (referenceBox5 (!canonicalBox5_38.bump)) = canonicalBox5_38 := by decide

theorem canonicalDecode5_38 : canonicalBox5_38.toKeyData 19200 = keys5Chunk1.get ⟨6, by decide⟩ := by
  change canonicalBox5_38.toKeyData 19200 = ⟨![(9 / 20), (3 / 5), (27 / 20), 0, (3 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(107 / 240), (773 / 1280), (1077 / 800), (1 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_38, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_38, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_38, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_38 : keySolid (keys5Chunk1.get ⟨6, by decide⟩) = canonicalPose5_38.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_38 (box := canonicalBox5_38) (k := keys5Chunk1.get ⟨6, by decide⟩) (canonicalMatch5_38) (canonicalDecode5_38)

def canonicalPose5_39 : Pose 5 :=
  ⟨canonicalPerm5_6, ![false, true, true, true, true], ![0, 1, 2, 1, 0]⟩
def canonicalBox5_39 : BoxKey 5 :=
  ⟨![11520, 5760, 25920, 8640, 0], ![300, 420, 360, 240, 0], ![11595, 5690, 25848, 8560, -80], true⟩

theorem canonicalMatch5_39 :
    canonicalPose5_39.boxKey 19200 (referenceBox5 (!canonicalBox5_39.bump)) = canonicalBox5_39 := by decide

theorem canonicalDecode5_39 : canonicalBox5_39.toKeyData 19200 = keys5Chunk1.get ⟨7, by decide⟩ := by
  change canonicalBox5_39.toKeyData 19200 = ⟨![(3 / 5), (3 / 10), (27 / 20), (9 / 20), 0], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(773 / 1280), (569 / 1920), (1077 / 800), (107 / 240), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_39, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_39, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_39, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_39 : keySolid (keys5Chunk1.get ⟨7, by decide⟩) = canonicalPose5_39.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_39 (box := canonicalBox5_39) (k := keys5Chunk1.get ⟨7, by decide⟩) (canonicalMatch5_39) (canonicalDecode5_39)

def canonicalPose5_40 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, false, false, false, false], ![0, 0, 1, 0, 1]⟩
def canonicalBox5_40 : BoxKey 5 :=
  ⟨![0, 11520, 32640, 12480, 29760], ![0, 300, 420, 360, 240], ![80, 11595, 32710, 12552, 29840], false⟩

theorem canonicalMatch5_40 :
    canonicalPose5_40.boxKey 19200 (referenceBox5 (!canonicalBox5_40.bump)) = canonicalBox5_40 := by decide

theorem canonicalDecode5_40 : canonicalBox5_40.toKeyData 19200 = keys5Chunk1.get ⟨8, by decide⟩ := by
  change canonicalBox5_40.toKeyData 19200 = ⟨![0, (3 / 5), (17 / 10), (13 / 20), (31 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(1 / 240), (773 / 1280), (3271 / 1920), (523 / 800), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_40, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_40, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_40, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_40 : keySolid (keys5Chunk1.get ⟨8, by decide⟩) = canonicalPose5_40.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_40 (box := canonicalBox5_40) (k := keys5Chunk1.get ⟨8, by decide⟩) (canonicalMatch5_40) (canonicalDecode5_40)

def canonicalPose5_41 : Pose 5 :=
  ⟨canonicalPerm5_7, ![false, false, false, false, false], ![0, 0, 1, 0, 1]⟩
def canonicalBox5_41 : BoxKey 5 :=
  ⟨![11520, 0, 29760, 12480, 32640], ![300, 0, 240, 360, 420], ![11595, 80, 29840, 12552, 32710], false⟩

theorem canonicalMatch5_41 :
    canonicalPose5_41.boxKey 19200 (referenceBox5 (!canonicalBox5_41.bump)) = canonicalBox5_41 := by decide

theorem canonicalDecode5_41 : canonicalBox5_41.toKeyData 19200 = keys5Chunk1.get ⟨9, by decide⟩ := by
  change canonicalBox5_41.toKeyData 19200 = ⟨![(3 / 5), 0, (31 / 20), (13 / 20), (17 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(773 / 1280), (1 / 240), (373 / 240), (523 / 800), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_41, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_41, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_41, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_41 : keySolid (keys5Chunk1.get ⟨9, by decide⟩) = canonicalPose5_41.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_41 (box := canonicalBox5_41) (k := keys5Chunk1.get ⟨9, by decide⟩) (canonicalMatch5_41) (canonicalDecode5_41)

def canonicalPose5_42 : Pose 5 :=
  ⟨canonicalPerm5_2, ![true, true, false, false, true], ![1, 1, 2, 0, 2]⟩
def canonicalBox5_42 : BoxKey 5 :=
  ⟨![8640, 5760, 38400, 12480, 26880], ![240, 420, 0, 360, 300], ![8560, 5690, 38480, 12552, 26805], true⟩

theorem canonicalMatch5_42 :
    canonicalPose5_42.boxKey 19200 (referenceBox5 (!canonicalBox5_42.bump)) = canonicalBox5_42 := by decide

theorem canonicalDecode5_42 : canonicalBox5_42.toKeyData 19200 = keys5Chunk1.get ⟨10, by decide⟩ := by
  change canonicalBox5_42.toKeyData 19200 = ⟨![(9 / 20), (3 / 10), 2, (13 / 20), (7 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(107 / 240), (569 / 1920), (481 / 240), (523 / 800), (1787 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_42, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_42, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_42, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_42 : keySolid (keys5Chunk1.get ⟨10, by decide⟩) = canonicalPose5_42.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_42 (box := canonicalBox5_42) (k := keys5Chunk1.get ⟨10, by decide⟩) (canonicalMatch5_42) (canonicalDecode5_42)

def canonicalPose5_43 : Pose 5 :=
  ⟨canonicalPerm5_14, ![true, true, false, false, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_43 : BoxKey 5 :=
  ⟨![5760, 6720, 29760, 0, 30720], ![420, 360, 240, 0, 300], ![5690, 6648, 29840, 80, 30795], false⟩

theorem canonicalMatch5_43 :
    canonicalPose5_43.boxKey 19200 (referenceBox5 (!canonicalBox5_43.bump)) = canonicalBox5_43 := by decide

theorem canonicalDecode5_43 : canonicalBox5_43.toKeyData 19200 = keys5Chunk1.get ⟨11, by decide⟩ := by
  change canonicalBox5_43.toKeyData 19200 = ⟨![(3 / 10), (7 / 20), (31 / 20), 0, (8 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(569 / 1920), (277 / 800), (373 / 240), (1 / 240), (2053 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_43, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_43, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_43, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_43 : keySolid (keys5Chunk1.get ⟨11, by decide⟩) = canonicalPose5_43.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_43 (box := canonicalBox5_43) (k := keys5Chunk1.get ⟨11, by decide⟩) (canonicalMatch5_43) (canonicalDecode5_43)

def canonicalPose5_44 : Pose 5 :=
  ⟨canonicalPerm5_10, ![true, true, false, false, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_44 : BoxKey 5 :=
  ⟨![6720, 5760, 30720, 0, 29760], ![360, 420, 300, 0, 240], ![6648, 5690, 30795, 80, 29840], false⟩

theorem canonicalMatch5_44 :
    canonicalPose5_44.boxKey 19200 (referenceBox5 (!canonicalBox5_44.bump)) = canonicalBox5_44 := by decide

theorem canonicalDecode5_44 : canonicalBox5_44.toKeyData 19200 = keys5Chunk1.get ⟨12, by decide⟩ := by
  change canonicalBox5_44.toKeyData 19200 = ⟨![(7 / 20), (3 / 10), (8 / 5), 0, (31 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(277 / 800), (569 / 1920), (2053 / 1280), (1 / 240), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_44, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_44, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_44, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_44 : keySolid (keys5Chunk1.get ⟨12, by decide⟩) = canonicalPose5_44.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_44 (box := canonicalBox5_44) (k := keys5Chunk1.get ⟨12, by decide⟩) (canonicalMatch5_44) (canonicalDecode5_44)

def canonicalPose5_45 : Pose 5 :=
  ⟨canonicalPerm5_4, ![true, true, false, true, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_45 : BoxKey 5 :=
  ⟨![7680, 8640, 32640, 0, 31680], ![300, 240, 420, 0, 360], ![7605, 8560, 32710, -80, 31752], true⟩

theorem canonicalMatch5_45 :
    canonicalPose5_45.boxKey 19200 (referenceBox5 (!canonicalBox5_45.bump)) = canonicalBox5_45 := by decide

theorem canonicalDecode5_45 : canonicalBox5_45.toKeyData 19200 = keys5Chunk1.get ⟨13, by decide⟩ := by
  change canonicalBox5_45.toKeyData 19200 = ⟨![(2 / 5), (9 / 20), (17 / 10), 0, (33 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(507 / 1280), (107 / 240), (3271 / 1920), (-1 / 240), (1323 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_45, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_45, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_45, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_45 : keySolid (keys5Chunk1.get ⟨13, by decide⟩) = canonicalPose5_45.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_45 (box := canonicalBox5_45) (k := keys5Chunk1.get ⟨13, by decide⟩) (canonicalMatch5_45) (canonicalDecode5_45)

def canonicalPose5_46 : Pose 5 :=
  ⟨canonicalPerm5_0, ![true, true, false, true, false], ![1, 1, 1, 0, 1]⟩
def canonicalBox5_46 : BoxKey 5 :=
  ⟨![8640, 7680, 31680, 0, 32640], ![240, 300, 360, 0, 420], ![8560, 7605, 31752, -80, 32710], true⟩

theorem canonicalMatch5_46 :
    canonicalPose5_46.boxKey 19200 (referenceBox5 (!canonicalBox5_46.bump)) = canonicalBox5_46 := by decide

theorem canonicalDecode5_46 : canonicalBox5_46.toKeyData 19200 = keys5Chunk1.get ⟨14, by decide⟩ := by
  change canonicalBox5_46.toKeyData 19200 = ⟨![(9 / 20), (2 / 5), (33 / 20), 0, (17 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(107 / 240), (507 / 1280), (1323 / 800), (-1 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_46, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_46, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_46, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_46 : keySolid (keys5Chunk1.get ⟨14, by decide⟩) = canonicalPose5_46.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_46 (box := canonicalBox5_46) (k := keys5Chunk1.get ⟨14, by decide⟩) (canonicalMatch5_46) (canonicalDecode5_46)

def canonicalPose5_47 : Pose 5 :=
  ⟨canonicalPerm5_12, ![true, true, true, false, false], ![1, 1, 2, 0, 2]⟩
def canonicalBox5_47 : BoxKey 5 :=
  ⟨![5760, 8640, 26880, 12480, 38400], ![420, 240, 300, 360, 0], ![5690, 8560, 26805, 12552, 38480], true⟩

theorem canonicalMatch5_47 :
    canonicalPose5_47.boxKey 19200 (referenceBox5 (!canonicalBox5_47.bump)) = canonicalBox5_47 := by decide

theorem canonicalDecode5_47 : canonicalBox5_47.toKeyData 19200 = keys5Chunk1.get ⟨15, by decide⟩ := by
  change canonicalBox5_47.toKeyData 19200 = ⟨![(3 / 10), (9 / 20), (7 / 5), (13 / 20), 2], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(569 / 1920), (107 / 240), (1787 / 1280), (523 / 800), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_47, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_47, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_47, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_47 : keySolid (keys5Chunk1.get ⟨15, by decide⟩) = canonicalPose5_47.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_47 (box := canonicalBox5_47) (k := keys5Chunk1.get ⟨15, by decide⟩) (canonicalMatch5_47) (canonicalDecode5_47)

def canonicalPose5_48 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, true, false, false, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_48 : BoxKey 5 :=
  ⟨![0, 5760, 29760, 30720, 6720], ![0, 420, 240, 300, 360], ![-80, 5690, 29840, 30795, 6648], true⟩

theorem canonicalMatch5_48 :
    canonicalPose5_48.boxKey 19200 (referenceBox5 (!canonicalBox5_48.bump)) = canonicalBox5_48 := by decide

theorem canonicalDecode5_48 : canonicalBox5_48.toKeyData 19200 = keys5Chunk1.get ⟨16, by decide⟩ := by
  change canonicalBox5_48.toKeyData 19200 = ⟨![0, (3 / 10), (31 / 20), (8 / 5), (7 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(-1 / 240), (569 / 1920), (373 / 240), (2053 / 1280), (277 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_48, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_48, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_48, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_48 : keySolid (keys5Chunk1.get ⟨16, by decide⟩) = canonicalPose5_48.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_48 (box := canonicalBox5_48) (k := keys5Chunk1.get ⟨16, by decide⟩) (canonicalMatch5_48) (canonicalDecode5_48)

def canonicalPose5_49 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, true, false, false, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_49 : BoxKey 5 :=
  ⟨![0, 6720, 30720, 29760, 5760], ![0, 360, 300, 240, 420], ![-80, 6648, 30795, 29840, 5690], true⟩

theorem canonicalMatch5_49 :
    canonicalPose5_49.boxKey 19200 (referenceBox5 (!canonicalBox5_49.bump)) = canonicalBox5_49 := by decide

theorem canonicalDecode5_49 : canonicalBox5_49.toKeyData 19200 = keys5Chunk1.get ⟨17, by decide⟩ := by
  change canonicalBox5_49.toKeyData 19200 = ⟨![0, (7 / 20), (8 / 5), (31 / 20), (3 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(-1 / 240), (277 / 800), (2053 / 1280), (373 / 240), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_49, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_49, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_49, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_49 : keySolid (keys5Chunk1.get ⟨17, by decide⟩) = canonicalPose5_49.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_49 (box := canonicalBox5_49) (k := keys5Chunk1.get ⟨17, by decide⟩) (canonicalMatch5_49) (canonicalDecode5_49)

def canonicalPose5_50 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, true, false, false, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_50 : BoxKey 5 :=
  ⟨![0, 7680, 32640, 31680, 8640], ![0, 300, 420, 360, 240], ![80, 7605, 32710, 31752, 8560], false⟩

theorem canonicalMatch5_50 :
    canonicalPose5_50.boxKey 19200 (referenceBox5 (!canonicalBox5_50.bump)) = canonicalBox5_50 := by decide

theorem canonicalDecode5_50 : canonicalBox5_50.toKeyData 19200 = keys5Chunk1.get ⟨18, by decide⟩ := by
  change canonicalBox5_50.toKeyData 19200 = ⟨![0, (2 / 5), (17 / 10), (33 / 20), (9 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(1 / 240), (507 / 1280), (3271 / 1920), (1323 / 800), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_50, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_50, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_50, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_50 : keySolid (keys5Chunk1.get ⟨18, by decide⟩) = canonicalPose5_50.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_50 (box := canonicalBox5_50) (k := keys5Chunk1.get ⟨18, by decide⟩) (canonicalMatch5_50) (canonicalDecode5_50)

def canonicalPose5_51 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, true, false, false, true], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_51 : BoxKey 5 :=
  ⟨![0, 8640, 31680, 32640, 7680], ![0, 240, 360, 420, 300], ![80, 8560, 31752, 32710, 7605], false⟩

theorem canonicalMatch5_51 :
    canonicalPose5_51.boxKey 19200 (referenceBox5 (!canonicalBox5_51.bump)) = canonicalBox5_51 := by decide

theorem canonicalDecode5_51 : canonicalBox5_51.toKeyData 19200 = keys5Chunk1.get ⟨19, by decide⟩ := by
  change canonicalBox5_51.toKeyData 19200 = ⟨![0, (9 / 20), (33 / 20), (17 / 10), (2 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(1 / 240), (107 / 240), (1323 / 800), (3271 / 1920), (507 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_51, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_51, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_51, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_51 : keySolid (keys5Chunk1.get ⟨19, by decide⟩) = canonicalPose5_51.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_51 (box := canonicalBox5_51) (k := keys5Chunk1.get ⟨19, by decide⟩) (canonicalMatch5_51) (canonicalDecode5_51)

def canonicalPose5_52 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, true, false, false, false], ![0, 0, 1, 1, 0]⟩
def canonicalBox5_52 : BoxKey 5 :=
  ⟨![12480, 0, 32640, 29760, 11520], ![360, 0, 420, 240, 300], ![12552, -80, 32710, 29840, 11595], true⟩

theorem canonicalMatch5_52 :
    canonicalPose5_52.boxKey 19200 (referenceBox5 (!canonicalBox5_52.bump)) = canonicalBox5_52 := by decide

theorem canonicalDecode5_52 : canonicalBox5_52.toKeyData 19200 = keys5Chunk1.get ⟨20, by decide⟩ := by
  change canonicalBox5_52.toKeyData 19200 = ⟨![(13 / 20), 0, (17 / 10), (31 / 20), (3 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(523 / 800), (-1 / 240), (3271 / 1920), (373 / 240), (773 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_52, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_52, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_52, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_52 : keySolid (keys5Chunk1.get ⟨20, by decide⟩) = canonicalPose5_52.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_52 (box := canonicalBox5_52) (k := keys5Chunk1.get ⟨20, by decide⟩) (canonicalMatch5_52) (canonicalDecode5_52)

def canonicalPose5_53 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, true, true, true, true], ![0, 1, 2, 2, 1]⟩
def canonicalBox5_53 : BoxKey 5 :=
  ⟨![12480, 8640, 38400, 26880, 5760], ![360, 240, 0, 300, 420], ![12552, 8560, 38320, 26805, 5690], false⟩

theorem canonicalMatch5_53 :
    canonicalPose5_53.boxKey 19200 (referenceBox5 (!canonicalBox5_53.bump)) = canonicalBox5_53 := by decide

theorem canonicalDecode5_53 : canonicalBox5_53.toKeyData 19200 = keys5Chunk1.get ⟨21, by decide⟩ := by
  change canonicalBox5_53.toKeyData 19200 = ⟨![(13 / 20), (9 / 20), 2, (7 / 5), (3 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(523 / 800), (107 / 240), (479 / 240), (1787 / 1280), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_53, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_53, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_53, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_53 : keySolid (keys5Chunk1.get ⟨21, by decide⟩) = canonicalPose5_53.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_53 (box := canonicalBox5_53) (k := keys5Chunk1.get ⟨21, by decide⟩) (canonicalMatch5_53) (canonicalDecode5_53)

def canonicalPose5_54 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, true, true, true, true], ![0, 1, 2, 2, 1]⟩
def canonicalBox5_54 : BoxKey 5 :=
  ⟨![12480, 5760, 26880, 38400, 8640], ![360, 420, 300, 0, 240], ![12552, 5690, 26805, 38320, 8560], false⟩

theorem canonicalMatch5_54 :
    canonicalPose5_54.boxKey 19200 (referenceBox5 (!canonicalBox5_54.bump)) = canonicalBox5_54 := by decide

theorem canonicalDecode5_54 : canonicalBox5_54.toKeyData 19200 = keys5Chunk1.get ⟨22, by decide⟩ := by
  change canonicalBox5_54.toKeyData 19200 = ⟨![(13 / 20), (3 / 10), (7 / 5), 2, (9 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(523 / 800), (569 / 1920), (1787 / 1280), (479 / 240), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_54, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_54, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_54, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_54 : keySolid (keys5Chunk1.get ⟨22, by decide⟩) = canonicalPose5_54.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_54 (box := canonicalBox5_54) (k := keys5Chunk1.get ⟨22, by decide⟩) (canonicalMatch5_54) (canonicalDecode5_54)

def canonicalPose5_55 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, false, false, false, true], ![0, 0, 1, 1, 0]⟩
def canonicalBox5_55 : BoxKey 5 :=
  ⟨![12480, 11520, 29760, 32640, 0], ![360, 300, 240, 420, 0], ![12552, 11595, 29840, 32710, -80], true⟩

theorem canonicalMatch5_55 :
    canonicalPose5_55.boxKey 19200 (referenceBox5 (!canonicalBox5_55.bump)) = canonicalBox5_55 := by decide

theorem canonicalDecode5_55 : canonicalBox5_55.toKeyData 19200 = keys5Chunk1.get ⟨23, by decide⟩ := by
  change canonicalBox5_55.toKeyData 19200 = ⟨![(13 / 20), (3 / 5), (31 / 20), (17 / 10), 0], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(523 / 800), (773 / 1280), (373 / 240), (3271 / 1920), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_55, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_55, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_55, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_55 : keySolid (keys5Chunk1.get ⟨23, by decide⟩) = canonicalPose5_55.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_55 (box := canonicalBox5_55) (k := keys5Chunk1.get ⟨23, by decide⟩) (canonicalMatch5_55) (canonicalDecode5_55)

def canonicalPose5_56 : Pose 5 :=
  ⟨canonicalPerm5_17, ![true, false, false, true, false], ![0, 0, 1, 2, 1]⟩
def canonicalBox5_56 : BoxKey 5 :=
  ⟨![0, 11520, 32640, 25920, 29760], ![0, 300, 420, 360, 240], ![-80, 11595, 32710, 25848, 29840], true⟩

theorem canonicalMatch5_56 :
    canonicalPose5_56.boxKey 19200 (referenceBox5 (!canonicalBox5_56.bump)) = canonicalBox5_56 := by decide

theorem canonicalDecode5_56 : canonicalBox5_56.toKeyData 19200 = keys5Chunk1.get ⟨24, by decide⟩ := by
  change canonicalBox5_56.toKeyData 19200 = ⟨![0, (3 / 5), (17 / 10), (27 / 20), (31 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(-1 / 240), (773 / 1280), (3271 / 1920), (1077 / 800), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_56, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_56, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_56, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_56 : keySolid (keys5Chunk1.get ⟨24, by decide⟩) = canonicalPose5_56.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_56 (box := canonicalBox5_56) (k := keys5Chunk1.get ⟨24, by decide⟩) (canonicalMatch5_56) (canonicalDecode5_56)

def canonicalPose5_57 : Pose 5 :=
  ⟨canonicalPerm5_7, ![false, true, false, true, false], ![0, 0, 1, 2, 1]⟩
def canonicalBox5_57 : BoxKey 5 :=
  ⟨![11520, 0, 29760, 25920, 32640], ![300, 0, 240, 360, 420], ![11595, -80, 29840, 25848, 32710], true⟩

theorem canonicalMatch5_57 :
    canonicalPose5_57.boxKey 19200 (referenceBox5 (!canonicalBox5_57.bump)) = canonicalBox5_57 := by decide

theorem canonicalDecode5_57 : canonicalBox5_57.toKeyData 19200 = keys5Chunk1.get ⟨25, by decide⟩ := by
  change canonicalBox5_57.toKeyData 19200 = ⟨![(3 / 5), 0, (31 / 20), (27 / 20), (17 / 10)], ![(1 / 64), 0, (1 / 80), (3 / 160), (7 / 320)], ![(773 / 1280), (-1 / 240), (373 / 240), (1077 / 800), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_57, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_57, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_57, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_57 : keySolid (keys5Chunk1.get ⟨25, by decide⟩) = canonicalPose5_57.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_57 (box := canonicalBox5_57) (k := keys5Chunk1.get ⟨25, by decide⟩) (canonicalMatch5_57) (canonicalDecode5_57)

def canonicalPose5_58 : Pose 5 :=
  ⟨canonicalPerm5_2, ![true, true, true, true, true], ![1, 1, 2, 2, 2]⟩
def canonicalBox5_58 : BoxKey 5 :=
  ⟨![8640, 5760, 38400, 25920, 26880], ![240, 420, 0, 360, 300], ![8560, 5690, 38320, 25848, 26805], false⟩

theorem canonicalMatch5_58 :
    canonicalPose5_58.boxKey 19200 (referenceBox5 (!canonicalBox5_58.bump)) = canonicalBox5_58 := by decide

theorem canonicalDecode5_58 : canonicalBox5_58.toKeyData 19200 = keys5Chunk1.get ⟨26, by decide⟩ := by
  change canonicalBox5_58.toKeyData 19200 = ⟨![(9 / 20), (3 / 10), 2, (27 / 20), (7 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(107 / 240), (569 / 1920), (479 / 240), (1077 / 800), (1787 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_58, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_58, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_58, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_58 : keySolid (keys5Chunk1.get ⟨26, by decide⟩) = canonicalPose5_58.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_58 (box := canonicalBox5_58) (k := keys5Chunk1.get ⟨26, by decide⟩) (canonicalMatch5_58) (canonicalDecode5_58)

def canonicalPose5_59 : Pose 5 :=
  ⟨canonicalPerm5_14, ![true, true, false, false, false], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_59 : BoxKey 5 :=
  ⟨![5760, 6720, 29760, 38400, 30720], ![420, 360, 240, 0, 300], ![5690, 6648, 29840, 38480, 30795], true⟩

theorem canonicalMatch5_59 :
    canonicalPose5_59.boxKey 19200 (referenceBox5 (!canonicalBox5_59.bump)) = canonicalBox5_59 := by decide

theorem canonicalDecode5_59 : canonicalBox5_59.toKeyData 19200 = keys5Chunk1.get ⟨27, by decide⟩ := by
  change canonicalBox5_59.toKeyData 19200 = ⟨![(3 / 10), (7 / 20), (31 / 20), 2, (8 / 5)], ![(7 / 320), (3 / 160), (1 / 80), 0, (1 / 64)], ![(569 / 1920), (277 / 800), (373 / 240), (481 / 240), (2053 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_59, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_59, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_59, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_59 : keySolid (keys5Chunk1.get ⟨27, by decide⟩) = canonicalPose5_59.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_59 (box := canonicalBox5_59) (k := keys5Chunk1.get ⟨27, by decide⟩) (canonicalMatch5_59) (canonicalDecode5_59)

def canonicalPose5_60 : Pose 5 :=
  ⟨canonicalPerm5_10, ![true, true, false, false, false], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_60 : BoxKey 5 :=
  ⟨![6720, 5760, 30720, 38400, 29760], ![360, 420, 300, 0, 240], ![6648, 5690, 30795, 38480, 29840], true⟩

theorem canonicalMatch5_60 :
    canonicalPose5_60.boxKey 19200 (referenceBox5 (!canonicalBox5_60.bump)) = canonicalBox5_60 := by decide

theorem canonicalDecode5_60 : canonicalBox5_60.toKeyData 19200 = keys5Chunk1.get ⟨28, by decide⟩ := by
  change canonicalBox5_60.toKeyData 19200 = ⟨![(7 / 20), (3 / 10), (8 / 5), 2, (31 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(277 / 800), (569 / 1920), (2053 / 1280), (481 / 240), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_60, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_60, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_60, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_60 : keySolid (keys5Chunk1.get ⟨28, by decide⟩) = canonicalPose5_60.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_60 (box := canonicalBox5_60) (k := keys5Chunk1.get ⟨28, by decide⟩) (canonicalMatch5_60) (canonicalDecode5_60)

def canonicalPose5_61 : Pose 5 :=
  ⟨canonicalPerm5_4, ![true, true, false, true, false], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_61 : BoxKey 5 :=
  ⟨![7680, 8640, 32640, 38400, 31680], ![300, 240, 420, 0, 360], ![7605, 8560, 32710, 38320, 31752], false⟩

theorem canonicalMatch5_61 :
    canonicalPose5_61.boxKey 19200 (referenceBox5 (!canonicalBox5_61.bump)) = canonicalBox5_61 := by decide

theorem canonicalDecode5_61 : canonicalBox5_61.toKeyData 19200 = keys5Chunk1.get ⟨29, by decide⟩ := by
  change canonicalBox5_61.toKeyData 19200 = ⟨![(2 / 5), (9 / 20), (17 / 10), 2, (33 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(507 / 1280), (107 / 240), (3271 / 1920), (479 / 240), (1323 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_61, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_61, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_61, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_61 : keySolid (keys5Chunk1.get ⟨29, by decide⟩) = canonicalPose5_61.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_61 (box := canonicalBox5_61) (k := keys5Chunk1.get ⟨29, by decide⟩) (canonicalMatch5_61) (canonicalDecode5_61)

def canonicalPose5_62 : Pose 5 :=
  ⟨canonicalPerm5_0, ![true, true, false, true, false], ![1, 1, 1, 2, 1]⟩
def canonicalBox5_62 : BoxKey 5 :=
  ⟨![8640, 7680, 31680, 38400, 32640], ![240, 300, 360, 0, 420], ![8560, 7605, 31752, 38320, 32710], false⟩

theorem canonicalMatch5_62 :
    canonicalPose5_62.boxKey 19200 (referenceBox5 (!canonicalBox5_62.bump)) = canonicalBox5_62 := by decide

theorem canonicalDecode5_62 : canonicalBox5_62.toKeyData 19200 = keys5Chunk1.get ⟨30, by decide⟩ := by
  change canonicalBox5_62.toKeyData 19200 = ⟨![(9 / 20), (2 / 5), (33 / 20), 2, (17 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(107 / 240), (507 / 1280), (1323 / 800), (479 / 240), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_62, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_62, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_62, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_62 : keySolid (keys5Chunk1.get ⟨30, by decide⟩) = canonicalPose5_62.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_62 (box := canonicalBox5_62) (k := keys5Chunk1.get ⟨30, by decide⟩) (canonicalMatch5_62) (canonicalDecode5_62)

def canonicalPose5_63 : Pose 5 :=
  ⟨canonicalPerm5_12, ![true, true, true, true, true], ![1, 1, 2, 2, 2]⟩
def canonicalBox5_63 : BoxKey 5 :=
  ⟨![5760, 8640, 26880, 25920, 38400], ![420, 240, 300, 360, 0], ![5690, 8560, 26805, 25848, 38320], false⟩

theorem canonicalMatch5_63 :
    canonicalPose5_63.boxKey 19200 (referenceBox5 (!canonicalBox5_63.bump)) = canonicalBox5_63 := by decide

theorem canonicalDecode5_63 : canonicalBox5_63.toKeyData 19200 = keys5Chunk1.get ⟨31, by decide⟩ := by
  change canonicalBox5_63.toKeyData 19200 = ⟨![(3 / 10), (9 / 20), (7 / 5), (27 / 20), 2], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(569 / 1920), (107 / 240), (1787 / 1280), (1077 / 800), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_63, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_63, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_63, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_63 : keySolid (keys5Chunk1.get ⟨31, by decide⟩) = canonicalPose5_63.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_63 (box := canonicalBox5_63) (k := keys5Chunk1.get ⟨31, by decide⟩) (canonicalMatch5_63) (canonicalDecode5_63)

theorem keys5Chunk1_canonical : ∀ k ∈ keys5Chunk1,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_32, canonicalSolid5_32⟩
  · exact ⟨canonicalPose5_33, canonicalSolid5_33⟩
  · exact ⟨canonicalPose5_34, canonicalSolid5_34⟩
  · exact ⟨canonicalPose5_35, canonicalSolid5_35⟩
  · exact ⟨canonicalPose5_36, canonicalSolid5_36⟩
  · exact ⟨canonicalPose5_37, canonicalSolid5_37⟩
  · exact ⟨canonicalPose5_38, canonicalSolid5_38⟩
  · exact ⟨canonicalPose5_39, canonicalSolid5_39⟩
  · exact ⟨canonicalPose5_40, canonicalSolid5_40⟩
  · exact ⟨canonicalPose5_41, canonicalSolid5_41⟩
  · exact ⟨canonicalPose5_42, canonicalSolid5_42⟩
  · exact ⟨canonicalPose5_43, canonicalSolid5_43⟩
  · exact ⟨canonicalPose5_44, canonicalSolid5_44⟩
  · exact ⟨canonicalPose5_45, canonicalSolid5_45⟩
  · exact ⟨canonicalPose5_46, canonicalSolid5_46⟩
  · exact ⟨canonicalPose5_47, canonicalSolid5_47⟩
  · exact ⟨canonicalPose5_48, canonicalSolid5_48⟩
  · exact ⟨canonicalPose5_49, canonicalSolid5_49⟩
  · exact ⟨canonicalPose5_50, canonicalSolid5_50⟩
  · exact ⟨canonicalPose5_51, canonicalSolid5_51⟩
  · exact ⟨canonicalPose5_52, canonicalSolid5_52⟩
  · exact ⟨canonicalPose5_53, canonicalSolid5_53⟩
  · exact ⟨canonicalPose5_54, canonicalSolid5_54⟩
  · exact ⟨canonicalPose5_55, canonicalSolid5_55⟩
  · exact ⟨canonicalPose5_56, canonicalSolid5_56⟩
  · exact ⟨canonicalPose5_57, canonicalSolid5_57⟩
  · exact ⟨canonicalPose5_58, canonicalSolid5_58⟩
  · exact ⟨canonicalPose5_59, canonicalSolid5_59⟩
  · exact ⟨canonicalPose5_60, canonicalSolid5_60⟩
  · exact ⟨canonicalPose5_61, canonicalSolid5_61⟩
  · exact ⟨canonicalPose5_62, canonicalSolid5_62⟩
  · exact ⟨canonicalPose5_63, canonicalSolid5_63⟩

#print axioms keys5Chunk1_canonical

end SparseMonotiles.Canonical
