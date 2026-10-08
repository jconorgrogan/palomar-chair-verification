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

def canonicalPose5_96 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, false, false, false, false], ![0, 1, 1, 0, 0]⟩
def canonicalBox5_96 : BoxKey 5 :=
  ⟨![0, 32640, 29760, 11520, 12480], ![0, 420, 240, 300, 360], ![-80, 32710, 29840, 11595, 12552], true⟩

theorem canonicalMatch5_96 :
    canonicalPose5_96.boxKey 19200 (referenceBox5 (!canonicalBox5_96.bump)) = canonicalBox5_96 := by decide

theorem canonicalDecode5_96 : canonicalBox5_96.toKeyData 19200 = keys5Chunk3.get ⟨0, by decide⟩ := by
  change canonicalBox5_96.toKeyData 19200 = ⟨![0, (17 / 10), (31 / 20), (3 / 5), (13 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(-1 / 240), (3271 / 1920), (373 / 240), (773 / 1280), (523 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_96, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_96, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_96, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_96 : keySolid (keys5Chunk3.get ⟨0, by decide⟩) = canonicalPose5_96.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_96 (box := canonicalBox5_96) (k := keys5Chunk3.get ⟨0, by decide⟩) (canonicalMatch5_96) (canonicalDecode5_96)

def canonicalPose5_97 : Pose 5 :=
  ⟨canonicalPerm5_3, ![true, true, true, true, false], ![1, 2, 2, 1, 0]⟩
def canonicalBox5_97 : BoxKey 5 :=
  ⟨![8640, 38400, 26880, 5760, 12480], ![240, 0, 300, 420, 360], ![8560, 38320, 26805, 5690, 12552], false⟩

theorem canonicalMatch5_97 :
    canonicalPose5_97.boxKey 19200 (referenceBox5 (!canonicalBox5_97.bump)) = canonicalBox5_97 := by decide

theorem canonicalDecode5_97 : canonicalBox5_97.toKeyData 19200 = keys5Chunk3.get ⟨1, by decide⟩ := by
  change canonicalBox5_97.toKeyData 19200 = ⟨![(9 / 20), 2, (7 / 5), (3 / 10), (13 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(107 / 240), (479 / 240), (1787 / 1280), (569 / 1920), (523 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_97, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_97, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_97, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_97 : keySolid (keys5Chunk3.get ⟨1, by decide⟩) = canonicalPose5_97.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_97 (box := canonicalBox5_97) (k := keys5Chunk3.get ⟨1, by decide⟩) (canonicalMatch5_97) (canonicalDecode5_97)

def canonicalPose5_98 : Pose 5 :=
  ⟨canonicalPerm5_13, ![true, true, true, true, false], ![1, 2, 2, 1, 0]⟩
def canonicalBox5_98 : BoxKey 5 :=
  ⟨![5760, 26880, 38400, 8640, 12480], ![420, 300, 0, 240, 360], ![5690, 26805, 38320, 8560, 12552], false⟩

theorem canonicalMatch5_98 :
    canonicalPose5_98.boxKey 19200 (referenceBox5 (!canonicalBox5_98.bump)) = canonicalBox5_98 := by decide

theorem canonicalDecode5_98 : canonicalBox5_98.toKeyData 19200 = keys5Chunk3.get ⟨2, by decide⟩ := by
  change canonicalBox5_98.toKeyData 19200 = ⟨![(3 / 10), (7 / 5), 2, (9 / 20), (13 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(569 / 1920), (1787 / 1280), (479 / 240), (107 / 240), (523 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_98, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_98, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_98, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_98 : keySolid (keys5Chunk3.get ⟨2, by decide⟩) = canonicalPose5_98.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_98 (box := canonicalBox5_98) (k := keys5Chunk3.get ⟨2, by decide⟩) (canonicalMatch5_98) (canonicalDecode5_98)

def canonicalPose5_99 : Pose 5 :=
  ⟨canonicalPerm5_4, ![false, false, false, true, false], ![0, 1, 1, 0, 0]⟩
def canonicalBox5_99 : BoxKey 5 :=
  ⟨![11520, 29760, 32640, 0, 12480], ![300, 240, 420, 0, 360], ![11595, 29840, 32710, -80, 12552], true⟩

theorem canonicalMatch5_99 :
    canonicalPose5_99.boxKey 19200 (referenceBox5 (!canonicalBox5_99.bump)) = canonicalBox5_99 := by decide

theorem canonicalDecode5_99 : canonicalBox5_99.toKeyData 19200 = keys5Chunk3.get ⟨3, by decide⟩ := by
  change canonicalBox5_99.toKeyData 19200 = ⟨![(3 / 5), (31 / 20), (17 / 10), 0, (13 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(773 / 1280), (373 / 240), (3271 / 1920), (-1 / 240), (523 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_99, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_99, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_99, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_99 : keySolid (keys5Chunk3.get ⟨3, by decide⟩) = canonicalPose5_99.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_99 (box := canonicalBox5_99) (k := keys5Chunk3.get ⟨3, by decide⟩) (canonicalMatch5_99) (canonicalDecode5_99)

def canonicalPose5_100 : Pose 5 :=
  ⟨canonicalPerm5_12, ![true, false, false, true, true], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_100 : BoxKey 5 :=
  ⟨![5760, 29760, 30720, 6720, 0], ![420, 240, 300, 360, 0], ![5690, 29840, 30795, 6648, -80], true⟩

theorem canonicalMatch5_100 :
    canonicalPose5_100.boxKey 19200 (referenceBox5 (!canonicalBox5_100.bump)) = canonicalBox5_100 := by decide

theorem canonicalDecode5_100 : canonicalBox5_100.toKeyData 19200 = keys5Chunk3.get ⟨4, by decide⟩ := by
  change canonicalBox5_100.toKeyData 19200 = ⟨![(3 / 10), (31 / 20), (8 / 5), (7 / 20), 0], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(569 / 1920), (373 / 240), (2053 / 1280), (277 / 800), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_100, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_100, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_100, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_100 : keySolid (keys5Chunk3.get ⟨4, by decide⟩) = canonicalPose5_100.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_100 (box := canonicalBox5_100) (k := keys5Chunk3.get ⟨4, by decide⟩) (canonicalMatch5_100) (canonicalDecode5_100)

def canonicalPose5_101 : Pose 5 :=
  ⟨canonicalPerm5_9, ![true, false, false, true, true], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_101 : BoxKey 5 :=
  ⟨![6720, 30720, 29760, 5760, 0], ![360, 300, 240, 420, 0], ![6648, 30795, 29840, 5690, -80], true⟩

theorem canonicalMatch5_101 :
    canonicalPose5_101.boxKey 19200 (referenceBox5 (!canonicalBox5_101.bump)) = canonicalBox5_101 := by decide

theorem canonicalDecode5_101 : canonicalBox5_101.toKeyData 19200 = keys5Chunk3.get ⟨5, by decide⟩ := by
  change canonicalBox5_101.toKeyData 19200 = ⟨![(7 / 20), (8 / 5), (31 / 20), (3 / 10), 0], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(277 / 800), (2053 / 1280), (373 / 240), (569 / 1920), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_101, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_101, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_101, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_101 : keySolid (keys5Chunk3.get ⟨5, by decide⟩) = canonicalPose5_101.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_101 (box := canonicalBox5_101) (k := keys5Chunk3.get ⟨5, by decide⟩) (canonicalMatch5_101) (canonicalDecode5_101)

def canonicalPose5_102 : Pose 5 :=
  ⟨canonicalPerm5_6, ![true, false, false, true, false], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_102 : BoxKey 5 :=
  ⟨![7680, 32640, 31680, 8640, 0], ![300, 420, 360, 240, 0], ![7605, 32710, 31752, 8560, 80], false⟩

theorem canonicalMatch5_102 :
    canonicalPose5_102.boxKey 19200 (referenceBox5 (!canonicalBox5_102.bump)) = canonicalBox5_102 := by decide

theorem canonicalDecode5_102 : canonicalBox5_102.toKeyData 19200 = keys5Chunk3.get ⟨6, by decide⟩ := by
  change canonicalBox5_102.toKeyData 19200 = ⟨![(2 / 5), (17 / 10), (33 / 20), (9 / 20), 0], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(507 / 1280), (3271 / 1920), (1323 / 800), (107 / 240), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_102, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_102, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_102, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_102 : keySolid (keys5Chunk3.get ⟨6, by decide⟩) = canonicalPose5_102.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_102 (box := canonicalBox5_102) (k := keys5Chunk3.get ⟨6, by decide⟩) (canonicalMatch5_102) (canonicalDecode5_102)

def canonicalPose5_103 : Pose 5 :=
  ⟨canonicalPerm5_1, ![true, false, false, true, false], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_103 : BoxKey 5 :=
  ⟨![8640, 31680, 32640, 7680, 0], ![240, 360, 420, 300, 0], ![8560, 31752, 32710, 7605, 80], false⟩

theorem canonicalMatch5_103 :
    canonicalPose5_103.boxKey 19200 (referenceBox5 (!canonicalBox5_103.bump)) = canonicalBox5_103 := by decide

theorem canonicalDecode5_103 : canonicalBox5_103.toKeyData 19200 = keys5Chunk3.get ⟨7, by decide⟩ := by
  change canonicalBox5_103.toKeyData 19200 = ⟨![(9 / 20), (33 / 20), (17 / 10), (2 / 5), 0], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(107 / 240), (1323 / 800), (3271 / 1920), (507 / 1280), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_103, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_103, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_103, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_103 : keySolid (keys5Chunk3.get ⟨7, by decide⟩) = canonicalPose5_103.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_103 (box := canonicalBox5_103) (k := keys5Chunk3.get ⟨7, by decide⟩) (canonicalMatch5_103) (canonicalDecode5_103)

def canonicalPose5_104 : Pose 5 :=
  ⟨canonicalPerm5_19, ![false, false, false, false, true], ![0, 1, 1, 0, 2]⟩
def canonicalBox5_104 : BoxKey 5 :=
  ⟨![0, 32640, 29760, 11520, 25920], ![0, 420, 240, 300, 360], ![80, 32710, 29840, 11595, 25848], false⟩

theorem canonicalMatch5_104 :
    canonicalPose5_104.boxKey 19200 (referenceBox5 (!canonicalBox5_104.bump)) = canonicalBox5_104 := by decide

theorem canonicalDecode5_104 : canonicalBox5_104.toKeyData 19200 = keys5Chunk3.get ⟨8, by decide⟩ := by
  change canonicalBox5_104.toKeyData 19200 = ⟨![0, (17 / 10), (31 / 20), (3 / 5), (27 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(1 / 240), (3271 / 1920), (373 / 240), (773 / 1280), (1077 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_104, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_104, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_104, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_104 : keySolid (keys5Chunk3.get ⟨8, by decide⟩) = canonicalPose5_104.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_104 (box := canonicalBox5_104) (k := keys5Chunk3.get ⟨8, by decide⟩) (canonicalMatch5_104) (canonicalDecode5_104)

def canonicalPose5_105 : Pose 5 :=
  ⟨canonicalPerm5_3, ![true, false, true, true, true], ![1, 2, 2, 1, 2]⟩
def canonicalBox5_105 : BoxKey 5 :=
  ⟨![8640, 38400, 26880, 5760, 25920], ![240, 0, 300, 420, 360], ![8560, 38480, 26805, 5690, 25848], true⟩

theorem canonicalMatch5_105 :
    canonicalPose5_105.boxKey 19200 (referenceBox5 (!canonicalBox5_105.bump)) = canonicalBox5_105 := by decide

theorem canonicalDecode5_105 : canonicalBox5_105.toKeyData 19200 = keys5Chunk3.get ⟨9, by decide⟩ := by
  change canonicalBox5_105.toKeyData 19200 = ⟨![(9 / 20), 2, (7 / 5), (3 / 10), (27 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(107 / 240), (481 / 240), (1787 / 1280), (569 / 1920), (1077 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_105, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_105, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_105, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_105 : keySolid (keys5Chunk3.get ⟨9, by decide⟩) = canonicalPose5_105.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_105 (box := canonicalBox5_105) (k := keys5Chunk3.get ⟨9, by decide⟩) (canonicalMatch5_105) (canonicalDecode5_105)

def canonicalPose5_106 : Pose 5 :=
  ⟨canonicalPerm5_13, ![true, true, false, true, true], ![1, 2, 2, 1, 2]⟩
def canonicalBox5_106 : BoxKey 5 :=
  ⟨![5760, 26880, 38400, 8640, 25920], ![420, 300, 0, 240, 360], ![5690, 26805, 38480, 8560, 25848], true⟩

theorem canonicalMatch5_106 :
    canonicalPose5_106.boxKey 19200 (referenceBox5 (!canonicalBox5_106.bump)) = canonicalBox5_106 := by decide

theorem canonicalDecode5_106 : canonicalBox5_106.toKeyData 19200 = keys5Chunk3.get ⟨10, by decide⟩ := by
  change canonicalBox5_106.toKeyData 19200 = ⟨![(3 / 10), (7 / 5), 2, (9 / 20), (27 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(569 / 1920), (1787 / 1280), (481 / 240), (107 / 240), (1077 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_106, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_106, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_106, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_106 : keySolid (keys5Chunk3.get ⟨10, by decide⟩) = canonicalPose5_106.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_106 (box := canonicalBox5_106) (k := keys5Chunk3.get ⟨10, by decide⟩) (canonicalMatch5_106) (canonicalDecode5_106)

def canonicalPose5_107 : Pose 5 :=
  ⟨canonicalPerm5_4, ![false, false, false, false, true], ![0, 1, 1, 0, 2]⟩
def canonicalBox5_107 : BoxKey 5 :=
  ⟨![11520, 29760, 32640, 0, 25920], ![300, 240, 420, 0, 360], ![11595, 29840, 32710, 80, 25848], false⟩

theorem canonicalMatch5_107 :
    canonicalPose5_107.boxKey 19200 (referenceBox5 (!canonicalBox5_107.bump)) = canonicalBox5_107 := by decide

theorem canonicalDecode5_107 : canonicalBox5_107.toKeyData 19200 = keys5Chunk3.get ⟨11, by decide⟩ := by
  change canonicalBox5_107.toKeyData 19200 = ⟨![(3 / 5), (31 / 20), (17 / 10), 0, (27 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(773 / 1280), (373 / 240), (3271 / 1920), (1 / 240), (1077 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_107, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_107, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_107, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_107 : keySolid (keys5Chunk3.get ⟨11, by decide⟩) = canonicalPose5_107.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_107 (box := canonicalBox5_107) (k := keys5Chunk3.get ⟨11, by decide⟩) (canonicalMatch5_107) (canonicalDecode5_107)

def canonicalPose5_108 : Pose 5 :=
  ⟨canonicalPerm5_12, ![true, false, false, true, true], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_108 : BoxKey 5 :=
  ⟨![5760, 29760, 30720, 6720, 38400], ![420, 240, 300, 360, 0], ![5690, 29840, 30795, 6648, 38320], false⟩

theorem canonicalMatch5_108 :
    canonicalPose5_108.boxKey 19200 (referenceBox5 (!canonicalBox5_108.bump)) = canonicalBox5_108 := by decide

theorem canonicalDecode5_108 : canonicalBox5_108.toKeyData 19200 = keys5Chunk3.get ⟨12, by decide⟩ := by
  change canonicalBox5_108.toKeyData 19200 = ⟨![(3 / 10), (31 / 20), (8 / 5), (7 / 20), 2], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(569 / 1920), (373 / 240), (2053 / 1280), (277 / 800), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_108, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_108, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_108, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_108 : keySolid (keys5Chunk3.get ⟨12, by decide⟩) = canonicalPose5_108.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_108 (box := canonicalBox5_108) (k := keys5Chunk3.get ⟨12, by decide⟩) (canonicalMatch5_108) (canonicalDecode5_108)

def canonicalPose5_109 : Pose 5 :=
  ⟨canonicalPerm5_9, ![true, false, false, true, true], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_109 : BoxKey 5 :=
  ⟨![6720, 30720, 29760, 5760, 38400], ![360, 300, 240, 420, 0], ![6648, 30795, 29840, 5690, 38320], false⟩

theorem canonicalMatch5_109 :
    canonicalPose5_109.boxKey 19200 (referenceBox5 (!canonicalBox5_109.bump)) = canonicalBox5_109 := by decide

theorem canonicalDecode5_109 : canonicalBox5_109.toKeyData 19200 = keys5Chunk3.get ⟨13, by decide⟩ := by
  change canonicalBox5_109.toKeyData 19200 = ⟨![(7 / 20), (8 / 5), (31 / 20), (3 / 10), 2], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(277 / 800), (2053 / 1280), (373 / 240), (569 / 1920), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_109, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_109, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_109, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_109 : keySolid (keys5Chunk3.get ⟨13, by decide⟩) = canonicalPose5_109.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_109 (box := canonicalBox5_109) (k := keys5Chunk3.get ⟨13, by decide⟩) (canonicalMatch5_109) (canonicalDecode5_109)

def canonicalPose5_110 : Pose 5 :=
  ⟨canonicalPerm5_6, ![true, false, false, true, false], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_110 : BoxKey 5 :=
  ⟨![7680, 32640, 31680, 8640, 38400], ![300, 420, 360, 240, 0], ![7605, 32710, 31752, 8560, 38480], true⟩

theorem canonicalMatch5_110 :
    canonicalPose5_110.boxKey 19200 (referenceBox5 (!canonicalBox5_110.bump)) = canonicalBox5_110 := by decide

theorem canonicalDecode5_110 : canonicalBox5_110.toKeyData 19200 = keys5Chunk3.get ⟨14, by decide⟩ := by
  change canonicalBox5_110.toKeyData 19200 = ⟨![(2 / 5), (17 / 10), (33 / 20), (9 / 20), 2], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(507 / 1280), (3271 / 1920), (1323 / 800), (107 / 240), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_110, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_110, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_110, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_110 : keySolid (keys5Chunk3.get ⟨14, by decide⟩) = canonicalPose5_110.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_110 (box := canonicalBox5_110) (k := keys5Chunk3.get ⟨14, by decide⟩) (canonicalMatch5_110) (canonicalDecode5_110)

def canonicalPose5_111 : Pose 5 :=
  ⟨canonicalPerm5_1, ![true, false, false, true, false], ![1, 1, 1, 1, 2]⟩
def canonicalBox5_111 : BoxKey 5 :=
  ⟨![8640, 31680, 32640, 7680, 38400], ![240, 360, 420, 300, 0], ![8560, 31752, 32710, 7605, 38480], true⟩

theorem canonicalMatch5_111 :
    canonicalPose5_111.boxKey 19200 (referenceBox5 (!canonicalBox5_111.bump)) = canonicalBox5_111 := by decide

theorem canonicalDecode5_111 : canonicalBox5_111.toKeyData 19200 = keys5Chunk3.get ⟨15, by decide⟩ := by
  change canonicalBox5_111.toKeyData 19200 = ⟨![(9 / 20), (33 / 20), (17 / 10), (2 / 5), 2], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(107 / 240), (1323 / 800), (3271 / 1920), (507 / 1280), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_111, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_111, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_111, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_111 : keySolid (keys5Chunk3.get ⟨15, by decide⟩) = canonicalPose5_111.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_111 (box := canonicalBox5_111) (k := keys5Chunk3.get ⟨15, by decide⟩) (canonicalMatch5_111) (canonicalDecode5_111)

def canonicalPose5_112 : Pose 5 :=
  ⟨canonicalPerm5_16, ![true, false, true, false, false], ![0, 1, 2, 1, 0]⟩
def canonicalBox5_112 : BoxKey 5 :=
  ⟨![0, 29760, 25920, 32640, 11520], ![0, 240, 360, 420, 300], ![-80, 29840, 25848, 32710, 11595], true⟩

theorem canonicalMatch5_112 :
    canonicalPose5_112.boxKey 19200 (referenceBox5 (!canonicalBox5_112.bump)) = canonicalBox5_112 := by decide

theorem canonicalDecode5_112 : canonicalBox5_112.toKeyData 19200 = keys5Chunk3.get ⟨16, by decide⟩ := by
  change canonicalBox5_112.toKeyData 19200 = ⟨![0, (31 / 20), (27 / 20), (17 / 10), (3 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(-1 / 240), (373 / 240), (1077 / 800), (3271 / 1920), (773 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_112, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_112, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_112, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_112 : keySolid (keys5Chunk3.get ⟨16, by decide⟩) = canonicalPose5_112.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_112 (box := canonicalBox5_112) (k := keys5Chunk3.get ⟨16, by decide⟩) (canonicalMatch5_112) (canonicalDecode5_112)

def canonicalPose5_113 : Pose 5 :=
  ⟨canonicalPerm5_15, ![true, true, true, true, true], ![1, 2, 2, 2, 1]⟩
def canonicalBox5_113 : BoxKey 5 :=
  ⟨![5760, 38400, 25920, 26880, 8640], ![420, 0, 360, 300, 240], ![5690, 38320, 25848, 26805, 8560], false⟩

theorem canonicalMatch5_113 :
    canonicalPose5_113.boxKey 19200 (referenceBox5 (!canonicalBox5_113.bump)) = canonicalBox5_113 := by decide

theorem canonicalDecode5_113 : canonicalBox5_113.toKeyData 19200 = keys5Chunk3.get ⟨17, by decide⟩ := by
  change canonicalBox5_113.toKeyData 19200 = ⟨![(3 / 10), 2, (27 / 20), (7 / 5), (9 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(569 / 1920), (479 / 240), (1077 / 800), (1787 / 1280), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_113, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_113, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_113, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_113 : keySolid (keys5Chunk3.get ⟨17, by decide⟩) = canonicalPose5_113.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_113 (box := canonicalBox5_113) (k := keys5Chunk3.get ⟨17, by decide⟩) (canonicalMatch5_113) (canonicalDecode5_113)

def canonicalPose5_114 : Pose 5 :=
  ⟨canonicalPerm5_13, ![true, false, false, false, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_114 : BoxKey 5 :=
  ⟨![5760, 30720, 38400, 29760, 6720], ![420, 300, 0, 240, 360], ![5690, 30795, 38480, 29840, 6648], true⟩

theorem canonicalMatch5_114 :
    canonicalPose5_114.boxKey 19200 (referenceBox5 (!canonicalBox5_114.bump)) = canonicalBox5_114 := by decide

theorem canonicalDecode5_114 : canonicalBox5_114.toKeyData 19200 = keys5Chunk3.get ⟨18, by decide⟩ := by
  change canonicalBox5_114.toKeyData 19200 = ⟨![(3 / 10), (8 / 5), 2, (31 / 20), (7 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(569 / 1920), (2053 / 1280), (481 / 240), (373 / 240), (277 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_114, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_114, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_114, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_114 : keySolid (keys5Chunk3.get ⟨18, by decide⟩) = canonicalPose5_114.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_114 (box := canonicalBox5_114) (k := keys5Chunk3.get ⟨18, by decide⟩) (canonicalMatch5_114) (canonicalDecode5_114)

def canonicalPose5_115 : Pose 5 :=
  ⟨canonicalPerm5_8, ![true, false, false, false, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_115 : BoxKey 5 :=
  ⟨![6720, 29760, 38400, 30720, 5760], ![360, 240, 0, 300, 420], ![6648, 29840, 38480, 30795, 5690], true⟩

theorem canonicalMatch5_115 :
    canonicalPose5_115.boxKey 19200 (referenceBox5 (!canonicalBox5_115.bump)) = canonicalBox5_115 := by decide

theorem canonicalDecode5_115 : canonicalBox5_115.toKeyData 19200 = keys5Chunk3.get ⟨19, by decide⟩ := by
  change canonicalBox5_115.toKeyData 19200 = ⟨![(7 / 20), (31 / 20), 2, (8 / 5), (3 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(277 / 800), (373 / 240), (481 / 240), (2053 / 1280), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_115, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_115, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_115, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_115 : keySolid (keys5Chunk3.get ⟨19, by decide⟩) = canonicalPose5_115.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_115 (box := canonicalBox5_115) (k := keys5Chunk3.get ⟨19, by decide⟩) (canonicalMatch5_115) (canonicalDecode5_115)

def canonicalPose5_116 : Pose 5 :=
  ⟨canonicalPerm5_5, ![true, false, true, false, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_116 : BoxKey 5 :=
  ⟨![7680, 31680, 38400, 32640, 8640], ![300, 360, 0, 420, 240], ![7605, 31752, 38320, 32710, 8560], false⟩

theorem canonicalMatch5_116 :
    canonicalPose5_116.boxKey 19200 (referenceBox5 (!canonicalBox5_116.bump)) = canonicalBox5_116 := by decide

theorem canonicalDecode5_116 : canonicalBox5_116.toKeyData 19200 = keys5Chunk3.get ⟨20, by decide⟩ := by
  change canonicalBox5_116.toKeyData 19200 = ⟨![(2 / 5), (33 / 20), 2, (17 / 10), (9 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(507 / 1280), (1323 / 800), (479 / 240), (3271 / 1920), (107 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_116, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_116, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_116, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_116 : keySolid (keys5Chunk3.get ⟨20, by decide⟩) = canonicalPose5_116.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_116 (box := canonicalBox5_116) (k := keys5Chunk3.get ⟨20, by decide⟩) (canonicalMatch5_116) (canonicalDecode5_116)

def canonicalPose5_117 : Pose 5 :=
  ⟨canonicalPerm5_2, ![true, false, true, false, true], ![1, 1, 2, 1, 1]⟩
def canonicalBox5_117 : BoxKey 5 :=
  ⟨![8640, 32640, 38400, 31680, 7680], ![240, 420, 0, 360, 300], ![8560, 32710, 38320, 31752, 7605], false⟩

theorem canonicalMatch5_117 :
    canonicalPose5_117.boxKey 19200 (referenceBox5 (!canonicalBox5_117.bump)) = canonicalBox5_117 := by decide

theorem canonicalDecode5_117 : canonicalBox5_117.toKeyData 19200 = keys5Chunk3.get ⟨21, by decide⟩ := by
  change canonicalBox5_117.toKeyData 19200 = ⟨![(9 / 20), (17 / 10), 2, (33 / 20), (2 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(107 / 240), (3271 / 1920), (479 / 240), (1323 / 800), (507 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_117, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_117, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_117, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_117 : keySolid (keys5Chunk3.get ⟨21, by decide⟩) = canonicalPose5_117.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_117 (box := canonicalBox5_117) (k := keys5Chunk3.get ⟨21, by decide⟩) (canonicalMatch5_117) (canonicalDecode5_117)

def canonicalPose5_118 : Pose 5 :=
  ⟨canonicalPerm5_0, ![true, true, true, true, true], ![1, 2, 2, 2, 1]⟩
def canonicalBox5_118 : BoxKey 5 :=
  ⟨![8640, 26880, 25920, 38400, 5760], ![240, 300, 360, 0, 420], ![8560, 26805, 25848, 38320, 5690], false⟩

theorem canonicalMatch5_118 :
    canonicalPose5_118.boxKey 19200 (referenceBox5 (!canonicalBox5_118.bump)) = canonicalBox5_118 := by decide

theorem canonicalDecode5_118 : canonicalBox5_118.toKeyData 19200 = keys5Chunk3.get ⟨22, by decide⟩ := by
  change canonicalBox5_118.toKeyData 19200 = ⟨![(9 / 20), (7 / 5), (27 / 20), 2, (3 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(107 / 240), (1787 / 1280), (1077 / 800), (479 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_118, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_118, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_118, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_118 : keySolid (keys5Chunk3.get ⟨22, by decide⟩) = canonicalPose5_118.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_118 (box := canonicalBox5_118) (k := keys5Chunk3.get ⟨22, by decide⟩) (canonicalMatch5_118) (canonicalDecode5_118)

def canonicalPose5_119 : Pose 5 :=
  ⟨canonicalPerm5_6, ![false, false, true, false, true], ![0, 1, 2, 1, 0]⟩
def canonicalBox5_119 : BoxKey 5 :=
  ⟨![11520, 32640, 25920, 29760, 0], ![300, 420, 360, 240, 0], ![11595, 32710, 25848, 29840, -80], true⟩

theorem canonicalMatch5_119 :
    canonicalPose5_119.boxKey 19200 (referenceBox5 (!canonicalBox5_119.bump)) = canonicalBox5_119 := by decide

theorem canonicalDecode5_119 : canonicalBox5_119.toKeyData 19200 = keys5Chunk3.get ⟨23, by decide⟩ := by
  change canonicalBox5_119.toKeyData 19200 = ⟨![(3 / 5), (17 / 10), (27 / 20), (31 / 20), 0], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(773 / 1280), (3271 / 1920), (1077 / 800), (373 / 240), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_119, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_119, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_119, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_119 : keySolid (keys5Chunk3.get ⟨23, by decide⟩) = canonicalPose5_119.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_119 (box := canonicalBox5_119) (k := keys5Chunk3.get ⟨23, by decide⟩) (canonicalMatch5_119) (canonicalDecode5_119)

def canonicalPose5_120 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, false, false, false, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_120 : BoxKey 5 :=
  ⟨![0, 29760, 31680, 32640, 30720], ![0, 240, 360, 420, 300], ![80, 29840, 31752, 32710, 30795], false⟩

theorem canonicalMatch5_120 :
    canonicalPose5_120.boxKey 19200 (referenceBox5 (!canonicalBox5_120.bump)) = canonicalBox5_120 := by decide

theorem canonicalDecode5_120 : canonicalBox5_120.toKeyData 19200 = keys5Chunk3.get ⟨24, by decide⟩ := by
  change canonicalBox5_120.toKeyData 19200 = ⟨![0, (31 / 20), (33 / 20), (17 / 10), (8 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(1 / 240), (373 / 240), (1323 / 800), (3271 / 1920), (2053 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_120, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_120, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_120, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_120 : keySolid (keys5Chunk3.get ⟨24, by decide⟩) = canonicalPose5_120.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_120 (box := canonicalBox5_120) (k := keys5Chunk3.get ⟨24, by decide⟩) (canonicalMatch5_120) (canonicalDecode5_120)

def canonicalPose5_121 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, false, false, false, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_121 : BoxKey 5 :=
  ⟨![0, 30720, 32640, 31680, 29760], ![0, 300, 420, 360, 240], ![80, 30795, 32710, 31752, 29840], false⟩

theorem canonicalMatch5_121 :
    canonicalPose5_121.boxKey 19200 (referenceBox5 (!canonicalBox5_121.bump)) = canonicalBox5_121 := by decide

theorem canonicalDecode5_121 : canonicalBox5_121.toKeyData 19200 = keys5Chunk3.get ⟨25, by decide⟩ := by
  change canonicalBox5_121.toKeyData 19200 = ⟨![0, (8 / 5), (17 / 10), (33 / 20), (31 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(1 / 240), (2053 / 1280), (3271 / 1920), (1323 / 800), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_121, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_121, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_121, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_121 : keySolid (keys5Chunk3.get ⟨25, by decide⟩) = canonicalPose5_121.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_121 (box := canonicalBox5_121) (k := keys5Chunk3.get ⟨25, by decide⟩) (canonicalMatch5_121) (canonicalDecode5_121)

def canonicalPose5_122 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, false, false, false, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_122 : BoxKey 5 :=
  ⟨![0, 31680, 30720, 29760, 32640], ![0, 360, 300, 240, 420], ![-80, 31752, 30795, 29840, 32710], true⟩

theorem canonicalMatch5_122 :
    canonicalPose5_122.boxKey 19200 (referenceBox5 (!canonicalBox5_122.bump)) = canonicalBox5_122 := by decide

theorem canonicalDecode5_122 : canonicalBox5_122.toKeyData 19200 = keys5Chunk3.get ⟨26, by decide⟩ := by
  change canonicalBox5_122.toKeyData 19200 = ⟨![0, (33 / 20), (8 / 5), (31 / 20), (17 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(-1 / 240), (1323 / 800), (2053 / 1280), (373 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_122, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_122, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_122, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_122 : keySolid (keys5Chunk3.get ⟨26, by decide⟩) = canonicalPose5_122.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_122 (box := canonicalBox5_122) (k := keys5Chunk3.get ⟨26, by decide⟩) (canonicalMatch5_122) (canonicalDecode5_122)

def canonicalPose5_123 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, false, false, false, false], ![0, 1, 1, 1, 1]⟩
def canonicalBox5_123 : BoxKey 5 :=
  ⟨![0, 32640, 29760, 30720, 31680], ![0, 420, 240, 300, 360], ![-80, 32710, 29840, 30795, 31752], true⟩

theorem canonicalMatch5_123 :
    canonicalPose5_123.boxKey 19200 (referenceBox5 (!canonicalBox5_123.bump)) = canonicalBox5_123 := by decide

theorem canonicalDecode5_123 : canonicalBox5_123.toKeyData 19200 = keys5Chunk3.get ⟨27, by decide⟩ := by
  change canonicalBox5_123.toKeyData 19200 = ⟨![0, (17 / 10), (31 / 20), (8 / 5), (33 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(-1 / 240), (3271 / 1920), (373 / 240), (2053 / 1280), (1323 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_123, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_123, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_123, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_123 : keySolid (keys5Chunk3.get ⟨27, by decide⟩) = canonicalPose5_123.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_123 (box := canonicalBox5_123) (k := keys5Chunk3.get ⟨27, by decide⟩) (canonicalMatch5_123) (canonicalDecode5_123)

def canonicalPose5_124 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, true, true, true, true], ![1, 2, 2, 2, 2]⟩
def canonicalBox5_124 : BoxKey 5 :=
  ⟨![19200, 24960, 27840, 26880, 25920], ![0, 420, 240, 300, 360], ![19120, 24890, 27760, 26805, 25848], false⟩

theorem canonicalMatch5_124 :
    canonicalPose5_124.boxKey 19200 (referenceBox5 (!canonicalBox5_124.bump)) = canonicalBox5_124 := by decide

theorem canonicalDecode5_124 : canonicalBox5_124.toKeyData 19200 = keys5Chunk3.get ⟨28, by decide⟩ := by
  change canonicalBox5_124.toKeyData 19200 = ⟨![1, (13 / 10), (29 / 20), (7 / 5), (27 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(239 / 240), (2489 / 1920), (347 / 240), (1787 / 1280), (1077 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_124, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_124, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_124, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_124 : keySolid (keys5Chunk3.get ⟨28, by decide⟩) = canonicalPose5_124.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_124 (box := canonicalBox5_124) (k := keys5Chunk3.get ⟨28, by decide⟩) (canonicalMatch5_124) (canonicalDecode5_124)

def canonicalPose5_125 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, true, true, true, true], ![1, 2, 2, 2, 2]⟩
def canonicalBox5_125 : BoxKey 5 :=
  ⟨![19200, 25920, 26880, 27840, 24960], ![0, 360, 300, 240, 420], ![19120, 25848, 26805, 27760, 24890], false⟩

theorem canonicalMatch5_125 :
    canonicalPose5_125.boxKey 19200 (referenceBox5 (!canonicalBox5_125.bump)) = canonicalBox5_125 := by decide

theorem canonicalDecode5_125 : canonicalBox5_125.toKeyData 19200 = keys5Chunk3.get ⟨29, by decide⟩ := by
  change canonicalBox5_125.toKeyData 19200 = ⟨![1, (27 / 20), (7 / 5), (29 / 20), (13 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(239 / 240), (1077 / 800), (1787 / 1280), (347 / 240), (2489 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_125, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_125, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_125, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_125 : keySolid (keys5Chunk3.get ⟨29, by decide⟩) = canonicalPose5_125.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_125 (box := canonicalBox5_125) (k := keys5Chunk3.get ⟨29, by decide⟩) (canonicalMatch5_125) (canonicalDecode5_125)

def canonicalPose5_126 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, true, true, true, true], ![1, 2, 2, 2, 2]⟩
def canonicalBox5_126 : BoxKey 5 :=
  ⟨![19200, 26880, 24960, 25920, 27840], ![0, 300, 420, 360, 240], ![19280, 26805, 24890, 25848, 27760], true⟩

theorem canonicalMatch5_126 :
    canonicalPose5_126.boxKey 19200 (referenceBox5 (!canonicalBox5_126.bump)) = canonicalBox5_126 := by decide

theorem canonicalDecode5_126 : canonicalBox5_126.toKeyData 19200 = keys5Chunk3.get ⟨30, by decide⟩ := by
  change canonicalBox5_126.toKeyData 19200 = ⟨![1, (7 / 5), (13 / 10), (27 / 20), (29 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(241 / 240), (1787 / 1280), (2489 / 1920), (1077 / 800), (347 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_126, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_126, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_126, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_126 : keySolid (keys5Chunk3.get ⟨30, by decide⟩) = canonicalPose5_126.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_126 (box := canonicalBox5_126) (k := keys5Chunk3.get ⟨30, by decide⟩) (canonicalMatch5_126) (canonicalDecode5_126)

def canonicalPose5_127 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, true, true, true, true], ![1, 2, 2, 2, 2]⟩
def canonicalBox5_127 : BoxKey 5 :=
  ⟨![19200, 27840, 25920, 24960, 26880], ![0, 240, 360, 420, 300], ![19280, 27760, 25848, 24890, 26805], true⟩

theorem canonicalMatch5_127 :
    canonicalPose5_127.boxKey 19200 (referenceBox5 (!canonicalBox5_127.bump)) = canonicalBox5_127 := by decide

theorem canonicalDecode5_127 : canonicalBox5_127.toKeyData 19200 = keys5Chunk3.get ⟨31, by decide⟩ := by
  change canonicalBox5_127.toKeyData 19200 = ⟨![1, (29 / 20), (27 / 20), (13 / 10), (7 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(241 / 240), (347 / 240), (1077 / 800), (2489 / 1920), (1787 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_127, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_127, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_127, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_127 : keySolid (keys5Chunk3.get ⟨31, by decide⟩) = canonicalPose5_127.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_127 (box := canonicalBox5_127) (k := keys5Chunk3.get ⟨31, by decide⟩) (canonicalMatch5_127) (canonicalDecode5_127)

theorem keys5Chunk3_canonical : ∀ k ∈ keys5Chunk3,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk3, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_96, canonicalSolid5_96⟩
  · exact ⟨canonicalPose5_97, canonicalSolid5_97⟩
  · exact ⟨canonicalPose5_98, canonicalSolid5_98⟩
  · exact ⟨canonicalPose5_99, canonicalSolid5_99⟩
  · exact ⟨canonicalPose5_100, canonicalSolid5_100⟩
  · exact ⟨canonicalPose5_101, canonicalSolid5_101⟩
  · exact ⟨canonicalPose5_102, canonicalSolid5_102⟩
  · exact ⟨canonicalPose5_103, canonicalSolid5_103⟩
  · exact ⟨canonicalPose5_104, canonicalSolid5_104⟩
  · exact ⟨canonicalPose5_105, canonicalSolid5_105⟩
  · exact ⟨canonicalPose5_106, canonicalSolid5_106⟩
  · exact ⟨canonicalPose5_107, canonicalSolid5_107⟩
  · exact ⟨canonicalPose5_108, canonicalSolid5_108⟩
  · exact ⟨canonicalPose5_109, canonicalSolid5_109⟩
  · exact ⟨canonicalPose5_110, canonicalSolid5_110⟩
  · exact ⟨canonicalPose5_111, canonicalSolid5_111⟩
  · exact ⟨canonicalPose5_112, canonicalSolid5_112⟩
  · exact ⟨canonicalPose5_113, canonicalSolid5_113⟩
  · exact ⟨canonicalPose5_114, canonicalSolid5_114⟩
  · exact ⟨canonicalPose5_115, canonicalSolid5_115⟩
  · exact ⟨canonicalPose5_116, canonicalSolid5_116⟩
  · exact ⟨canonicalPose5_117, canonicalSolid5_117⟩
  · exact ⟨canonicalPose5_118, canonicalSolid5_118⟩
  · exact ⟨canonicalPose5_119, canonicalSolid5_119⟩
  · exact ⟨canonicalPose5_120, canonicalSolid5_120⟩
  · exact ⟨canonicalPose5_121, canonicalSolid5_121⟩
  · exact ⟨canonicalPose5_122, canonicalSolid5_122⟩
  · exact ⟨canonicalPose5_123, canonicalSolid5_123⟩
  · exact ⟨canonicalPose5_124, canonicalSolid5_124⟩
  · exact ⟨canonicalPose5_125, canonicalSolid5_125⟩
  · exact ⟨canonicalPose5_126, canonicalSolid5_126⟩
  · exact ⟨canonicalPose5_127, canonicalSolid5_127⟩

#print axioms keys5Chunk3_canonical

end SparseMonotiles.Canonical
