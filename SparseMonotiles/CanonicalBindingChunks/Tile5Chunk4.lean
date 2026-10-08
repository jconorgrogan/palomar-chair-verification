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

def canonicalPose5_128 : Pose 5 :=
  ⟨canonicalPerm5_11, ![false, false, false, false, true], ![0, 2, 1, 1, 2]⟩
def canonicalBox5_128 : BoxKey 5 :=
  ⟨![12480, 38400, 32640, 29760, 26880], ![360, 0, 420, 240, 300], ![12552, 38480, 32710, 29840, 26805], true⟩

theorem canonicalMatch5_128 :
    canonicalPose5_128.boxKey 19200 (referenceBox5 (!canonicalBox5_128.bump)) = canonicalBox5_128 := by decide

theorem canonicalDecode5_128 : canonicalBox5_128.toKeyData 19200 = keys5Chunk4.get ⟨0, by decide⟩ := by
  change canonicalBox5_128.toKeyData 19200 = ⟨![(13 / 20), 2, (17 / 10), (31 / 20), (7 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(523 / 800), (481 / 240), (3271 / 1920), (373 / 240), (1787 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_128, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_128, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_128, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_128 : keySolid (keys5Chunk4.get ⟨0, by decide⟩) = canonicalPose5_128.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_128 (box := canonicalBox5_128) (k := keys5Chunk4.get ⟨0, by decide⟩) (canonicalMatch5_128) (canonicalDecode5_128)

def canonicalPose5_129 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, false, true, true, false], ![0, 1, 2, 2, 1]⟩
def canonicalBox5_129 : BoxKey 5 :=
  ⟨![12480, 29760, 38400, 26880, 32640], ![360, 240, 0, 300, 420], ![12552, 29840, 38320, 26805, 32710], false⟩

theorem canonicalMatch5_129 :
    canonicalPose5_129.boxKey 19200 (referenceBox5 (!canonicalBox5_129.bump)) = canonicalBox5_129 := by decide

theorem canonicalDecode5_129 : canonicalBox5_129.toKeyData 19200 = keys5Chunk4.get ⟨1, by decide⟩ := by
  change canonicalBox5_129.toKeyData 19200 = ⟨![(13 / 20), (31 / 20), 2, (7 / 5), (17 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(523 / 800), (373 / 240), (479 / 240), (1787 / 1280), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_129, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_129, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_129, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_129 : keySolid (keys5Chunk4.get ⟨1, by decide⟩) = canonicalPose5_129.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_129 (box := canonicalBox5_129) (k := keys5Chunk4.get ⟨1, by decide⟩) (canonicalMatch5_129) (canonicalDecode5_129)

def canonicalPose5_130 : Pose 5 :=
  ⟨canonicalPerm5_10, ![false, false, true, true, false], ![0, 1, 2, 2, 1]⟩
def canonicalBox5_130 : BoxKey 5 :=
  ⟨![12480, 32640, 26880, 38400, 29760], ![360, 420, 300, 0, 240], ![12552, 32710, 26805, 38320, 29840], false⟩

theorem canonicalMatch5_130 :
    canonicalPose5_130.boxKey 19200 (referenceBox5 (!canonicalBox5_130.bump)) = canonicalBox5_130 := by decide

theorem canonicalDecode5_130 : canonicalBox5_130.toKeyData 19200 = keys5Chunk4.get ⟨2, by decide⟩ := by
  change canonicalBox5_130.toKeyData 19200 = ⟨![(13 / 20), (17 / 10), (7 / 5), 2, (31 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(523 / 800), (3271 / 1920), (1787 / 1280), (479 / 240), (373 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_130, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_130, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_130, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_130 : keySolid (keys5Chunk4.get ⟨2, by decide⟩) = canonicalPose5_130.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_130 (box := canonicalBox5_130) (k := keys5Chunk4.get ⟨2, by decide⟩) (canonicalMatch5_130) (canonicalDecode5_130)

def canonicalPose5_131 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, true, false, false, false], ![0, 2, 1, 1, 2]⟩
def canonicalBox5_131 : BoxKey 5 :=
  ⟨![12480, 26880, 29760, 32640, 38400], ![360, 300, 240, 420, 0], ![12552, 26805, 29840, 32710, 38480], true⟩

theorem canonicalMatch5_131 :
    canonicalPose5_131.boxKey 19200 (referenceBox5 (!canonicalBox5_131.bump)) = canonicalBox5_131 := by decide

theorem canonicalDecode5_131 : canonicalBox5_131.toKeyData 19200 = keys5Chunk4.get ⟨3, by decide⟩ := by
  change canonicalBox5_131.toKeyData 19200 = ⟨![(13 / 20), (7 / 5), (31 / 20), (17 / 10), 2], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(523 / 800), (1787 / 1280), (373 / 240), (3271 / 1920), (481 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_131, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_131, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_131, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_131 : keySolid (keys5Chunk4.get ⟨3, by decide⟩) = canonicalPose5_131.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_131 (box := canonicalBox5_131) (k := keys5Chunk4.get ⟨3, by decide⟩) (canonicalMatch5_131) (canonicalDecode5_131)

def canonicalPose5_132 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, true, true, true, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_132 : BoxKey 5 :=
  ⟨![38400, 5760, 8640, 7680, 6720], ![0, 420, 240, 300, 360], ![38320, 5690, 8560, 7605, 6648], false⟩

theorem canonicalMatch5_132 :
    canonicalPose5_132.boxKey 19200 (referenceBox5 (!canonicalBox5_132.bump)) = canonicalBox5_132 := by decide

theorem canonicalDecode5_132 : canonicalBox5_132.toKeyData 19200 = keys5Chunk4.get ⟨4, by decide⟩ := by
  change canonicalBox5_132.toKeyData 19200 = ⟨![2, (3 / 10), (9 / 20), (2 / 5), (7 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(479 / 240), (569 / 1920), (107 / 240), (507 / 1280), (277 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_132, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_132, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_132, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_132 : keySolid (keys5Chunk4.get ⟨4, by decide⟩) = canonicalPose5_132.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_132 (box := canonicalBox5_132) (k := keys5Chunk4.get ⟨4, by decide⟩) (canonicalMatch5_132) (canonicalDecode5_132)

def canonicalPose5_133 : Pose 5 :=
  ⟨canonicalPerm5_18, ![true, true, true, true, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_133 : BoxKey 5 :=
  ⟨![38400, 6720, 7680, 8640, 5760], ![0, 360, 300, 240, 420], ![38320, 6648, 7605, 8560, 5690], false⟩

theorem canonicalMatch5_133 :
    canonicalPose5_133.boxKey 19200 (referenceBox5 (!canonicalBox5_133.bump)) = canonicalBox5_133 := by decide

theorem canonicalDecode5_133 : canonicalBox5_133.toKeyData 19200 = keys5Chunk4.get ⟨5, by decide⟩ := by
  change canonicalBox5_133.toKeyData 19200 = ⟨![2, (7 / 20), (2 / 5), (9 / 20), (3 / 10)], ![0, (3 / 160), (1 / 64), (1 / 80), (7 / 320)], ![(479 / 240), (277 / 800), (507 / 1280), (107 / 240), (569 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_133, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_133, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_133, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_133 : keySolid (keys5Chunk4.get ⟨5, by decide⟩) = canonicalPose5_133.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_133 (box := canonicalBox5_133) (k := keys5Chunk4.get ⟨5, by decide⟩) (canonicalMatch5_133) (canonicalDecode5_133)

def canonicalPose5_134 : Pose 5 :=
  ⟨canonicalPerm5_17, ![false, true, true, true, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_134 : BoxKey 5 :=
  ⟨![38400, 7680, 5760, 6720, 8640], ![0, 300, 420, 360, 240], ![38480, 7605, 5690, 6648, 8560], true⟩

theorem canonicalMatch5_134 :
    canonicalPose5_134.boxKey 19200 (referenceBox5 (!canonicalBox5_134.bump)) = canonicalBox5_134 := by decide

theorem canonicalDecode5_134 : canonicalBox5_134.toKeyData 19200 = keys5Chunk4.get ⟨6, by decide⟩ := by
  change canonicalBox5_134.toKeyData 19200 = ⟨![2, (2 / 5), (3 / 10), (7 / 20), (9 / 20)], ![0, (1 / 64), (7 / 320), (3 / 160), (1 / 80)], ![(481 / 240), (507 / 1280), (569 / 1920), (277 / 800), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_134, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_134, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_134, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_134 : keySolid (keys5Chunk4.get ⟨6, by decide⟩) = canonicalPose5_134.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_134 (box := canonicalBox5_134) (k := keys5Chunk4.get ⟨6, by decide⟩) (canonicalMatch5_134) (canonicalDecode5_134)

def canonicalPose5_135 : Pose 5 :=
  ⟨canonicalPerm5_16, ![false, true, true, true, true], ![2, 1, 1, 1, 1]⟩
def canonicalBox5_135 : BoxKey 5 :=
  ⟨![38400, 8640, 6720, 5760, 7680], ![0, 240, 360, 420, 300], ![38480, 8560, 6648, 5690, 7605], true⟩

theorem canonicalMatch5_135 :
    canonicalPose5_135.boxKey 19200 (referenceBox5 (!canonicalBox5_135.bump)) = canonicalBox5_135 := by decide

theorem canonicalDecode5_135 : canonicalBox5_135.toKeyData 19200 = keys5Chunk4.get ⟨7, by decide⟩ := by
  change canonicalBox5_135.toKeyData 19200 = ⟨![2, (9 / 20), (7 / 20), (3 / 10), (2 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(481 / 240), (107 / 240), (277 / 800), (569 / 1920), (507 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_135, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_135, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_135, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_135 : keySolid (keys5Chunk4.get ⟨7, by decide⟩) = canonicalPose5_135.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_135 (box := canonicalBox5_135) (k := keys5Chunk4.get ⟨7, by decide⟩) (canonicalMatch5_135) (canonicalDecode5_135)

def canonicalPose5_136 : Pose 5 :=
  ⟨canonicalPerm5_11, ![true, false, true, true, false], ![2, 0, 1, 1, 0]⟩
def canonicalBox5_136 : BoxKey 5 :=
  ⟨![25920, 0, 5760, 8640, 11520], ![360, 0, 420, 240, 300], ![25848, 80, 5690, 8560, 11595], false⟩

theorem canonicalMatch5_136 :
    canonicalPose5_136.boxKey 19200 (referenceBox5 (!canonicalBox5_136.bump)) = canonicalBox5_136 := by decide

theorem canonicalDecode5_136 : canonicalBox5_136.toKeyData 19200 = keys5Chunk4.get ⟨8, by decide⟩ := by
  change canonicalBox5_136.toKeyData 19200 = ⟨![(27 / 20), 0, (3 / 10), (9 / 20), (3 / 5)], ![(3 / 160), 0, (7 / 320), (1 / 80), (1 / 64)], ![(1077 / 800), (1 / 240), (569 / 1920), (107 / 240), (773 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_136, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_136, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_136, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_136 : keySolid (keys5Chunk4.get ⟨8, by decide⟩) = canonicalPose5_136.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_136 (box := canonicalBox5_136) (k := keys5Chunk4.get ⟨8, by decide⟩) (canonicalMatch5_136) (canonicalDecode5_136)

def canonicalPose5_137 : Pose 5 :=
  ⟨canonicalPerm5_8, ![true, true, true, false, true], ![2, 1, 0, 0, 1]⟩
def canonicalBox5_137 : BoxKey 5 :=
  ⟨![25920, 8640, 0, 11520, 5760], ![360, 240, 0, 300, 420], ![25848, 8560, -80, 11595, 5690], true⟩

theorem canonicalMatch5_137 :
    canonicalPose5_137.boxKey 19200 (referenceBox5 (!canonicalBox5_137.bump)) = canonicalBox5_137 := by decide

theorem canonicalDecode5_137 : canonicalBox5_137.toKeyData 19200 = keys5Chunk4.get ⟨9, by decide⟩ := by
  change canonicalBox5_137.toKeyData 19200 = ⟨![(27 / 20), (9 / 20), 0, (3 / 5), (3 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(1077 / 800), (107 / 240), (-1 / 240), (773 / 1280), (569 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_137, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_137, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_137, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_137 : keySolid (keys5Chunk4.get ⟨9, by decide⟩) = canonicalPose5_137.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_137 (box := canonicalBox5_137) (k := keys5Chunk4.get ⟨9, by decide⟩) (canonicalMatch5_137) (canonicalDecode5_137)

def canonicalPose5_138 : Pose 5 :=
  ⟨canonicalPerm5_10, ![true, true, false, true, true], ![2, 1, 0, 0, 1]⟩
def canonicalBox5_138 : BoxKey 5 :=
  ⟨![25920, 5760, 11520, 0, 8640], ![360, 420, 300, 0, 240], ![25848, 5690, 11595, -80, 8560], true⟩

theorem canonicalMatch5_138 :
    canonicalPose5_138.boxKey 19200 (referenceBox5 (!canonicalBox5_138.bump)) = canonicalBox5_138 := by decide

theorem canonicalDecode5_138 : canonicalBox5_138.toKeyData 19200 = keys5Chunk4.get ⟨10, by decide⟩ := by
  change canonicalBox5_138.toKeyData 19200 = ⟨![(27 / 20), (3 / 10), (3 / 5), 0, (9 / 20)], ![(3 / 160), (7 / 320), (1 / 64), 0, (1 / 80)], ![(1077 / 800), (569 / 1920), (773 / 1280), (-1 / 240), (107 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_138, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_138, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_138, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_138 : keySolid (keys5Chunk4.get ⟨10, by decide⟩) = canonicalPose5_138.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_138 (box := canonicalBox5_138) (k := keys5Chunk4.get ⟨10, by decide⟩) (canonicalMatch5_138) (canonicalDecode5_138)

def canonicalPose5_139 : Pose 5 :=
  ⟨canonicalPerm5_9, ![true, false, true, true, false], ![2, 0, 1, 1, 0]⟩
def canonicalBox5_139 : BoxKey 5 :=
  ⟨![25920, 11520, 8640, 5760, 0], ![360, 300, 240, 420, 0], ![25848, 11595, 8560, 5690, 80], false⟩

theorem canonicalMatch5_139 :
    canonicalPose5_139.boxKey 19200 (referenceBox5 (!canonicalBox5_139.bump)) = canonicalBox5_139 := by decide

theorem canonicalDecode5_139 : canonicalBox5_139.toKeyData 19200 = keys5Chunk4.get ⟨11, by decide⟩ := by
  change canonicalBox5_139.toKeyData 19200 = ⟨![(27 / 20), (3 / 5), (9 / 20), (3 / 10), 0], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(1077 / 800), (773 / 1280), (107 / 240), (569 / 1920), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_139, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_139, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_139, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_139 : keySolid (keys5Chunk4.get ⟨11, by decide⟩) = canonicalPose5_139.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_139 (box := canonicalBox5_139) (k := keys5Chunk4.get ⟨11, by decide⟩) (canonicalMatch5_139) (canonicalDecode5_139)

def canonicalPose5_140 : Pose 5 :=
  ⟨canonicalPerm5_16, ![true, true, false, true, true], ![2, 1, 0, 1, 2]⟩
def canonicalBox5_140 : BoxKey 5 :=
  ⟨![38400, 8640, 12480, 5760, 26880], ![0, 240, 360, 420, 300], ![38320, 8560, 12552, 5690, 26805], false⟩

theorem canonicalMatch5_140 :
    canonicalPose5_140.boxKey 19200 (referenceBox5 (!canonicalBox5_140.bump)) = canonicalBox5_140 := by decide

theorem canonicalDecode5_140 : canonicalBox5_140.toKeyData 19200 = keys5Chunk4.get ⟨12, by decide⟩ := by
  change canonicalBox5_140.toKeyData 19200 = ⟨![2, (9 / 20), (13 / 20), (3 / 10), (7 / 5)], ![0, (1 / 80), (3 / 160), (7 / 320), (1 / 64)], ![(479 / 240), (107 / 240), (523 / 800), (569 / 1920), (1787 / 1280)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_140, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_140, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_140, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_140 : keySolid (keys5Chunk4.get ⟨12, by decide⟩) = canonicalPose5_140.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_140 (box := canonicalBox5_140) (k := keys5Chunk4.get ⟨12, by decide⟩) (canonicalMatch5_140) (canonicalDecode5_140)

def canonicalPose5_141 : Pose 5 :=
  ⟨canonicalPerm5_15, ![false, true, false, false, false], ![1, 0, 0, 0, 1]⟩
def canonicalBox5_141 : BoxKey 5 :=
  ⟨![32640, 0, 12480, 11520, 29760], ![420, 0, 360, 300, 240], ![32710, -80, 12552, 11595, 29840], true⟩

theorem canonicalMatch5_141 :
    canonicalPose5_141.boxKey 19200 (referenceBox5 (!canonicalBox5_141.bump)) = canonicalBox5_141 := by decide

theorem canonicalDecode5_141 : canonicalBox5_141.toKeyData 19200 = keys5Chunk4.get ⟨13, by decide⟩ := by
  change canonicalBox5_141.toKeyData 19200 = ⟨![(17 / 10), 0, (13 / 20), (3 / 5), (31 / 20)], ![(7 / 320), 0, (3 / 160), (1 / 64), (1 / 80)], ![(3271 / 1920), (-1 / 240), (523 / 800), (773 / 1280), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_141, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_141, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_141, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_141 : keySolid (keys5Chunk4.get ⟨13, by decide⟩) = canonicalPose5_141.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_141 (box := canonicalBox5_141) (k := keys5Chunk4.get ⟨13, by decide⟩) (canonicalMatch5_141) (canonicalDecode5_141)

def canonicalPose5_142 : Pose 5 :=
  ⟨canonicalPerm5_2, ![false, true, true, true, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_142 : BoxKey 5 :=
  ⟨![29760, 5760, 0, 6720, 30720], ![240, 420, 0, 360, 300], ![29840, 5690, -80, 6648, 30795], true⟩

theorem canonicalMatch5_142 :
    canonicalPose5_142.boxKey 19200 (referenceBox5 (!canonicalBox5_142.bump)) = canonicalBox5_142 := by decide

theorem canonicalDecode5_142 : canonicalBox5_142.toKeyData 19200 = keys5Chunk4.get ⟨14, by decide⟩ := by
  change canonicalBox5_142.toKeyData 19200 = ⟨![(31 / 20), (3 / 10), 0, (7 / 20), (8 / 5)], ![(1 / 80), (7 / 320), 0, (3 / 160), (1 / 64)], ![(373 / 240), (569 / 1920), (-1 / 240), (277 / 800), (2053 / 1280)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_142, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_142, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_142, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_142 : keySolid (keys5Chunk4.get ⟨14, by decide⟩) = canonicalPose5_142.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_142 (box := canonicalBox5_142) (k := keys5Chunk4.get ⟨14, by decide⟩) (canonicalMatch5_142) (canonicalDecode5_142)

def canonicalPose5_143 : Pose 5 :=
  ⟨canonicalPerm5_5, ![false, true, true, true, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_143 : BoxKey 5 :=
  ⟨![30720, 6720, 0, 5760, 29760], ![300, 360, 0, 420, 240], ![30795, 6648, -80, 5690, 29840], true⟩

theorem canonicalMatch5_143 :
    canonicalPose5_143.boxKey 19200 (referenceBox5 (!canonicalBox5_143.bump)) = canonicalBox5_143 := by decide

theorem canonicalDecode5_143 : canonicalBox5_143.toKeyData 19200 = keys5Chunk4.get ⟨15, by decide⟩ := by
  change canonicalBox5_143.toKeyData 19200 = ⟨![(8 / 5), (7 / 20), 0, (3 / 10), (31 / 20)], ![(1 / 64), (3 / 160), 0, (7 / 320), (1 / 80)], ![(2053 / 1280), (277 / 800), (-1 / 240), (569 / 1920), (373 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_143, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_143, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_143, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_143 : keySolid (keys5Chunk4.get ⟨15, by decide⟩) = canonicalPose5_143.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_143 (box := canonicalBox5_143) (k := keys5Chunk4.get ⟨15, by decide⟩) (canonicalMatch5_143) (canonicalDecode5_143)

def canonicalPose5_144 : Pose 5 :=
  ⟨canonicalPerm5_8, ![false, true, false, true, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_144 : BoxKey 5 :=
  ⟨![31680, 8640, 0, 7680, 32640], ![360, 240, 0, 300, 420], ![31752, 8560, 80, 7605, 32710], false⟩

theorem canonicalMatch5_144 :
    canonicalPose5_144.boxKey 19200 (referenceBox5 (!canonicalBox5_144.bump)) = canonicalBox5_144 := by decide

theorem canonicalDecode5_144 : canonicalBox5_144.toKeyData 19200 = keys5Chunk4.get ⟨16, by decide⟩ := by
  change canonicalBox5_144.toKeyData 19200 = ⟨![(33 / 20), (9 / 20), 0, (2 / 5), (17 / 10)], ![(3 / 160), (1 / 80), 0, (1 / 64), (7 / 320)], ![(1323 / 800), (107 / 240), (1 / 240), (507 / 1280), (3271 / 1920)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_144, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_144, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_144, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_144 : keySolid (keys5Chunk4.get ⟨16, by decide⟩) = canonicalPose5_144.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_144 (box := canonicalBox5_144) (k := keys5Chunk4.get ⟨16, by decide⟩) (canonicalMatch5_144) (canonicalDecode5_144)

def canonicalPose5_145 : Pose 5 :=
  ⟨canonicalPerm5_13, ![false, true, false, true, false], ![1, 1, 0, 1, 1]⟩
def canonicalBox5_145 : BoxKey 5 :=
  ⟨![32640, 7680, 0, 8640, 31680], ![420, 300, 0, 240, 360], ![32710, 7605, 80, 8560, 31752], false⟩

theorem canonicalMatch5_145 :
    canonicalPose5_145.boxKey 19200 (referenceBox5 (!canonicalBox5_145.bump)) = canonicalBox5_145 := by decide

theorem canonicalDecode5_145 : canonicalBox5_145.toKeyData 19200 = keys5Chunk4.get ⟨17, by decide⟩ := by
  change canonicalBox5_145.toKeyData 19200 = ⟨![(17 / 10), (2 / 5), 0, (9 / 20), (33 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(3271 / 1920), (507 / 1280), (1 / 240), (107 / 240), (1323 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_145, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_145, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_145, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_145 : keySolid (keys5Chunk4.get ⟨17, by decide⟩) = canonicalPose5_145.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_145 (box := canonicalBox5_145) (k := keys5Chunk4.get ⟨17, by decide⟩) (canonicalMatch5_145) (canonicalDecode5_145)

def canonicalPose5_146 : Pose 5 :=
  ⟨canonicalPerm5_0, ![false, false, false, true, false], ![1, 0, 0, 0, 1]⟩
def canonicalBox5_146 : BoxKey 5 :=
  ⟨![29760, 11520, 12480, 0, 32640], ![240, 300, 360, 0, 420], ![29840, 11595, 12552, -80, 32710], true⟩

theorem canonicalMatch5_146 :
    canonicalPose5_146.boxKey 19200 (referenceBox5 (!canonicalBox5_146.bump)) = canonicalBox5_146 := by decide

theorem canonicalDecode5_146 : canonicalBox5_146.toKeyData 19200 = keys5Chunk4.get ⟨18, by decide⟩ := by
  change canonicalBox5_146.toKeyData 19200 = ⟨![(31 / 20), (3 / 5), (13 / 20), 0, (17 / 10)], ![(1 / 80), (1 / 64), (3 / 160), 0, (7 / 320)], ![(373 / 240), (773 / 1280), (523 / 800), (-1 / 240), (3271 / 1920)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_146, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_146, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_146, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_146 : keySolid (keys5Chunk4.get ⟨18, by decide⟩) = canonicalPose5_146.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_146 (box := canonicalBox5_146) (k := keys5Chunk4.get ⟨18, by decide⟩) (canonicalMatch5_146) (canonicalDecode5_146)

def canonicalPose5_147 : Pose 5 :=
  ⟨canonicalPerm5_6, ![true, true, false, true, true], ![2, 1, 0, 1, 2]⟩
def canonicalBox5_147 : BoxKey 5 :=
  ⟨![26880, 5760, 12480, 8640, 38400], ![300, 420, 360, 240, 0], ![26805, 5690, 12552, 8560, 38320], false⟩

theorem canonicalMatch5_147 :
    canonicalPose5_147.boxKey 19200 (referenceBox5 (!canonicalBox5_147.bump)) = canonicalBox5_147 := by decide

theorem canonicalDecode5_147 : canonicalBox5_147.toKeyData 19200 = keys5Chunk4.get ⟨19, by decide⟩ := by
  change canonicalBox5_147.toKeyData 19200 = ⟨![(7 / 5), (3 / 10), (13 / 20), (9 / 20), 2], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(1787 / 1280), (569 / 1920), (523 / 800), (107 / 240), (479 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_147, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_147, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_147, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_147 : keySolid (keys5Chunk4.get ⟨19, by decide⟩) = canonicalPose5_147.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_147 (box := canonicalBox5_147) (k := keys5Chunk4.get ⟨19, by decide⟩) (canonicalMatch5_147) (canonicalDecode5_147)

def canonicalPose5_148 : Pose 5 :=
  ⟨canonicalPerm5_19, ![false, true, true, true, false], ![2, 1, 1, 2, 0]⟩
def canonicalBox5_148 : BoxKey 5 :=
  ⟨![38400, 5760, 8640, 26880, 12480], ![0, 420, 240, 300, 360], ![38480, 5690, 8560, 26805, 12552], true⟩

theorem canonicalMatch5_148 :
    canonicalPose5_148.boxKey 19200 (referenceBox5 (!canonicalBox5_148.bump)) = canonicalBox5_148 := by decide

theorem canonicalDecode5_148 : canonicalBox5_148.toKeyData 19200 = keys5Chunk4.get ⟨20, by decide⟩ := by
  change canonicalBox5_148.toKeyData 19200 = ⟨![2, (3 / 10), (9 / 20), (7 / 5), (13 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(481 / 240), (569 / 1920), (107 / 240), (1787 / 1280), (523 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_148, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_148, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_148, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_148 : keySolid (keys5Chunk4.get ⟨20, by decide⟩) = canonicalPose5_148.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_148 (box := canonicalBox5_148) (k := keys5Chunk4.get ⟨20, by decide⟩) (canonicalMatch5_148) (canonicalDecode5_148)

def canonicalPose5_149 : Pose 5 :=
  ⟨canonicalPerm5_3, ![false, false, false, false, false], ![1, 0, 0, 1, 0]⟩
def canonicalBox5_149 : BoxKey 5 :=
  ⟨![29760, 0, 11520, 32640, 12480], ![240, 0, 300, 420, 360], ![29840, 80, 11595, 32710, 12552], false⟩

theorem canonicalMatch5_149 :
    canonicalPose5_149.boxKey 19200 (referenceBox5 (!canonicalBox5_149.bump)) = canonicalBox5_149 := by decide

theorem canonicalDecode5_149 : canonicalBox5_149.toKeyData 19200 = keys5Chunk4.get ⟨21, by decide⟩ := by
  change canonicalBox5_149.toKeyData 19200 = ⟨![(31 / 20), 0, (3 / 5), (17 / 10), (13 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(373 / 240), (1 / 240), (773 / 1280), (3271 / 1920), (523 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_149, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_149, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_149, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_149 : keySolid (keys5Chunk4.get ⟨21, by decide⟩) = canonicalPose5_149.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_149 (box := canonicalBox5_149) (k := keys5Chunk4.get ⟨21, by decide⟩) (canonicalMatch5_149) (canonicalDecode5_149)

def canonicalPose5_150 : Pose 5 :=
  ⟨canonicalPerm5_13, ![false, false, false, false, false], ![1, 0, 0, 1, 0]⟩
def canonicalBox5_150 : BoxKey 5 :=
  ⟨![32640, 11520, 0, 29760, 12480], ![420, 300, 0, 240, 360], ![32710, 11595, 80, 29840, 12552], false⟩

theorem canonicalMatch5_150 :
    canonicalPose5_150.boxKey 19200 (referenceBox5 (!canonicalBox5_150.bump)) = canonicalBox5_150 := by decide

theorem canonicalDecode5_150 : canonicalBox5_150.toKeyData 19200 = keys5Chunk4.get ⟨22, by decide⟩ := by
  change canonicalBox5_150.toKeyData 19200 = ⟨![(17 / 10), (3 / 5), 0, (31 / 20), (13 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(3271 / 1920), (773 / 1280), (1 / 240), (373 / 240), (523 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_150, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_150, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_150, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_150 : keySolid (keys5Chunk4.get ⟨22, by decide⟩) = canonicalPose5_150.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_150 (box := canonicalBox5_150) (k := keys5Chunk4.get ⟨22, by decide⟩) (canonicalMatch5_150) (canonicalDecode5_150)

def canonicalPose5_151 : Pose 5 :=
  ⟨canonicalPerm5_4, ![true, true, true, false, false], ![2, 1, 1, 2, 0]⟩
def canonicalBox5_151 : BoxKey 5 :=
  ⟨![26880, 8640, 5760, 38400, 12480], ![300, 240, 420, 0, 360], ![26805, 8560, 5690, 38480, 12552], true⟩

theorem canonicalMatch5_151 :
    canonicalPose5_151.boxKey 19200 (referenceBox5 (!canonicalBox5_151.bump)) = canonicalBox5_151 := by decide

theorem canonicalDecode5_151 : canonicalBox5_151.toKeyData 19200 = keys5Chunk4.get ⟨23, by decide⟩ := by
  change canonicalBox5_151.toKeyData 19200 = ⟨![(7 / 5), (9 / 20), (3 / 10), 2, (13 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(1787 / 1280), (107 / 240), (569 / 1920), (481 / 240), (523 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_151, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_151, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_151, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_151 : keySolid (keys5Chunk4.get ⟨23, by decide⟩) = canonicalPose5_151.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_151 (box := canonicalBox5_151) (k := keys5Chunk4.get ⟨23, by decide⟩) (canonicalMatch5_151) (canonicalDecode5_151)

def canonicalPose5_152 : Pose 5 :=
  ⟨canonicalPerm5_1, ![false, true, true, false, false], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_152 : BoxKey 5 :=
  ⟨![29760, 6720, 5760, 30720, 0], ![240, 360, 420, 300, 0], ![29840, 6648, 5690, 30795, 80], false⟩

theorem canonicalMatch5_152 :
    canonicalPose5_152.boxKey 19200 (referenceBox5 (!canonicalBox5_152.bump)) = canonicalBox5_152 := by decide

theorem canonicalDecode5_152 : canonicalBox5_152.toKeyData 19200 = keys5Chunk4.get ⟨24, by decide⟩ := by
  change canonicalBox5_152.toKeyData 19200 = ⟨![(31 / 20), (7 / 20), (3 / 10), (8 / 5), 0], ![(1 / 80), (3 / 160), (7 / 320), (1 / 64), 0], ![(373 / 240), (277 / 800), (569 / 1920), (2053 / 1280), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_152, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_152, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_152, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_152 : keySolid (keys5Chunk4.get ⟨24, by decide⟩) = canonicalPose5_152.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_152 (box := canonicalBox5_152) (k := keys5Chunk4.get ⟨24, by decide⟩) (canonicalMatch5_152) (canonicalDecode5_152)

def canonicalPose5_153 : Pose 5 :=
  ⟨canonicalPerm5_6, ![false, true, true, false, false], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_153 : BoxKey 5 :=
  ⟨![30720, 5760, 6720, 29760, 0], ![300, 420, 360, 240, 0], ![30795, 5690, 6648, 29840, 80], false⟩

theorem canonicalMatch5_153 :
    canonicalPose5_153.boxKey 19200 (referenceBox5 (!canonicalBox5_153.bump)) = canonicalBox5_153 := by decide

theorem canonicalDecode5_153 : canonicalBox5_153.toKeyData 19200 = keys5Chunk4.get ⟨25, by decide⟩ := by
  change canonicalBox5_153.toKeyData 19200 = ⟨![(8 / 5), (3 / 10), (7 / 20), (31 / 20), 0], ![(1 / 64), (7 / 320), (3 / 160), (1 / 80), 0], ![(2053 / 1280), (569 / 1920), (277 / 800), (373 / 240), (1 / 240)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_153, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_153, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_153, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_153 : keySolid (keys5Chunk4.get ⟨25, by decide⟩) = canonicalPose5_153.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_153 (box := canonicalBox5_153) (k := keys5Chunk4.get ⟨25, by decide⟩) (canonicalMatch5_153) (canonicalDecode5_153)

def canonicalPose5_154 : Pose 5 :=
  ⟨canonicalPerm5_9, ![false, true, true, false, true], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_154 : BoxKey 5 :=
  ⟨![31680, 7680, 8640, 32640, 0], ![360, 300, 240, 420, 0], ![31752, 7605, 8560, 32710, -80], true⟩

theorem canonicalMatch5_154 :
    canonicalPose5_154.boxKey 19200 (referenceBox5 (!canonicalBox5_154.bump)) = canonicalBox5_154 := by decide

theorem canonicalDecode5_154 : canonicalBox5_154.toKeyData 19200 = keys5Chunk4.get ⟨26, by decide⟩ := by
  change canonicalBox5_154.toKeyData 19200 = ⟨![(33 / 20), (2 / 5), (9 / 20), (17 / 10), 0], ![(3 / 160), (1 / 64), (1 / 80), (7 / 320), 0], ![(1323 / 800), (507 / 1280), (107 / 240), (3271 / 1920), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_154, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_154, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_154, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_154 : keySolid (keys5Chunk4.get ⟨26, by decide⟩) = canonicalPose5_154.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_154 (box := canonicalBox5_154) (k := keys5Chunk4.get ⟨26, by decide⟩) (canonicalMatch5_154) (canonicalDecode5_154)

def canonicalPose5_155 : Pose 5 :=
  ⟨canonicalPerm5_12, ![false, true, true, false, true], ![1, 1, 1, 1, 0]⟩
def canonicalBox5_155 : BoxKey 5 :=
  ⟨![32640, 8640, 7680, 31680, 0], ![420, 240, 300, 360, 0], ![32710, 8560, 7605, 31752, -80], true⟩

theorem canonicalMatch5_155 :
    canonicalPose5_155.boxKey 19200 (referenceBox5 (!canonicalBox5_155.bump)) = canonicalBox5_155 := by decide

theorem canonicalDecode5_155 : canonicalBox5_155.toKeyData 19200 = keys5Chunk4.get ⟨27, by decide⟩ := by
  change canonicalBox5_155.toKeyData 19200 = ⟨![(17 / 10), (9 / 20), (2 / 5), (33 / 20), 0], ![(7 / 320), (1 / 80), (1 / 64), (3 / 160), 0], ![(3271 / 1920), (107 / 240), (507 / 1280), (1323 / 800), (-1 / 240)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_155, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_155, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_155, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_155 : keySolid (keys5Chunk4.get ⟨27, by decide⟩) = canonicalPose5_155.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_155 (box := canonicalBox5_155) (k := keys5Chunk4.get ⟨27, by decide⟩) (canonicalMatch5_155) (canonicalDecode5_155)

def canonicalPose5_156 : Pose 5 :=
  ⟨canonicalPerm5_19, ![true, true, true, true, true], ![2, 1, 1, 2, 2]⟩
def canonicalBox5_156 : BoxKey 5 :=
  ⟨![38400, 5760, 8640, 26880, 25920], ![0, 420, 240, 300, 360], ![38320, 5690, 8560, 26805, 25848], false⟩

theorem canonicalMatch5_156 :
    canonicalPose5_156.boxKey 19200 (referenceBox5 (!canonicalBox5_156.bump)) = canonicalBox5_156 := by decide

theorem canonicalDecode5_156 : canonicalBox5_156.toKeyData 19200 = keys5Chunk4.get ⟨28, by decide⟩ := by
  change canonicalBox5_156.toKeyData 19200 = ⟨![2, (3 / 10), (9 / 20), (7 / 5), (27 / 20)], ![0, (7 / 320), (1 / 80), (1 / 64), (3 / 160)], ![(479 / 240), (569 / 1920), (107 / 240), (1787 / 1280), (1077 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_156, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_156, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_156, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_156 : keySolid (keys5Chunk4.get ⟨28, by decide⟩) = canonicalPose5_156.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_156 (box := canonicalBox5_156) (k := keys5Chunk4.get ⟨28, by decide⟩) (canonicalMatch5_156) (canonicalDecode5_156)

def canonicalPose5_157 : Pose 5 :=
  ⟨canonicalPerm5_3, ![false, true, false, false, true], ![1, 0, 0, 1, 2]⟩
def canonicalBox5_157 : BoxKey 5 :=
  ⟨![29760, 0, 11520, 32640, 25920], ![240, 0, 300, 420, 360], ![29840, -80, 11595, 32710, 25848], true⟩

theorem canonicalMatch5_157 :
    canonicalPose5_157.boxKey 19200 (referenceBox5 (!canonicalBox5_157.bump)) = canonicalBox5_157 := by decide

theorem canonicalDecode5_157 : canonicalBox5_157.toKeyData 19200 = keys5Chunk4.get ⟨29, by decide⟩ := by
  change canonicalBox5_157.toKeyData 19200 = ⟨![(31 / 20), 0, (3 / 5), (17 / 10), (27 / 20)], ![(1 / 80), 0, (1 / 64), (7 / 320), (3 / 160)], ![(373 / 240), (-1 / 240), (773 / 1280), (3271 / 1920), (1077 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_157, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_157, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_157, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_157 : keySolid (keys5Chunk4.get ⟨29, by decide⟩) = canonicalPose5_157.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_157 (box := canonicalBox5_157) (k := keys5Chunk4.get ⟨29, by decide⟩) (canonicalMatch5_157) (canonicalDecode5_157)

def canonicalPose5_158 : Pose 5 :=
  ⟨canonicalPerm5_13, ![false, false, true, false, true], ![1, 0, 0, 1, 2]⟩
def canonicalBox5_158 : BoxKey 5 :=
  ⟨![32640, 11520, 0, 29760, 25920], ![420, 300, 0, 240, 360], ![32710, 11595, -80, 29840, 25848], true⟩

theorem canonicalMatch5_158 :
    canonicalPose5_158.boxKey 19200 (referenceBox5 (!canonicalBox5_158.bump)) = canonicalBox5_158 := by decide

theorem canonicalDecode5_158 : canonicalBox5_158.toKeyData 19200 = keys5Chunk4.get ⟨30, by decide⟩ := by
  change canonicalBox5_158.toKeyData 19200 = ⟨![(17 / 10), (3 / 5), 0, (31 / 20), (27 / 20)], ![(7 / 320), (1 / 64), 0, (1 / 80), (3 / 160)], ![(3271 / 1920), (773 / 1280), (-1 / 240), (373 / 240), (1077 / 800)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_158, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_158, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_158, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_158 : keySolid (keys5Chunk4.get ⟨30, by decide⟩) = canonicalPose5_158.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_158 (box := canonicalBox5_158) (k := keys5Chunk4.get ⟨30, by decide⟩) (canonicalMatch5_158) (canonicalDecode5_158)

def canonicalPose5_159 : Pose 5 :=
  ⟨canonicalPerm5_4, ![true, true, true, true, true], ![2, 1, 1, 2, 2]⟩
def canonicalBox5_159 : BoxKey 5 :=
  ⟨![26880, 8640, 5760, 38400, 25920], ![300, 240, 420, 0, 360], ![26805, 8560, 5690, 38320, 25848], false⟩

theorem canonicalMatch5_159 :
    canonicalPose5_159.boxKey 19200 (referenceBox5 (!canonicalBox5_159.bump)) = canonicalBox5_159 := by decide

theorem canonicalDecode5_159 : canonicalBox5_159.toKeyData 19200 = keys5Chunk4.get ⟨31, by decide⟩ := by
  change canonicalBox5_159.toKeyData 19200 = ⟨![(7 / 5), (9 / 20), (3 / 10), 2, (27 / 20)], ![(1 / 64), (1 / 80), (7 / 320), 0, (3 / 160)], ![(1787 / 1280), (107 / 240), (569 / 1920), (479 / 240), (1077 / 800)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_159, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_159, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox5_159, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid5_159 : keySolid (keys5Chunk4.get ⟨31, by decide⟩) = canonicalPose5_159.euclidean '' referenceSolid5 :=
  canonical5_of_box_match canonicalPose5_159 (box := canonicalBox5_159) (k := keys5Chunk4.get ⟨31, by decide⟩) (canonicalMatch5_159) (canonicalDecode5_159)

theorem keys5Chunk4_canonical : ∀ k ∈ keys5Chunk4,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  intro k hk
  simp only [keys5Chunk4, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose5_128, canonicalSolid5_128⟩
  · exact ⟨canonicalPose5_129, canonicalSolid5_129⟩
  · exact ⟨canonicalPose5_130, canonicalSolid5_130⟩
  · exact ⟨canonicalPose5_131, canonicalSolid5_131⟩
  · exact ⟨canonicalPose5_132, canonicalSolid5_132⟩
  · exact ⟨canonicalPose5_133, canonicalSolid5_133⟩
  · exact ⟨canonicalPose5_134, canonicalSolid5_134⟩
  · exact ⟨canonicalPose5_135, canonicalSolid5_135⟩
  · exact ⟨canonicalPose5_136, canonicalSolid5_136⟩
  · exact ⟨canonicalPose5_137, canonicalSolid5_137⟩
  · exact ⟨canonicalPose5_138, canonicalSolid5_138⟩
  · exact ⟨canonicalPose5_139, canonicalSolid5_139⟩
  · exact ⟨canonicalPose5_140, canonicalSolid5_140⟩
  · exact ⟨canonicalPose5_141, canonicalSolid5_141⟩
  · exact ⟨canonicalPose5_142, canonicalSolid5_142⟩
  · exact ⟨canonicalPose5_143, canonicalSolid5_143⟩
  · exact ⟨canonicalPose5_144, canonicalSolid5_144⟩
  · exact ⟨canonicalPose5_145, canonicalSolid5_145⟩
  · exact ⟨canonicalPose5_146, canonicalSolid5_146⟩
  · exact ⟨canonicalPose5_147, canonicalSolid5_147⟩
  · exact ⟨canonicalPose5_148, canonicalSolid5_148⟩
  · exact ⟨canonicalPose5_149, canonicalSolid5_149⟩
  · exact ⟨canonicalPose5_150, canonicalSolid5_150⟩
  · exact ⟨canonicalPose5_151, canonicalSolid5_151⟩
  · exact ⟨canonicalPose5_152, canonicalSolid5_152⟩
  · exact ⟨canonicalPose5_153, canonicalSolid5_153⟩
  · exact ⟨canonicalPose5_154, canonicalSolid5_154⟩
  · exact ⟨canonicalPose5_155, canonicalSolid5_155⟩
  · exact ⟨canonicalPose5_156, canonicalSolid5_156⟩
  · exact ⟨canonicalPose5_157, canonicalSolid5_157⟩
  · exact ⟨canonicalPose5_158, canonicalSolid5_158⟩
  · exact ⟨canonicalPose5_159, canonicalSolid5_159⟩

#print axioms keys5Chunk4_canonical

end SparseMonotiles.Canonical
