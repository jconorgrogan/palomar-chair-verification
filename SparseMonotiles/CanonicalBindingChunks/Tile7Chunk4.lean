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

def canonicalPose7_128 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, false, false, false, false], ![0, 0, 1, 0, 0, 0, 0]⟩
def canonicalBox7_128 : BoxKey 7 :=
  ⟨![0, 120960, 315840, 134400, 100800, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 121380, 316240, 134785, 101360, 108010, 114688], true⟩

theorem canonicalMatch7_128 :
    canonicalPose7_128.boxKey 188160 (referenceBox7 (!canonicalBox7_128.bump)) = canonicalBox7_128 := by decide +kernel

theorem canonicalDecode7_128 : canonicalBox7_128.toKeyData 188160 = keys7Chunk4.get ⟨0, by decide⟩ := by
  change canonicalBox7_128.toKeyData 188160 = ⟨![0, (9 / 14), (47 / 28), (5 / 7), (15 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_128 : keySolid (keys7Chunk4.get ⟨0, by decide⟩) = canonicalPose7_128.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_128 (box := canonicalBox7_128) (k := keys7Chunk4.get ⟨0, by decide⟩) (canonicalMatch7_128) (canonicalDecode7_128)

def canonicalPose7_129 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, true, false, false, true, true], ![0, 0, 2, 0, 0, 1, 1]⟩
def canonicalBox7_129 : BoxKey 7 :=
  ⟨![120960, 0, 262080, 107520, 100800, 53760, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, -560, 261632, 108010, 101360, 53375, 60080], true⟩

theorem canonicalMatch7_129 :
    canonicalPose7_129.boxKey 188160 (referenceBox7 (!canonicalBox7_129.bump)) = canonicalBox7_129 := by decide +kernel

theorem canonicalDecode7_129 : canonicalBox7_129.toKeyData 188160 = keys7Chunk4.get ⟨1, by decide⟩ := by
  change canonicalBox7_129.toKeyData 188160 = ⟨![(9 / 14), 0, (39 / 28), (4 / 7), (15 / 28), (2 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (181 / 336), (1525 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_129 : keySolid (keys7Chunk4.get ⟨1, by decide⟩) = canonicalPose7_129.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_129 (box := canonicalBox7_129) (k := keys7Chunk4.get ⟨1, by decide⟩) (canonicalMatch7_129) (canonicalDecode7_129)

def canonicalPose7_130 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, true, true, false, false, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_130 : BoxKey 7 :=
  ⟨![107520, 73920, 376320, 67200, 127680, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 73472, 375760, 66780, 128080, 134785, 101360], false⟩

theorem canonicalMatch7_130 :
    canonicalPose7_130.boxKey 188160 (referenceBox7 (!canonicalBox7_130.bump)) = canonicalBox7_130 := by decide +kernel

theorem canonicalDecode7_130 : canonicalBox7_130.toKeyData 188160 = keys7Chunk4.get ⟨2, by decide⟩ := by
  change canonicalBox7_130.toKeyData 188160 = ⟨![(4 / 7), (11 / 28), 2, (5 / 14), (19 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (41 / 105), (671 / 336), (159 / 448), (1601 / 2352), (3851 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_130 : keySolid (keys7Chunk4.get ⟨2, by decide⟩) = canonicalPose7_130.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_130 (box := canonicalBox7_130) (k := keys7Chunk4.get ⟨2, by decide⟩) (canonicalMatch7_130) (canonicalDecode7_130)

def canonicalPose7_131 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, false, true, false, false, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_131 : BoxKey 7 :=
  ⟨![127680, 67200, 376320, 73920, 107520, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 66780, 376880, 73472, 108010, 101360, 134785], true⟩

theorem canonicalMatch7_131 :
    canonicalPose7_131.boxKey 188160 (referenceBox7 (!canonicalBox7_131.bump)) = canonicalBox7_131 := by decide +kernel

theorem canonicalDecode7_131 : canonicalBox7_131.toKeyData 188160 = keys7Chunk4.get ⟨3, by decide⟩ := by
  change canonicalBox7_131.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), 2, (11 / 28), (4 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (673 / 336), (41 / 105), (1543 / 2688), (181 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_131 : keySolid (keys7Chunk4.get ⟨3, by decide⟩) = canonicalPose7_131.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_131 (box := canonicalBox7_131) (k := keys7Chunk4.get ⟨3, by decide⟩) (canonicalMatch7_131) (canonicalDecode7_131)

def canonicalPose7_132 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, true, false, false, true, true], ![0, 0, 2, 0, 0, 1, 1]⟩
def canonicalBox7_132 : BoxKey 7 :=
  ⟨![100800, 107520, 262080, 0, 120960, 60480, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 261632, 560, 121380, 60080, 53375], false⟩

theorem canonicalMatch7_132 :
    canonicalPose7_132.boxKey 188160 (referenceBox7 (!canonicalBox7_132.bump)) = canonicalBox7_132 := by decide +kernel

theorem canonicalDecode7_132 : canonicalBox7_132.toKeyData 188160 = keys7Chunk4.get ⟨4, by decide⟩ := by
  change canonicalBox7_132.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (9 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (751 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_132 : keySolid (keys7Chunk4.get ⟨4, by decide⟩) = canonicalPose7_132.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_132 (box := canonicalBox7_132) (k := keys7Chunk4.get ⟨4, by decide⟩) (canonicalMatch7_132) (canonicalDecode7_132)

def canonicalPose7_133 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, false, false, false], ![0, 0, 1, 0, 0, 0, 0]⟩
def canonicalBox7_133 : BoxKey 7 :=
  ⟨![100800, 134400, 315840, 120960, 0, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 316240, 121380, 560, 114688, 108010], false⟩

theorem canonicalMatch7_133 :
    canonicalPose7_133.boxKey 188160 (referenceBox7 (!canonicalBox7_133.bump)) = canonicalBox7_133 := by decide +kernel

theorem canonicalDecode7_133 : canonicalBox7_133.toKeyData 188160 = keys7Chunk4.get ⟨5, by decide⟩ := by
  change canonicalBox7_133.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (47 / 28), (9 / 14), 0, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (64 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_133 : keySolid (keys7Chunk4.get ⟨5, by decide⟩) = canonicalPose7_133.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_133 (box := canonicalBox7_133) (k := keys7Chunk4.get ⟨5, by decide⟩) (canonicalMatch7_133) (canonicalDecode7_133)

def canonicalPose7_134 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, true, true, true, false, true, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_134 : BoxKey 7 :=
  ⟨![100800, 53760, 248640, 67200, 114240, 0, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 53375, 248240, 66780, 114688, -560, 108010], true⟩

theorem canonicalMatch7_134 :
    canonicalPose7_134.boxKey 188160 (referenceBox7 (!canonicalBox7_134.bump)) = canonicalBox7_134 := by decide +kernel

theorem canonicalDecode7_134 : canonicalBox7_134.toKeyData 188160 = keys7Chunk4.get ⟨6, by decide⟩ := by
  change canonicalBox7_134.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (37 / 28), (5 / 14), (17 / 28), 0, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (-1 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_134 : keySolid (keys7Chunk4.get ⟨6, by decide⟩) = canonicalPose7_134.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_134 (box := canonicalBox7_134) (k := keys7Chunk4.get ⟨6, by decide⟩) (canonicalMatch7_134) (canonicalDecode7_134)

def canonicalPose7_135 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, true, true, true, false, false, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_135 : BoxKey 7 :=
  ⟨![114240, 67200, 248640, 53760, 100800, 107520, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 66780, 248240, 53375, 101360, 108010, 560], false⟩

theorem canonicalMatch7_135 :
    canonicalPose7_135.boxKey 188160 (referenceBox7 (!canonicalBox7_135.bump)) = canonicalBox7_135 := by decide +kernel

theorem canonicalDecode7_135 : canonicalBox7_135.toKeyData 188160 = keys7Chunk4.get ⟨7, by decide⟩ := by
  change canonicalBox7_135.toKeyData 188160 = ⟨![(17 / 28), (5 / 14), (37 / 28), (2 / 7), (15 / 28), (4 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_135 : keySolid (keys7Chunk4.get ⟨7, by decide⟩) = canonicalPose7_135.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_135 (box := canonicalBox7_135) (k := keys7Chunk4.get ⟨7, by decide⟩) (canonicalMatch7_135) (canonicalDecode7_135)

def canonicalPose7_136 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, false, true, true, false, true, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_136 : BoxKey 7 :=
  ⟨![0, 107520, 275520, 53760, 127680, 67200, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![560, 108010, 274960, 53375, 128080, 66780, 261632], false⟩

theorem canonicalMatch7_136 :
    canonicalPose7_136.boxKey 188160 (referenceBox7 (!canonicalBox7_136.bump)) = canonicalBox7_136 := by decide +kernel

theorem canonicalDecode7_136 : canonicalBox7_136.toKeyData 188160 = keys7Chunk4.get ⟨8, by decide⟩ := by
  change canonicalBox7_136.toKeyData 188160 = ⟨![0, (4 / 7), (41 / 28), (2 / 7), (19 / 28), (5 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_136 : keySolid (keys7Chunk4.get ⟨8, by decide⟩) = canonicalPose7_136.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_136 (box := canonicalBox7_136) (k := keys7Chunk4.get ⟨8, by decide⟩) (canonicalMatch7_136) (canonicalDecode7_136)

def canonicalPose7_137 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, true, true, true, false, true, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_137 : BoxKey 7 :=
  ⟨![107520, 0, 262080, 67200, 127680, 53760, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, -560, 261632, 66780, 128080, 53375, 274960], true⟩

theorem canonicalMatch7_137 :
    canonicalPose7_137.boxKey 188160 (referenceBox7 (!canonicalBox7_137.bump)) = canonicalBox7_137 := by decide +kernel

theorem canonicalDecode7_137 : canonicalBox7_137.toKeyData 188160 = keys7Chunk4.get ⟨9, by decide⟩ := by
  change canonicalBox7_137.toKeyData 188160 = ⟨![(4 / 7), 0, (39 / 28), (5 / 14), (19 / 28), (2 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (-1 / 336), (146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_137 : keySolid (keys7Chunk4.get ⟨9, by decide⟩) = canonicalPose7_137.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_137 (box := canonicalBox7_137) (k := keys7Chunk4.get ⟨9, by decide⟩) (canonicalMatch7_137) (canonicalDecode7_137)

def canonicalPose7_138 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, false, true, false, true], ![0, 0, 2, 0, 1, 0, 2]⟩
def canonicalBox7_138 : BoxKey 7 :=
  ⟨![107520, 114240, 376320, 120960, 60480, 134400, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, 375760, 121380, 60080, 134785, 274960], false⟩

theorem canonicalMatch7_138 :
    canonicalPose7_138.boxKey 188160 (referenceBox7 (!canonicalBox7_138.bump)) = canonicalBox7_138 := by decide +kernel

theorem canonicalDecode7_138 : canonicalBox7_138.toKeyData 188160 = keys7Chunk4.get ⟨10, by decide⟩ := by
  change canonicalBox7_138.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 2, (9 / 14), (9 / 28), (5 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (671 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_138 : keySolid (keys7Chunk4.get ⟨10, by decide⟩) = canonicalPose7_138.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_138 (box := canonicalBox7_138) (k := keys7Chunk4.get ⟨10, by decide⟩) (canonicalMatch7_138) (canonicalDecode7_138)

def canonicalPose7_139 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, false, false, false, true], ![1, 1, 2, 0, 0, 0, 2]⟩
def canonicalBox7_139 : BoxKey 7 :=
  ⟨![53760, 60480, 255360, 0, 114240, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 60080, 254940, 560, 114688, 108010, 274960], false⟩

theorem canonicalMatch7_139 :
    canonicalPose7_139.boxKey 188160 (referenceBox7 (!canonicalBox7_139.bump)) = canonicalBox7_139 := by decide +kernel

theorem canonicalDecode7_139 : canonicalBox7_139.toKeyData 188160 = keys7Chunk4.get ⟨11, by decide⟩ := by
  change canonicalBox7_139.toKeyData 188160 = ⟨![(2 / 7), (9 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (751 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_139 : keySolid (keys7Chunk4.get ⟨11, by decide⟩) = canonicalPose7_139.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_139 (box := canonicalBox7_139) (k := keys7Chunk4.get ⟨11, by decide⟩) (canonicalMatch7_139) (canonicalDecode7_139)

def canonicalPose7_140 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, true, false, true, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_140 : BoxKey 7 :=
  ⟨![100800, 134400, 248640, 67200, 0, 73920, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 248240, 66780, 560, 73472, 268310], false⟩

theorem canonicalMatch7_140 :
    canonicalPose7_140.boxKey 188160 (referenceBox7 (!canonicalBox7_140.bump)) = canonicalBox7_140 := by decide +kernel

theorem canonicalDecode7_140 : canonicalBox7_140.toKeyData 188160 = keys7Chunk4.get ⟨12, by decide⟩ := by
  change canonicalBox7_140.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (37 / 28), (5 / 14), 0, (11 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448), (1 / 336), (41 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_140 : keySolid (keys7Chunk4.get ⟨12, by decide⟩) = canonicalPose7_140.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_140 (box := canonicalBox7_140) (k := keys7Chunk4.get ⟨12, by decide⟩) (canonicalMatch7_140) (canonicalDecode7_140)

def canonicalPose7_141 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, true, true, true, true], ![0, 0, 2, 1, 0, 1, 2]⟩
def canonicalBox7_141 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 73920, 0, 67200, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 73472, -560, 66780, 248240], true⟩

theorem canonicalMatch7_141 :
    canonicalPose7_141.boxKey 188160 (referenceBox7 (!canonicalBox7_141.bump)) = canonicalBox7_141 := by decide +kernel

theorem canonicalDecode7_141 : canonicalBox7_141.toKeyData 188160 = keys7Chunk4.get ⟨13, by decide⟩ := by
  change canonicalBox7_141.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (11 / 28), 0, (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105), (-1 / 336), (159 / 448), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_141 : keySolid (keys7Chunk4.get ⟨13, by decide⟩) = canonicalPose7_141.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_141 (box := canonicalBox7_141) (k := keys7Chunk4.get ⟨13, by decide⟩) (canonicalMatch7_141) (canonicalDecode7_141)

def canonicalPose7_142 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, false, false, true, true], ![1, 1, 2, 0, 0, 0, 2]⟩
def canonicalBox7_142 : BoxKey 7 :=
  ⟨![60480, 53760, 275520, 107520, 114240, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 53375, 274960, 108010, 114688, -560, 254940], true⟩

theorem canonicalMatch7_142 :
    canonicalPose7_142.boxKey 188160 (referenceBox7 (!canonicalBox7_142.bump)) = canonicalBox7_142 := by decide +kernel

theorem canonicalDecode7_142 : canonicalBox7_142.toKeyData 188160 = keys7Chunk4.get ⟨14, by decide⟩ := by
  change canonicalBox7_142.toKeyData 188160 = ⟨![(9 / 28), (2 / 7), (41 / 28), (4 / 7), (17 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_142 : keySolid (keys7Chunk4.get ⟨14, by decide⟩) = canonicalPose7_142.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_142 (box := canonicalBox7_142) (k := keys7Chunk4.get ⟨14, by decide⟩) (canonicalMatch7_142) (canonicalDecode7_142)

def canonicalPose7_143 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, false, true, false, false], ![0, 0, 2, 0, 1, 0, 2]⟩
def canonicalBox7_143 : BoxKey 7 :=
  ⟨![114240, 107520, 275520, 134400, 60480, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 274960, 134785, 60080, 121380, 376880], true⟩

theorem canonicalMatch7_143 :
    canonicalPose7_143.boxKey 188160 (referenceBox7 (!canonicalBox7_143.bump)) = canonicalBox7_143 := by decide +kernel

theorem canonicalDecode7_143 : canonicalBox7_143.toKeyData 188160 = keys7Chunk4.get ⟨15, by decide⟩ := by
  change canonicalBox7_143.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (41 / 28), (5 / 7), (9 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_143 : keySolid (keys7Chunk4.get ⟨15, by decide⟩) = canonicalPose7_143.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_143 (box := canonicalBox7_143) (k := keys7Chunk4.get ⟨15, by decide⟩) (canonicalMatch7_143) (canonicalDecode7_143)

def canonicalPose7_144 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, false, false, true, true], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_144 : BoxKey 7 :=
  ⟨![0, 73920, 268800, 100800, 134400, 248640, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 73472, 268310, 101360, 134785, 248240, 66780], false⟩

theorem canonicalMatch7_144 :
    canonicalPose7_144.boxKey 188160 (referenceBox7 (!canonicalBox7_144.bump)) = canonicalBox7_144 := by decide +kernel

theorem canonicalDecode7_144 : canonicalBox7_144.toKeyData 188160 = keys7Chunk4.get ⟨16, by decide⟩ := by
  change canonicalBox7_144.toKeyData 188160 = ⟨![0, (11 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_144 : keySolid (keys7Chunk4.get ⟨16, by decide⟩) = canonicalPose7_144.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_144 (box := canonicalBox7_144) (k := keys7Chunk4.get ⟨16, by decide⟩) (canonicalMatch7_144) (canonicalDecode7_144)

def canonicalPose7_145 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, false, false, true, true], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_145 : BoxKey 7 :=
  ⟨![0, 67200, 248640, 134400, 100800, 268800, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 66780, 248240, 134785, 101360, 268310, 73472], true⟩

theorem canonicalMatch7_145 :
    canonicalPose7_145.boxKey 188160 (referenceBox7 (!canonicalBox7_145.bump)) = canonicalBox7_145 := by decide +kernel

theorem canonicalDecode7_145 : canonicalBox7_145.toKeyData 188160 = keys7Chunk4.get ⟨17, by decide⟩ := by
  change canonicalBox7_145.toKeyData 188160 = ⟨![0, (5 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_145 : keySolid (keys7Chunk4.get ⟨17, by decide⟩) = canonicalPose7_145.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_145 (box := canonicalBox7_145) (k := keys7Chunk4.get ⟨17, by decide⟩) (canonicalMatch7_145) (canonicalDecode7_145)

def canonicalPose7_146 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, true, true, true, true, false], ![0, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_146 : BoxKey 7 :=
  ⟨![114240, 0, 255360, 60480, 53760, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, -560, 254940, 60080, 53375, 274960, 108010], true⟩

theorem canonicalMatch7_146 :
    canonicalPose7_146.boxKey 188160 (referenceBox7 (!canonicalBox7_146.bump)) = canonicalBox7_146 := by decide +kernel

theorem canonicalDecode7_146 : canonicalBox7_146.toKeyData 188160 = keys7Chunk4.get ⟨18, by decide⟩ := by
  change canonicalBox7_146.toKeyData 188160 = ⟨![(17 / 28), 0, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (-1 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_146 : keySolid (keys7Chunk4.get ⟨18, by decide⟩) = canonicalPose7_146.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_146 (box := canonicalBox7_146) (k := keys7Chunk4.get ⟨18, by decide⟩) (canonicalMatch7_146) (canonicalDecode7_146)

def canonicalPose7_147 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, false, false, false, true, false], ![1, 0, 2, 0, 0, 2, 0]⟩
def canonicalBox7_147 : BoxKey 7 :=
  ⟨![60480, 120960, 376320, 114240, 107520, 275520, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, 376880, 114688, 108010, 274960, 134785], true⟩

theorem canonicalMatch7_147 :
    canonicalPose7_147.boxKey 188160 (referenceBox7 (!canonicalBox7_147.bump)) = canonicalBox7_147 := by decide +kernel

theorem canonicalDecode7_147 : canonicalBox7_147.toKeyData 188160 = keys7Chunk4.get ⟨19, by decide⟩ := by
  change canonicalBox7_147.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (673 / 336), (64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_147 : keySolid (keys7Chunk4.get ⟨19, by decide⟩) = canonicalPose7_147.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_147 (box := canonicalBox7_147) (k := keys7Chunk4.get ⟨19, by decide⟩) (canonicalMatch7_147) (canonicalDecode7_147)

def canonicalPose7_148 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, true, true, false, false, true, true], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_148 : BoxKey 7 :=
  ⟨![127680, 67200, 262080, 0, 107520, 275520, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 66780, 261632, 560, 108010, 274960, 53375], false⟩

theorem canonicalMatch7_148 :
    canonicalPose7_148.boxKey 188160 (referenceBox7 (!canonicalBox7_148.bump)) = canonicalBox7_148 := by decide +kernel

theorem canonicalDecode7_148 : canonicalBox7_148.toKeyData 188160 = keys7Chunk4.get ⟨20, by decide⟩ := by
  change canonicalBox7_148.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (146 / 105), (1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_148 : keySolid (keys7Chunk4.get ⟨20, by decide⟩) = canonicalPose7_148.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_148 (box := canonicalBox7_148) (k := keys7Chunk4.get ⟨20, by decide⟩) (canonicalMatch7_148) (canonicalDecode7_148)

def canonicalPose7_149 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, true, true, false, true, true, true], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_149 : BoxKey 7 :=
  ⟨![127680, 53760, 275520, 107520, 0, 262080, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 53375, 274960, 108010, -560, 261632, 66780], true⟩

theorem canonicalMatch7_149 :
    canonicalPose7_149.boxKey 188160 (referenceBox7 (!canonicalBox7_149.bump)) = canonicalBox7_149 := by decide +kernel

theorem canonicalDecode7_149 : canonicalBox7_149.toKeyData 188160 = keys7Chunk4.get ⟨21, by decide⟩ := by
  change canonicalBox7_149.toKeyData 188160 = ⟨![(19 / 28), (2 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (-1 / 336), (146 / 105), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_149 : keySolid (keys7Chunk4.get ⟨21, by decide⟩) = canonicalPose7_149.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_149 (box := canonicalBox7_149) (k := keys7Chunk4.get ⟨21, by decide⟩) (canonicalMatch7_149) (canonicalDecode7_149)

def canonicalPose7_150 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, true, false, false, true, false], ![1, 0, 2, 0, 0, 2, 0]⟩
def canonicalBox7_150 : BoxKey 7 :=
  ⟨![60480, 134400, 275520, 107520, 114240, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 134785, 274960, 108010, 114688, 375760, 121380], false⟩

theorem canonicalMatch7_150 :
    canonicalPose7_150.boxKey 188160 (referenceBox7 (!canonicalBox7_150.bump)) = canonicalBox7_150 := by decide +kernel

theorem canonicalDecode7_150 : canonicalBox7_150.toKeyData 188160 = keys7Chunk4.get ⟨22, by decide⟩ := by
  change canonicalBox7_150.toKeyData 188160 = ⟨![(9 / 28), (5 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (671 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_150 : keySolid (keys7Chunk4.get ⟨22, by decide⟩) = canonicalPose7_150.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_150 (box := canonicalBox7_150) (k := keys7Chunk4.get ⟨22, by decide⟩) (canonicalMatch7_150) (canonicalDecode7_150)

def canonicalPose7_151 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, true, true, true, false], ![0, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_151 : BoxKey 7 :=
  ⟨![114240, 107520, 275520, 53760, 60480, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 274960, 53375, 60080, 254940, 560], false⟩

theorem canonicalMatch7_151 :
    canonicalPose7_151.boxKey 188160 (referenceBox7 (!canonicalBox7_151.bump)) = canonicalBox7_151 := by decide +kernel

theorem canonicalDecode7_151 : canonicalBox7_151.toKeyData 188160 = keys7Chunk4.get ⟨23, by decide⟩ := by
  change canonicalBox7_151.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_151 : keySolid (keys7Chunk4.get ⟨23, by decide⟩) = canonicalPose7_151.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_151 (box := canonicalBox7_151) (k := keys7Chunk4.get ⟨23, by decide⟩) (canonicalMatch7_151) (canonicalDecode7_151)

def canonicalPose7_152 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, false, false, true, true], ![0, 0, 1, 0, 0, 2, 2]⟩
def canonicalBox7_152 : BoxKey 7 :=
  ⟨![0, 120960, 315840, 134400, 100800, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 121380, 316240, 134785, 101360, 268310, 261632], true⟩

theorem canonicalMatch7_152 :
    canonicalPose7_152.boxKey 188160 (referenceBox7 (!canonicalBox7_152.bump)) = canonicalBox7_152 := by decide +kernel

theorem canonicalDecode7_152 : canonicalBox7_152.toKeyData 188160 = keys7Chunk4.get ⟨24, by decide⟩ := by
  change canonicalBox7_152.toKeyData 188160 = ⟨![0, (9 / 14), (47 / 28), (5 / 7), (15 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_152 : keySolid (keys7Chunk4.get ⟨24, by decide⟩) = canonicalPose7_152.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_152 (box := canonicalBox7_152) (k := keys7Chunk4.get ⟨24, by decide⟩) (canonicalMatch7_152) (canonicalDecode7_152)

def canonicalPose7_153 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, true, false, false, false, false], ![0, 0, 2, 0, 0, 1, 1]⟩
def canonicalBox7_153 : BoxKey 7 :=
  ⟨![120960, 0, 262080, 107520, 100800, 322560, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, -560, 261632, 108010, 101360, 322945, 316240], true⟩

theorem canonicalMatch7_153 :
    canonicalPose7_153.boxKey 188160 (referenceBox7 (!canonicalBox7_153.bump)) = canonicalBox7_153 := by decide +kernel

theorem canonicalDecode7_153 : canonicalBox7_153.toKeyData 188160 = keys7Chunk4.get ⟨25, by decide⟩ := by
  change canonicalBox7_153.toKeyData 188160 = ⟨![(9 / 14), 0, (39 / 28), (4 / 7), (15 / 28), (12 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_153 : keySolid (keys7Chunk4.get ⟨25, by decide⟩) = canonicalPose7_153.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_153 (box := canonicalBox7_153) (k := keys7Chunk4.get ⟨25, by decide⟩) (canonicalMatch7_153) (canonicalDecode7_153)

def canonicalPose7_154 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, true, true, false, true, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_154 : BoxKey 7 :=
  ⟨![107520, 73920, 376320, 67200, 127680, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 73472, 375760, 66780, 128080, 241535, 274960], false⟩

theorem canonicalMatch7_154 :
    canonicalPose7_154.boxKey 188160 (referenceBox7 (!canonicalBox7_154.bump)) = canonicalBox7_154 := by decide +kernel

theorem canonicalDecode7_154 : canonicalBox7_154.toKeyData 188160 = keys7Chunk4.get ⟨26, by decide⟩ := by
  change canonicalBox7_154.toKeyData 188160 = ⟨![(4 / 7), (11 / 28), 2, (5 / 14), (19 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (41 / 105), (671 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_154 : keySolid (keys7Chunk4.get ⟨26, by decide⟩) = canonicalPose7_154.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_154 (box := canonicalBox7_154) (k := keys7Chunk4.get ⟨26, by decide⟩) (canonicalMatch7_154) (canonicalDecode7_154)

def canonicalPose7_155 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, false, true, false, true, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_155 : BoxKey 7 :=
  ⟨![127680, 67200, 376320, 73920, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 66780, 376880, 73472, 108010, 274960, 241535], true⟩

theorem canonicalMatch7_155 :
    canonicalPose7_155.boxKey 188160 (referenceBox7 (!canonicalBox7_155.bump)) = canonicalBox7_155 := by decide +kernel

theorem canonicalDecode7_155 : canonicalBox7_155.toKeyData 188160 = keys7Chunk4.get ⟨27, by decide⟩ := by
  change canonicalBox7_155.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), 2, (11 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (673 / 336), (41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_155 : keySolid (keys7Chunk4.get ⟨27, by decide⟩) = canonicalPose7_155.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_155 (box := canonicalBox7_155) (k := keys7Chunk4.get ⟨27, by decide⟩) (canonicalMatch7_155) (canonicalDecode7_155)

def canonicalPose7_156 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, true, false, false, false, false], ![0, 0, 2, 0, 0, 1, 1]⟩
def canonicalBox7_156 : BoxKey 7 :=
  ⟨![100800, 107520, 262080, 0, 120960, 315840, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 261632, 560, 121380, 316240, 322945], false⟩

theorem canonicalMatch7_156 :
    canonicalPose7_156.boxKey 188160 (referenceBox7 (!canonicalBox7_156.bump)) = canonicalBox7_156 := by decide +kernel

theorem canonicalDecode7_156 : canonicalBox7_156.toKeyData 188160 = keys7Chunk4.get ⟨28, by decide⟩ := by
  change canonicalBox7_156.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_156 : keySolid (keys7Chunk4.get ⟨28, by decide⟩) = canonicalPose7_156.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_156 (box := canonicalBox7_156) (k := keys7Chunk4.get ⟨28, by decide⟩) (canonicalMatch7_156) (canonicalDecode7_156)

def canonicalPose7_157 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, false, true, true], ![0, 0, 1, 0, 0, 2, 2]⟩
def canonicalBox7_157 : BoxKey 7 :=
  ⟨![100800, 134400, 315840, 120960, 0, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 316240, 121380, 560, 261632, 268310], false⟩

theorem canonicalMatch7_157 :
    canonicalPose7_157.boxKey 188160 (referenceBox7 (!canonicalBox7_157.bump)) = canonicalBox7_157 := by decide +kernel

theorem canonicalDecode7_157 : canonicalBox7_157.toKeyData 188160 = keys7Chunk4.get ⟨29, by decide⟩ := by
  change canonicalBox7_157.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (146 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_157 : keySolid (keys7Chunk4.get ⟨29, by decide⟩) = canonicalPose7_157.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_157 (box := canonicalBox7_157) (k := keys7Chunk4.get ⟨29, by decide⟩) (canonicalMatch7_157) (canonicalDecode7_157)

def canonicalPose7_158 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, true, true, true, false, false, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_158 : BoxKey 7 :=
  ⟨![100800, 53760, 248640, 67200, 114240, 376320, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 53375, 248240, 66780, 114688, 376880, 268310], true⟩

theorem canonicalMatch7_158 :
    canonicalPose7_158.boxKey 188160 (referenceBox7 (!canonicalBox7_158.bump)) = canonicalBox7_158 := by decide +kernel

theorem canonicalDecode7_158 : canonicalBox7_158.toKeyData 188160 = keys7Chunk4.get ⟨30, by decide⟩ := by
  change canonicalBox7_158.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (37 / 28), (5 / 14), (17 / 28), 2, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (673 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_158 : keySolid (keys7Chunk4.get ⟨30, by decide⟩) = canonicalPose7_158.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_158 (box := canonicalBox7_158) (k := keys7Chunk4.get ⟨30, by decide⟩) (canonicalMatch7_158) (canonicalDecode7_158)

def canonicalPose7_159 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, true, true, true, false, true, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_159 : BoxKey 7 :=
  ⟨![114240, 67200, 248640, 53760, 100800, 268800, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 66780, 248240, 53375, 101360, 268310, 375760], false⟩

theorem canonicalMatch7_159 :
    canonicalPose7_159.boxKey 188160 (referenceBox7 (!canonicalBox7_159.bump)) = canonicalBox7_159 := by decide +kernel

theorem canonicalDecode7_159 : canonicalBox7_159.toKeyData 188160 = keys7Chunk4.get ⟨31, by decide⟩ := by
  change canonicalBox7_159.toKeyData 188160 = ⟨![(17 / 28), (5 / 14), (37 / 28), (2 / 7), (15 / 28), (10 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_159 : keySolid (keys7Chunk4.get ⟨31, by decide⟩) = canonicalPose7_159.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_159 (box := canonicalBox7_159) (k := keys7Chunk4.get ⟨31, by decide⟩) (canonicalMatch7_159) (canonicalDecode7_159)

theorem keys7Chunk4_canonical : ∀ k ∈ keys7Chunk4,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk4, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_128, canonicalSolid7_128⟩
  · exact ⟨canonicalPose7_129, canonicalSolid7_129⟩
  · exact ⟨canonicalPose7_130, canonicalSolid7_130⟩
  · exact ⟨canonicalPose7_131, canonicalSolid7_131⟩
  · exact ⟨canonicalPose7_132, canonicalSolid7_132⟩
  · exact ⟨canonicalPose7_133, canonicalSolid7_133⟩
  · exact ⟨canonicalPose7_134, canonicalSolid7_134⟩
  · exact ⟨canonicalPose7_135, canonicalSolid7_135⟩
  · exact ⟨canonicalPose7_136, canonicalSolid7_136⟩
  · exact ⟨canonicalPose7_137, canonicalSolid7_137⟩
  · exact ⟨canonicalPose7_138, canonicalSolid7_138⟩
  · exact ⟨canonicalPose7_139, canonicalSolid7_139⟩
  · exact ⟨canonicalPose7_140, canonicalSolid7_140⟩
  · exact ⟨canonicalPose7_141, canonicalSolid7_141⟩
  · exact ⟨canonicalPose7_142, canonicalSolid7_142⟩
  · exact ⟨canonicalPose7_143, canonicalSolid7_143⟩
  · exact ⟨canonicalPose7_144, canonicalSolid7_144⟩
  · exact ⟨canonicalPose7_145, canonicalSolid7_145⟩
  · exact ⟨canonicalPose7_146, canonicalSolid7_146⟩
  · exact ⟨canonicalPose7_147, canonicalSolid7_147⟩
  · exact ⟨canonicalPose7_148, canonicalSolid7_148⟩
  · exact ⟨canonicalPose7_149, canonicalSolid7_149⟩
  · exact ⟨canonicalPose7_150, canonicalSolid7_150⟩
  · exact ⟨canonicalPose7_151, canonicalSolid7_151⟩
  · exact ⟨canonicalPose7_152, canonicalSolid7_152⟩
  · exact ⟨canonicalPose7_153, canonicalSolid7_153⟩
  · exact ⟨canonicalPose7_154, canonicalSolid7_154⟩
  · exact ⟨canonicalPose7_155, canonicalSolid7_155⟩
  · exact ⟨canonicalPose7_156, canonicalSolid7_156⟩
  · exact ⟨canonicalPose7_157, canonicalSolid7_157⟩
  · exact ⟨canonicalPose7_158, canonicalSolid7_158⟩
  · exact ⟨canonicalPose7_159, canonicalSolid7_159⟩

#print axioms keys7Chunk4_canonical

end SparseMonotiles.Canonical
