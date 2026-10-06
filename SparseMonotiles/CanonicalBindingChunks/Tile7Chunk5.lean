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

def canonicalPose7_160 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, false, false, false, false, false, false], ![0, 0, 1, 0, 1, 0, 0]⟩
def canonicalBox7_160 : BoxKey 7 :=
  ⟨![0, 114240, 309120, 127680, 322560, 100800, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![-560, 114688, 309540, 128080, 322945, 101360, 108010], true⟩

theorem canonicalMatch7_160 :
    canonicalPose7_160.boxKey 188160 (referenceBox7 (!canonicalBox7_160.bump)) = canonicalBox7_160 := by decide +kernel

theorem canonicalDecode7_160 : canonicalBox7_160.toKeyData 188160 = keys7Chunk5.get ⟨0, by decide⟩ := by
  change canonicalBox7_160.toKeyData 188160 = ⟨![0, (17 / 28), (23 / 14), (19 / 28), (12 / 7), (15 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(-1 / 336), (64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_160 : keySolid (keys7Chunk5.get ⟨0, by decide⟩) = canonicalPose7_160.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_160 (box := canonicalBox7_160) (k := keys7Chunk5.get ⟨0, by decide⟩) (canonicalMatch7_160) (canonicalDecode7_160)

def canonicalPose7_161 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, true, true, true, false, false], ![0, 0, 2, 1, 2, 0, 0]⟩
def canonicalBox7_161 : BoxKey 7 :=
  ⟨![114240, 0, 255360, 60480, 241920, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 560, 254940, 60080, 241535, 101360, 108010], false⟩

theorem canonicalMatch7_161 :
    canonicalPose7_161.boxKey 188160 (referenceBox7 (!canonicalBox7_161.bump)) = canonicalBox7_161 := by decide +kernel

theorem canonicalDecode7_161 : canonicalBox7_161.toKeyData 188160 = keys7Chunk5.get ⟨1, by decide⟩ := by
  change canonicalBox7_161.toKeyData 188160 = ⟨![(17 / 28), 0, (19 / 14), (9 / 28), (9 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (1 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_161 : keySolid (keys7Chunk5.get ⟨1, by decide⟩) = canonicalPose7_161.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_161 (box := canonicalBox7_161) (k := keys7Chunk5.get ⟨1, by decide⟩) (canonicalMatch7_161) (canonicalDecode7_161)

def canonicalPose7_162 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, true, false, true, false, true], ![1, 0, 2, 0, 2, 0, 1]⟩
def canonicalBox7_162 : BoxKey 7 :=
  ⟨![60480, 120960, 376320, 114240, 268800, 100800, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, 375760, 114688, 268310, 101360, 53375], false⟩

theorem canonicalMatch7_162 :
    canonicalPose7_162.boxKey 188160 (referenceBox7 (!canonicalBox7_162.bump)) = canonicalBox7_162 := by decide +kernel

theorem canonicalDecode7_162 : canonicalBox7_162.toKeyData 188160 = keys7Chunk5.get ⟨2, by decide⟩ := by
  change canonicalBox7_162.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_162 : keySolid (keys7Chunk5.get ⟨2, by decide⟩) = canonicalPose7_162.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_162 (box := canonicalBox7_162) (k := keys7Chunk5.get ⟨2, by decide⟩) (canonicalMatch7_162) (canonicalDecode7_162)

def canonicalPose7_163 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, false, true, false, false, false], ![0, 0, 1, 0, 1, 0, 0]⟩
def canonicalBox7_163 : BoxKey 7 :=
  ⟨![100800, 107520, 302400, 0, 309120, 127680, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 302848, -560, 309540, 128080, 134785], true⟩

theorem canonicalMatch7_163 :
    canonicalPose7_163.boxKey 188160 (referenceBox7 (!canonicalBox7_163.bump)) = canonicalBox7_163 := by decide +kernel

theorem canonicalDecode7_163 : canonicalBox7_163.toKeyData 188160 = keys7Chunk5.get ⟨3, by decide⟩ := by
  change canonicalBox7_163.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (45 / 28), 0, (23 / 14), (19 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (169 / 105), (-1 / 336), (737 / 448), (1601 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_163 : keySolid (keys7Chunk5.get ⟨3, by decide⟩) = canonicalPose7_163.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_163 (box := canonicalBox7_163) (k := keys7Chunk5.get ⟨3, by decide⟩) (canonicalMatch7_163) (canonicalDecode7_163)

def canonicalPose7_164 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, false, false, false, false], ![0, 0, 1, 0, 1, 0, 0]⟩
def canonicalBox7_164 : BoxKey 7 :=
  ⟨![134400, 127680, 309120, 0, 302400, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 128080, 309540, 560, 302848, 108010, 101360], false⟩

theorem canonicalMatch7_164 :
    canonicalPose7_164.boxKey 188160 (referenceBox7 (!canonicalBox7_164.bump)) = canonicalBox7_164 := by decide +kernel

theorem canonicalDecode7_164 : canonicalBox7_164.toKeyData 188160 = keys7Chunk5.get ⟨4, by decide⟩ := by
  change canonicalBox7_164.toKeyData 188160 = ⟨![(5 / 7), (19 / 28), (23 / 14), 0, (45 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (1601 / 2352), (737 / 448), (1 / 336), (169 / 105), (1543 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_164 : keySolid (keys7Chunk5.get ⟨4, by decide⟩) = canonicalPose7_164.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_164 (box := canonicalBox7_164) (k := keys7Chunk5.get ⟨4, by decide⟩) (canonicalMatch7_164) (canonicalDecode7_164)

def canonicalPose7_165 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, true, false, false, false, true], ![1, 0, 2, 0, 2, 0, 1]⟩
def canonicalBox7_165 : BoxKey 7 :=
  ⟨![53760, 100800, 268800, 114240, 376320, 120960, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 101360, 268310, 114688, 376880, 121380, 60080], true⟩

theorem canonicalMatch7_165 :
    canonicalPose7_165.boxKey 188160 (referenceBox7 (!canonicalBox7_165.bump)) = canonicalBox7_165 := by decide +kernel

theorem canonicalDecode7_165 : canonicalBox7_165.toKeyData 188160 = keys7Chunk5.get ⟨5, by decide⟩ := by
  change canonicalBox7_165.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (9 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (289 / 448), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_165 : keySolid (keys7Chunk5.get ⟨5, by decide⟩) = canonicalPose7_165.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_165 (box := canonicalBox7_165) (k := keys7Chunk5.get ⟨5, by decide⟩) (canonicalMatch7_165) (canonicalDecode7_165)

def canonicalPose7_166 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, true, true, true, true, false], ![0, 0, 2, 1, 2, 0, 0]⟩
def canonicalBox7_166 : BoxKey 7 :=
  ⟨![107520, 100800, 241920, 60480, 255360, 0, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 241535, 60080, 254940, -560, 114688], true⟩

theorem canonicalMatch7_166 :
    canonicalPose7_166.boxKey 188160 (referenceBox7 (!canonicalBox7_166.bump)) = canonicalBox7_166 := by decide +kernel

theorem canonicalDecode7_166 : canonicalBox7_166.toKeyData 188160 = keys7Chunk5.get ⟨6, by decide⟩ := by
  change canonicalBox7_166.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (9 / 7), (9 / 28), (19 / 14), 0, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_166 : keySolid (keys7Chunk5.get ⟨6, by decide⟩) = canonicalPose7_166.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_166 (box := canonicalBox7_166) (k := keys7Chunk5.get ⟨6, by decide⟩) (canonicalMatch7_166) (canonicalDecode7_166)

def canonicalPose7_167 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, false, false, false, false, false, false], ![0, 0, 1, 0, 1, 0, 0]⟩
def canonicalBox7_167 : BoxKey 7 :=
  ⟨![107520, 100800, 322560, 127680, 309120, 114240, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 101360, 322945, 128080, 309540, 114688, 560], false⟩

theorem canonicalMatch7_167 :
    canonicalPose7_167.boxKey 188160 (referenceBox7 (!canonicalBox7_167.bump)) = canonicalBox7_167 := by decide +kernel

theorem canonicalDecode7_167 : canonicalBox7_167.toKeyData 188160 = keys7Chunk5.get ⟨7, by decide⟩ := by
  change canonicalBox7_167.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (12 / 7), (19 / 28), (23 / 14), (17 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_167 : keySolid (keys7Chunk5.get ⟨7, by decide⟩) = canonicalPose7_167.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_167 (box := canonicalBox7_167) (k := keys7Chunk5.get ⟨7, by decide⟩) (canonicalMatch7_167) (canonicalDecode7_167)

def canonicalPose7_168 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, false, true, true, true, true, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_168 : BoxKey 7 :=
  ⟨![0, 107520, 275520, 53760, 248640, 67200, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![-560, 108010, 274960, 53375, 248240, 66780, 261632], true⟩

theorem canonicalMatch7_168 :
    canonicalPose7_168.boxKey 188160 (referenceBox7 (!canonicalBox7_168.bump)) = canonicalBox7_168 := by decide +kernel

theorem canonicalDecode7_168 : canonicalBox7_168.toKeyData 188160 = keys7Chunk5.get ⟨8, by decide⟩ := by
  change canonicalBox7_168.toKeyData 188160 = ⟨![0, (4 / 7), (41 / 28), (2 / 7), (37 / 28), (5 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(-1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_168 : keySolid (keys7Chunk5.get ⟨8, by decide⟩) = canonicalPose7_168.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_168 (box := canonicalBox7_168) (k := keys7Chunk5.get ⟨8, by decide⟩) (canonicalMatch7_168) (canonicalDecode7_168)

def canonicalPose7_169 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, false, true, true, true, true, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_169 : BoxKey 7 :=
  ⟨![107520, 0, 262080, 67200, 248640, 53760, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, 560, 261632, 66780, 248240, 53375, 274960], false⟩

theorem canonicalMatch7_169 :
    canonicalPose7_169.boxKey 188160 (referenceBox7 (!canonicalBox7_169.bump)) = canonicalBox7_169 := by decide +kernel

theorem canonicalDecode7_169 : canonicalBox7_169.toKeyData 188160 = keys7Chunk5.get ⟨9, by decide⟩ := by
  change canonicalBox7_169.toKeyData 188160 = ⟨![(4 / 7), 0, (39 / 28), (5 / 14), (37 / 28), (2 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (1 / 336), (146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_169 : keySolid (keys7Chunk5.get ⟨9, by decide⟩) = canonicalPose7_169.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_169 (box := canonicalBox7_169) (k := keys7Chunk5.get ⟨9, by decide⟩) (canonicalMatch7_169) (canonicalDecode7_169)

def canonicalPose7_170 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, false, false, false, false, true], ![0, 0, 2, 0, 1, 0, 2]⟩
def canonicalBox7_170 : BoxKey 7 :=
  ⟨![107520, 114240, 376320, 120960, 315840, 134400, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, 376880, 121380, 316240, 134785, 274960], true⟩

theorem canonicalMatch7_170 :
    canonicalPose7_170.boxKey 188160 (referenceBox7 (!canonicalBox7_170.bump)) = canonicalBox7_170 := by decide +kernel

theorem canonicalDecode7_170 : canonicalBox7_170.toKeyData 188160 = keys7Chunk5.get ⟨10, by decide⟩ := by
  change canonicalBox7_170.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 2, (9 / 14), (47 / 28), (5 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_170 : keySolid (keys7Chunk5.get ⟨10, by decide⟩) = canonicalPose7_170.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_170 (box := canonicalBox7_170) (k := keys7Chunk5.get ⟨10, by decide⟩) (canonicalMatch7_170) (canonicalDecode7_170)

def canonicalPose7_171 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, true, true, false, true], ![1, 1, 2, 0, 2, 0, 2]⟩
def canonicalBox7_171 : BoxKey 7 :=
  ⟨![53760, 60480, 255360, 0, 262080, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 60080, 254940, -560, 261632, 108010, 274960], true⟩

theorem canonicalMatch7_171 :
    canonicalPose7_171.boxKey 188160 (referenceBox7 (!canonicalBox7_171.bump)) = canonicalBox7_171 := by decide +kernel

theorem canonicalDecode7_171 : canonicalBox7_171.toKeyData 188160 = keys7Chunk5.get ⟨11, by decide⟩ := by
  change canonicalBox7_171.toKeyData 188160 = ⟨![(2 / 7), (9 / 28), (19 / 14), 0, (39 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_171 : keySolid (keys7Chunk5.get ⟨11, by decide⟩) = canonicalPose7_171.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_171 (box := canonicalBox7_171) (k := keys7Chunk5.get ⟨11, by decide⟩) (canonicalMatch7_171) (canonicalDecode7_171)

def canonicalPose7_172 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, true, false, true, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_172 : BoxKey 7 :=
  ⟨![100800, 134400, 248640, 67200, 376320, 73920, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 248240, 66780, 376880, 73472, 268310], true⟩

theorem canonicalMatch7_172 :
    canonicalPose7_172.boxKey 188160 (referenceBox7 (!canonicalBox7_172.bump)) = canonicalBox7_172 := by decide +kernel

theorem canonicalDecode7_172 : canonicalBox7_172.toKeyData 188160 = keys7Chunk5.get ⟨12, by decide⟩ := by
  change canonicalBox7_172.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (37 / 28), (5 / 14), 2, (11 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448), (673 / 336), (41 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_172 : keySolid (keys7Chunk5.get ⟨12, by decide⟩) = canonicalPose7_172.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_172 (box := canonicalBox7_172) (k := keys7Chunk5.get ⟨12, by decide⟩) (canonicalMatch7_172) (canonicalDecode7_172)

def canonicalPose7_173 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, true, true, true, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_173 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 73920, 376320, 67200, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 73472, 375760, 66780, 248240], false⟩

theorem canonicalMatch7_173 :
    canonicalPose7_173.boxKey 188160 (referenceBox7 (!canonicalBox7_173.bump)) = canonicalBox7_173 := by decide +kernel

theorem canonicalDecode7_173 : canonicalBox7_173.toKeyData 188160 = keys7Chunk5.get ⟨13, by decide⟩ := by
  change canonicalBox7_173.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (11 / 28), 2, (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105), (671 / 336), (159 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_173 : keySolid (keys7Chunk5.get ⟨13, by decide⟩) = canonicalPose7_173.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_173 (box := canonicalBox7_173) (k := keys7Chunk5.get ⟨13, by decide⟩) (canonicalMatch7_173) (canonicalDecode7_173)

def canonicalPose7_174 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, false, true, false, true], ![1, 1, 2, 0, 2, 0, 2]⟩
def canonicalBox7_174 : BoxKey 7 :=
  ⟨![60480, 53760, 275520, 107520, 262080, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 53375, 274960, 108010, 261632, 560, 254940], false⟩

theorem canonicalMatch7_174 :
    canonicalPose7_174.boxKey 188160 (referenceBox7 (!canonicalBox7_174.bump)) = canonicalBox7_174 := by decide +kernel

theorem canonicalDecode7_174 : canonicalBox7_174.toKeyData 188160 = keys7Chunk5.get ⟨14, by decide⟩ := by
  change canonicalBox7_174.toKeyData 188160 = ⟨![(9 / 28), (2 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_174 : keySolid (keys7Chunk5.get ⟨14, by decide⟩) = canonicalPose7_174.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_174 (box := canonicalBox7_174) (k := keys7Chunk5.get ⟨14, by decide⟩) (canonicalMatch7_174) (canonicalDecode7_174)

def canonicalPose7_175 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, false, false, false, true], ![0, 0, 2, 0, 1, 0, 2]⟩
def canonicalBox7_175 : BoxKey 7 :=
  ⟨![114240, 107520, 275520, 134400, 315840, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 274960, 134785, 316240, 121380, 375760], false⟩

theorem canonicalMatch7_175 :
    canonicalPose7_175.boxKey 188160 (referenceBox7 (!canonicalBox7_175.bump)) = canonicalBox7_175 := by decide +kernel

theorem canonicalDecode7_175 : canonicalBox7_175.toKeyData 188160 = keys7Chunk5.get ⟨15, by decide⟩ := by
  change canonicalBox7_175.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (41 / 28), (5 / 7), (47 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_175 : keySolid (keys7Chunk5.get ⟨15, by decide⟩) = canonicalPose7_175.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_175 (box := canonicalBox7_175) (k := keys7Chunk5.get ⟨15, by decide⟩) (canonicalMatch7_175) (canonicalDecode7_175)

def canonicalPose7_176 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, false, true, true, true, false], ![0, 0, 1, 1, 2, 2, 0]⟩
def canonicalBox7_176 : BoxKey 7 :=
  ⟨![0, 120960, 315840, 53760, 275520, 268800, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 121380, 316240, 53375, 274960, 268310, 114688], false⟩

theorem canonicalMatch7_176 :
    canonicalPose7_176.boxKey 188160 (referenceBox7 (!canonicalBox7_176.bump)) = canonicalBox7_176 := by decide +kernel

theorem canonicalDecode7_176 : canonicalBox7_176.toKeyData 188160 = keys7Chunk5.get ⟨16, by decide⟩ := by
  change canonicalBox7_176.toKeyData 188160 = ⟨![0, (9 / 14), (47 / 28), (2 / 7), (41 / 28), (10 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_176 : keySolid (keys7Chunk5.get ⟨16, by decide⟩) = canonicalPose7_176.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_176 (box := canonicalBox7_176) (k := keys7Chunk5.get ⟨16, by decide⟩) (canonicalMatch7_176) (canonicalDecode7_176)

def canonicalPose7_177 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, true, false, true, true, true], ![0, 0, 2, 0, 2, 2, 1]⟩
def canonicalBox7_177 : BoxKey 7 :=
  ⟨![120960, 0, 262080, 107520, 275520, 241920, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 560, 261632, 108010, 274960, 241535, 60080], false⟩

theorem canonicalMatch7_177 :
    canonicalPose7_177.boxKey 188160 (referenceBox7 (!canonicalBox7_177.bump)) = canonicalBox7_177 := by decide +kernel

theorem canonicalDecode7_177 : canonicalBox7_177.toKeyData 188160 = keys7Chunk5.get ⟨17, by decide⟩ := by
  change canonicalBox7_177.toKeyData 188160 = ⟨![(9 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (9 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_177 : keySolid (keys7Chunk5.get ⟨17, by decide⟩) = canonicalPose7_177.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_177 (box := canonicalBox7_177) (k := keys7Chunk5.get ⟨17, by decide⟩) (canonicalMatch7_177) (canonicalDecode7_177)

def canonicalPose7_178 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, false, false, false, true, false, false], ![1, 0, 2, 0, 2, 1, 0]⟩
def canonicalBox7_178 : BoxKey 7 :=
  ⟨![67200, 114240, 376320, 107520, 275520, 322560, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 114688, 376880, 108010, 274960, 322945, 128080], true⟩

theorem canonicalMatch7_178 :
    canonicalPose7_178.boxKey 188160 (referenceBox7 (!canonicalBox7_178.bump)) = canonicalBox7_178 := by decide +kernel

theorem canonicalDecode7_178 : canonicalBox7_178.toKeyData 188160 = keys7Chunk5.get ⟨18, by decide⟩ := by
  change canonicalBox7_178.toKeyData 188160 = ⟨![(5 / 14), (17 / 28), 2, (4 / 7), (41 / 28), (12 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (64 / 105), (673 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_178 : keySolid (keys7Chunk5.get ⟨18, by decide⟩) = canonicalPose7_178.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_178 (box := canonicalBox7_178) (k := keys7Chunk5.get ⟨18, by decide⟩) (canonicalMatch7_178) (canonicalDecode7_178)

def canonicalPose7_179 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, false, true, false, true, false, false], ![1, 0, 2, 0, 2, 1, 0]⟩
def canonicalBox7_179 : BoxKey 7 :=
  ⟨![53760, 100800, 268800, 0, 262080, 309120, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 101360, 268310, 560, 261632, 309540, 128080], false⟩

theorem canonicalMatch7_179 :
    canonicalPose7_179.boxKey 188160 (referenceBox7 (!canonicalBox7_179.bump)) = canonicalBox7_179 := by decide +kernel

theorem canonicalDecode7_179 : canonicalBox7_179.toKeyData 188160 = keys7Chunk5.get ⟨19, by decide⟩ := by
  change canonicalBox7_179.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (10 / 7), 0, (39 / 28), (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (3833 / 2688), (1 / 336), (146 / 105), (737 / 448), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_179 : keySolid (keys7Chunk5.get ⟨19, by decide⟩) = canonicalPose7_179.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_179 (box := canonicalBox7_179) (k := keys7Chunk5.get ⟨19, by decide⟩) (canonicalMatch7_179) (canonicalDecode7_179)

def canonicalPose7_180 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, false, false, true, true], ![0, 0, 2, 0, 2, 2, 1]⟩
def canonicalBox7_180 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 114240, 376320, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 114688, 376880, 254940, 60080], true⟩

theorem canonicalMatch7_180 :
    canonicalPose7_180.boxKey 188160 (referenceBox7 (!canonicalBox7_180.bump)) = canonicalBox7_180 := by decide +kernel

theorem canonicalDecode7_180 : canonicalBox7_180.toKeyData 188160 = keys7Chunk5.get ⟨20, by decide⟩ := by
  change canonicalBox7_180.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_180 : keySolid (keys7Chunk5.get ⟨20, by decide⟩) = canonicalPose7_180.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_180 (box := canonicalBox7_180) (k := keys7Chunk5.get ⟨20, by decide⟩) (canonicalMatch7_180) (canonicalDecode7_180)

def canonicalPose7_181 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, true, true, false, false], ![0, 0, 1, 1, 2, 2, 0]⟩
def canonicalBox7_181 : BoxKey 7 :=
  ⟨![107520, 100800, 322560, 60480, 255360, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 322945, 60080, 254940, 376880, 114688], true⟩

theorem canonicalMatch7_181 :
    canonicalPose7_181.boxKey 188160 (referenceBox7 (!canonicalBox7_181.bump)) = canonicalBox7_181 := by decide +kernel

theorem canonicalDecode7_181 : canonicalBox7_181.toKeyData 188160 = keys7Chunk5.get ⟨21, by decide⟩ := by
  change canonicalBox7_181.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (12 / 7), (9 / 28), (19 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352), (607 / 448), (673 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_181 : keySolid (keys7Chunk5.get ⟨21, by decide⟩) = canonicalPose7_181.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_181 (box := canonicalBox7_181) (k := keys7Chunk5.get ⟨21, by decide⟩) (canonicalMatch7_181) (canonicalDecode7_181)

def canonicalPose7_182 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, false, true, false, true], ![1, 0, 2, 0, 2, 1, 0]⟩
def canonicalBox7_182 : BoxKey 7 :=
  ⟨![73920, 107520, 275520, 134400, 248640, 309120, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 108010, 274960, 134785, 248240, 309540, -560], true⟩

theorem canonicalMatch7_182 :
    canonicalPose7_182.boxKey 188160 (referenceBox7 (!canonicalBox7_182.bump)) = canonicalBox7_182 := by decide +kernel

theorem canonicalDecode7_182 : canonicalBox7_182.toKeyData 188160 = keys7Chunk5.get ⟨22, by decide⟩ := by
  change canonicalBox7_182.toKeyData 188160 = ⟨![(11 / 28), (4 / 7), (41 / 28), (5 / 7), (37 / 28), (23 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_182 : keySolid (keys7Chunk5.get ⟨22, by decide⟩) = canonicalPose7_182.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_182 (box := canonicalBox7_182) (k := keys7Chunk5.get ⟨22, by decide⟩) (canonicalMatch7_182) (canonicalDecode7_182)

def canonicalPose7_183 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, true, false, true, false, false], ![1, 0, 2, 0, 2, 1, 0]⟩
def canonicalBox7_183 : BoxKey 7 :=
  ⟨![67200, 127680, 241920, 100800, 268800, 302400, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 128080, 241535, 101360, 268310, 302848, 560], false⟩

theorem canonicalMatch7_183 :
    canonicalPose7_183.boxKey 188160 (referenceBox7 (!canonicalBox7_183.bump)) = canonicalBox7_183 := by decide +kernel

theorem canonicalDecode7_183 : canonicalBox7_183.toKeyData 188160 = keys7Chunk5.get ⟨23, by decide⟩ := by
  change canonicalBox7_183.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (9 / 7), (15 / 28), (10 / 7), (45 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_183 : keySolid (keys7Chunk5.get ⟨23, by decide⟩) = canonicalPose7_183.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_183 (box := canonicalBox7_183) (k := keys7Chunk5.get ⟨23, by decide⟩) (canonicalMatch7_183) (canonicalDecode7_183)

def canonicalPose7_184 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, true, true, true, true], ![0, 0, 1, 1, 2, 2, 2]⟩
def canonicalBox7_184 : BoxKey 7 :=
  ⟨![0, 120960, 315840, 53760, 275520, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 121380, 316240, 53375, 274960, 268310, 261632], true⟩

theorem canonicalMatch7_184 :
    canonicalPose7_184.boxKey 188160 (referenceBox7 (!canonicalBox7_184.bump)) = canonicalBox7_184 := by decide +kernel

theorem canonicalDecode7_184 : canonicalBox7_184.toKeyData 188160 = keys7Chunk5.get ⟨24, by decide⟩ := by
  change canonicalBox7_184.toKeyData 188160 = ⟨![0, (9 / 14), (47 / 28), (2 / 7), (41 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_184 : keySolid (keys7Chunk5.get ⟨24, by decide⟩) = canonicalPose7_184.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_184 (box := canonicalBox7_184) (k := keys7Chunk5.get ⟨24, by decide⟩) (canonicalMatch7_184) (canonicalDecode7_184)

def canonicalPose7_185 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, true, false, true, true, false], ![0, 0, 2, 0, 2, 2, 1]⟩
def canonicalBox7_185 : BoxKey 7 :=
  ⟨![120960, 0, 262080, 107520, 275520, 241920, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, -560, 261632, 108010, 274960, 241535, 316240], true⟩

theorem canonicalMatch7_185 :
    canonicalPose7_185.boxKey 188160 (referenceBox7 (!canonicalBox7_185.bump)) = canonicalBox7_185 := by decide +kernel

theorem canonicalDecode7_185 : canonicalBox7_185.toKeyData 188160 = keys7Chunk5.get ⟨25, by decide⟩ := by
  change canonicalBox7_185.toKeyData 188160 = ⟨![(9 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (9 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_185 : keySolid (keys7Chunk5.get ⟨25, by decide⟩) = canonicalPose7_185.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_185 (box := canonicalBox7_185) (k := keys7Chunk5.get ⟨25, by decide⟩) (canonicalMatch7_185) (canonicalDecode7_185)

def canonicalPose7_186 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, false, true, false, true, false, true], ![1, 0, 2, 0, 2, 1, 2]⟩
def canonicalBox7_186 : BoxKey 7 :=
  ⟨![67200, 114240, 376320, 107520, 275520, 322560, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 114688, 375760, 108010, 274960, 322945, 248240], false⟩

theorem canonicalMatch7_186 :
    canonicalPose7_186.boxKey 188160 (referenceBox7 (!canonicalBox7_186.bump)) = canonicalBox7_186 := by decide +kernel

theorem canonicalDecode7_186 : canonicalBox7_186.toKeyData 188160 = keys7Chunk5.get ⟨26, by decide⟩ := by
  change canonicalBox7_186.toKeyData 188160 = ⟨![(5 / 14), (17 / 28), 2, (4 / 7), (41 / 28), (12 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (64 / 105), (671 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_186 : keySolid (keys7Chunk5.get ⟨26, by decide⟩) = canonicalPose7_186.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_186 (box := canonicalBox7_186) (k := keys7Chunk5.get ⟨26, by decide⟩) (canonicalMatch7_186) (canonicalDecode7_186)

def canonicalPose7_187 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, false, true, true, true, false, true], ![1, 0, 2, 0, 2, 1, 2]⟩
def canonicalBox7_187 : BoxKey 7 :=
  ⟨![53760, 100800, 268800, 0, 262080, 309120, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 101360, 268310, -560, 261632, 309540, 248240], true⟩

theorem canonicalMatch7_187 :
    canonicalPose7_187.boxKey 188160 (referenceBox7 (!canonicalBox7_187.bump)) = canonicalBox7_187 := by decide +kernel

theorem canonicalDecode7_187 : canonicalBox7_187.toKeyData 188160 = keys7Chunk5.get ⟨27, by decide⟩ := by
  change canonicalBox7_187.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (10 / 7), 0, (39 / 28), (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (3833 / 2688), (-1 / 336), (146 / 105), (737 / 448), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_187 : keySolid (keys7Chunk5.get ⟨27, by decide⟩) = canonicalPose7_187.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_187 (box := canonicalBox7_187) (k := keys7Chunk5.get ⟨27, by decide⟩) (canonicalMatch7_187) (canonicalDecode7_187)

def canonicalPose7_188 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, false, true, true, false], ![0, 0, 2, 0, 2, 2, 1]⟩
def canonicalBox7_188 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 114240, 376320, 255360, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 114688, 375760, 254940, 316240], false⟩

theorem canonicalMatch7_188 :
    canonicalPose7_188.boxKey 188160 (referenceBox7 (!canonicalBox7_188.bump)) = canonicalBox7_188 := by decide +kernel

theorem canonicalDecode7_188 : canonicalBox7_188.toKeyData 188160 = keys7Chunk5.get ⟨28, by decide⟩ := by
  change canonicalBox7_188.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (671 / 336), (607 / 448), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_188 : keySolid (keys7Chunk5.get ⟨28, by decide⟩) = canonicalPose7_188.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_188 (box := canonicalBox7_188) (k := keys7Chunk5.get ⟨28, by decide⟩) (canonicalMatch7_188) (canonicalDecode7_188)

def canonicalPose7_189 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, true, true, true, true], ![0, 0, 1, 1, 2, 2, 2]⟩
def canonicalBox7_189 : BoxKey 7 :=
  ⟨![107520, 100800, 322560, 60480, 255360, 376320, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 322945, 60080, 254940, 375760, 261632], false⟩

theorem canonicalMatch7_189 :
    canonicalPose7_189.boxKey 188160 (referenceBox7 (!canonicalBox7_189.bump)) = canonicalBox7_189 := by decide +kernel

theorem canonicalDecode7_189 : canonicalBox7_189.toKeyData 188160 = keys7Chunk5.get ⟨29, by decide⟩ := by
  change canonicalBox7_189.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (12 / 7), (9 / 28), (19 / 14), 2, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352), (607 / 448), (671 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_189 : keySolid (keys7Chunk5.get ⟨29, by decide⟩) = canonicalPose7_189.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_189 (box := canonicalBox7_189) (k := keys7Chunk5.get ⟨29, by decide⟩) (canonicalMatch7_189) (canonicalDecode7_189)

def canonicalPose7_190 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, false, true, false, true], ![1, 0, 2, 0, 2, 1, 2]⟩
def canonicalBox7_190 : BoxKey 7 :=
  ⟨![73920, 107520, 275520, 134400, 248640, 309120, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 108010, 274960, 134785, 248240, 309540, 375760], false⟩

theorem canonicalMatch7_190 :
    canonicalPose7_190.boxKey 188160 (referenceBox7 (!canonicalBox7_190.bump)) = canonicalBox7_190 := by decide +kernel

theorem canonicalDecode7_190 : canonicalBox7_190.toKeyData 188160 = keys7Chunk5.get ⟨30, by decide⟩ := by
  change canonicalBox7_190.toKeyData 188160 = ⟨![(11 / 28), (4 / 7), (41 / 28), (5 / 7), (37 / 28), (23 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_190 : keySolid (keys7Chunk5.get ⟨30, by decide⟩) = canonicalPose7_190.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_190 (box := canonicalBox7_190) (k := keys7Chunk5.get ⟨30, by decide⟩) (canonicalMatch7_190) (canonicalDecode7_190)

def canonicalPose7_191 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, true, false, true, false, false], ![1, 0, 2, 0, 2, 1, 2]⟩
def canonicalBox7_191 : BoxKey 7 :=
  ⟨![67200, 127680, 241920, 100800, 268800, 302400, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 128080, 241535, 101360, 268310, 302848, 376880], true⟩

theorem canonicalMatch7_191 :
    canonicalPose7_191.boxKey 188160 (referenceBox7 (!canonicalBox7_191.bump)) = canonicalBox7_191 := by decide +kernel

theorem canonicalDecode7_191 : canonicalBox7_191.toKeyData 188160 = keys7Chunk5.get ⟨31, by decide⟩ := by
  change canonicalBox7_191.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (9 / 7), (15 / 28), (10 / 7), (45 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_191 : keySolid (keys7Chunk5.get ⟨31, by decide⟩) = canonicalPose7_191.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_191 (box := canonicalBox7_191) (k := keys7Chunk5.get ⟨31, by decide⟩) (canonicalMatch7_191) (canonicalDecode7_191)

theorem keys7Chunk5_canonical : ∀ k ∈ keys7Chunk5,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk5, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_160, canonicalSolid7_160⟩
  · exact ⟨canonicalPose7_161, canonicalSolid7_161⟩
  · exact ⟨canonicalPose7_162, canonicalSolid7_162⟩
  · exact ⟨canonicalPose7_163, canonicalSolid7_163⟩
  · exact ⟨canonicalPose7_164, canonicalSolid7_164⟩
  · exact ⟨canonicalPose7_165, canonicalSolid7_165⟩
  · exact ⟨canonicalPose7_166, canonicalSolid7_166⟩
  · exact ⟨canonicalPose7_167, canonicalSolid7_167⟩
  · exact ⟨canonicalPose7_168, canonicalSolid7_168⟩
  · exact ⟨canonicalPose7_169, canonicalSolid7_169⟩
  · exact ⟨canonicalPose7_170, canonicalSolid7_170⟩
  · exact ⟨canonicalPose7_171, canonicalSolid7_171⟩
  · exact ⟨canonicalPose7_172, canonicalSolid7_172⟩
  · exact ⟨canonicalPose7_173, canonicalSolid7_173⟩
  · exact ⟨canonicalPose7_174, canonicalSolid7_174⟩
  · exact ⟨canonicalPose7_175, canonicalSolid7_175⟩
  · exact ⟨canonicalPose7_176, canonicalSolid7_176⟩
  · exact ⟨canonicalPose7_177, canonicalSolid7_177⟩
  · exact ⟨canonicalPose7_178, canonicalSolid7_178⟩
  · exact ⟨canonicalPose7_179, canonicalSolid7_179⟩
  · exact ⟨canonicalPose7_180, canonicalSolid7_180⟩
  · exact ⟨canonicalPose7_181, canonicalSolid7_181⟩
  · exact ⟨canonicalPose7_182, canonicalSolid7_182⟩
  · exact ⟨canonicalPose7_183, canonicalSolid7_183⟩
  · exact ⟨canonicalPose7_184, canonicalSolid7_184⟩
  · exact ⟨canonicalPose7_185, canonicalSolid7_185⟩
  · exact ⟨canonicalPose7_186, canonicalSolid7_186⟩
  · exact ⟨canonicalPose7_187, canonicalSolid7_187⟩
  · exact ⟨canonicalPose7_188, canonicalSolid7_188⟩
  · exact ⟨canonicalPose7_189, canonicalSolid7_189⟩
  · exact ⟨canonicalPose7_190, canonicalSolid7_190⟩
  · exact ⟨canonicalPose7_191, canonicalSolid7_191⟩

#print axioms keys7Chunk5_canonical

end SparseMonotiles.Canonical
