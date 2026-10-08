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

def canonicalPose7_96 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, false, true, true, false, true], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_96 : BoxKey 7 :=
  ⟨![0, 73920, 107520, 275520, 241920, 127680, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 73472, 108010, 274960, 241535, 128080, 66780], false⟩

theorem canonicalMatch7_96 :
    canonicalPose7_96.boxKey 188160 (referenceBox7 (!canonicalBox7_96.bump)) = canonicalBox7_96 := by decide +kernel

theorem canonicalDecode7_96 : canonicalBox7_96.toKeyData 188160 = keys7Chunk3.get ⟨0, by decide⟩ := by
  change canonicalBox7_96.toKeyData 188160 = ⟨![0, (11 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_96 : keySolid (keys7Chunk3.get ⟨0, by decide⟩) = canonicalPose7_96.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_96 (box := canonicalBox7_96) (k := keys7Chunk3.get ⟨0, by decide⟩) (canonicalMatch7_96) (canonicalDecode7_96)

def canonicalPose7_97 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, true, true, false, true], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_97 : BoxKey 7 :=
  ⟨![0, 67200, 127680, 241920, 275520, 107520, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 66780, 128080, 241535, 274960, 108010, 73472], true⟩

theorem canonicalMatch7_97 :
    canonicalPose7_97.boxKey 188160 (referenceBox7 (!canonicalBox7_97.bump)) = canonicalBox7_97 := by decide +kernel

theorem canonicalDecode7_97 : canonicalBox7_97.toKeyData 188160 = keys7Chunk3.get ⟨1, by decide⟩ := by
  change canonicalBox7_97.toKeyData 188160 = ⟨![0, (5 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_97 : keySolid (keys7Chunk3.get ⟨1, by decide⟩) = canonicalPose7_97.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_97 (box := canonicalBox7_97) (k := keys7Chunk3.get ⟨1, by decide⟩) (canonicalMatch7_97) (canonicalDecode7_97)

def canonicalPose7_98 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, false, false, false, false], ![0, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_98 : BoxKey 7 :=
  ⟨![114240, 0, 120960, 315840, 322560, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, -560, 121380, 316240, 322945, 101360, 108010], true⟩

theorem canonicalMatch7_98 :
    canonicalPose7_98.boxKey 188160 (referenceBox7 (!canonicalBox7_98.bump)) = canonicalBox7_98 := by decide +kernel

theorem canonicalDecode7_98 : canonicalBox7_98.toKeyData 188160 = keys7Chunk3.get ⟨2, by decide⟩ := by
  change canonicalBox7_98.toKeyData 188160 = ⟨![(17 / 28), 0, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_98 : keySolid (keys7Chunk3.get ⟨2, by decide⟩) = canonicalPose7_98.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_98 (box := canonicalBox7_98) (k := keys7Chunk3.get ⟨2, by decide⟩) (canonicalMatch7_98) (canonicalDecode7_98)

def canonicalPose7_99 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, true, true, true, false, false], ![1, 0, 0, 2, 2, 0, 0]⟩
def canonicalBox7_99 : BoxKey 7 :=
  ⟨![60480, 120960, 0, 262080, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, -560, 261632, 268310, 101360, 134785], true⟩

theorem canonicalMatch7_99 :
    canonicalPose7_99.boxKey 188160 (referenceBox7 (!canonicalBox7_99.bump)) = canonicalBox7_99 := by decide +kernel

theorem canonicalDecode7_99 : canonicalBox7_99.toKeyData 188160 = keys7Chunk3.get ⟨3, by decide⟩ := by
  change canonicalBox7_99.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (-1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_99 : keySolid (keys7Chunk3.get ⟨3, by decide⟩) = canonicalPose7_99.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_99 (box := canonicalBox7_99) (k := keys7Chunk3.get ⟨3, by decide⟩) (canonicalMatch7_99) (canonicalDecode7_99)

def canonicalPose7_100 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, true, false, true, true, false, true], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_100 : BoxKey 7 :=
  ⟨![127680, 67200, 114240, 376320, 268800, 100800, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 66780, 114688, 375760, 268310, 101360, 53375], false⟩

theorem canonicalMatch7_100 :
    canonicalPose7_100.boxKey 188160 (referenceBox7 (!canonicalBox7_100.bump)) = canonicalBox7_100 := by decide +kernel

theorem canonicalDecode7_100 : canonicalBox7_100.toKeyData 188160 = keys7Chunk3.get ⟨4, by decide⟩ := by
  change canonicalBox7_100.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (64 / 105), (671 / 336), (3833 / 2688), (181 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_100 : keySolid (keys7Chunk3.get ⟨4, by decide⟩) = canonicalPose7_100.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_100 (box := canonicalBox7_100) (k := keys7Chunk3.get ⟨4, by decide⟩) (canonicalMatch7_100) (canonicalDecode7_100)

def canonicalPose7_101 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, true, false, true, false, false, true], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_101 : BoxKey 7 :=
  ⟨![127680, 53760, 100800, 268800, 376320, 114240, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 53375, 101360, 268310, 376880, 114688, 66780], true⟩

theorem canonicalMatch7_101 :
    canonicalPose7_101.boxKey 188160 (referenceBox7 (!canonicalBox7_101.bump)) = canonicalBox7_101 := by decide +kernel

theorem canonicalDecode7_101 : canonicalBox7_101.toKeyData 188160 = keys7Chunk3.get ⟨5, by decide⟩ := by
  change canonicalBox7_101.toKeyData 188160 = ⟨![(19 / 28), (2 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (673 / 336), (64 / 105), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_101 : keySolid (keys7Chunk3.get ⟨5, by decide⟩) = canonicalPose7_101.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_101 (box := canonicalBox7_101) (k := keys7Chunk3.get ⟨5, by decide⟩) (canonicalMatch7_101) (canonicalDecode7_101)

def canonicalPose7_102 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, true, true, false, false], ![1, 0, 0, 2, 2, 0, 0]⟩
def canonicalBox7_102 : BoxKey 7 :=
  ⟨![60480, 134400, 100800, 268800, 262080, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 134785, 101360, 268310, 261632, 560, 121380], false⟩

theorem canonicalMatch7_102 :
    canonicalPose7_102.boxKey 188160 (referenceBox7 (!canonicalBox7_102.bump)) = canonicalBox7_102 := by decide +kernel

theorem canonicalDecode7_102 : canonicalBox7_102.toKeyData 188160 = keys7Chunk3.get ⟨6, by decide⟩ := by
  change canonicalBox7_102.toKeyData 188160 = ⟨![(9 / 28), (5 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (1 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_102 : keySolid (keys7Chunk3.get ⟨6, by decide⟩) = canonicalPose7_102.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_102 (box := canonicalBox7_102) (k := keys7Chunk3.get ⟨6, by decide⟩) (canonicalMatch7_102) (canonicalDecode7_102)

def canonicalPose7_103 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, false, false, false, false], ![0, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_103 : BoxKey 7 :=
  ⟨![114240, 107520, 100800, 322560, 315840, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 101360, 322945, 316240, 121380, 560], false⟩

theorem canonicalMatch7_103 :
    canonicalPose7_103.boxKey 188160 (referenceBox7 (!canonicalBox7_103.bump)) = canonicalBox7_103 := by decide +kernel

theorem canonicalDecode7_103 : canonicalBox7_103.toKeyData 188160 = keys7Chunk3.get ⟨7, by decide⟩ := by
  change canonicalBox7_103.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_103 : keySolid (keys7Chunk3.get ⟨7, by decide⟩) = canonicalPose7_103.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_103 (box := canonicalBox7_103) (k := keys7Chunk3.get ⟨7, by decide⟩) (canonicalMatch7_103) (canonicalDecode7_103)

def canonicalPose7_104 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, true, true, true, false, true], ![0, 0, 1, 2, 2, 0, 2]⟩
def canonicalBox7_104 : BoxKey 7 :=
  ⟨![0, 120960, 60480, 241920, 275520, 107520, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 121380, 60080, 241535, 274960, 108010, 261632], true⟩

theorem canonicalMatch7_104 :
    canonicalPose7_104.boxKey 188160 (referenceBox7 (!canonicalBox7_104.bump)) = canonicalBox7_104 := by decide +kernel

theorem canonicalDecode7_104 : canonicalBox7_104.toKeyData 188160 = keys7Chunk3.get ⟨8, by decide⟩ := by
  change canonicalBox7_104.toKeyData 188160 = ⟨![0, (9 / 14), (9 / 28), (9 / 7), (41 / 28), (4 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (289 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_104 : keySolid (keys7Chunk3.get ⟨8, by decide⟩) = canonicalPose7_104.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_104 (box := canonicalBox7_104) (k := keys7Chunk3.get ⟨8, by decide⟩) (canonicalMatch7_104) (canonicalDecode7_104)

def canonicalPose7_105 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, false, true, true, true, false], ![0, 0, 0, 2, 2, 1, 1]⟩
def canonicalBox7_105 : BoxKey 7 :=
  ⟨![120960, 0, 114240, 268800, 275520, 53760, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, -560, 114688, 268310, 274960, 53375, 316240], true⟩

theorem canonicalMatch7_105 :
    canonicalPose7_105.boxKey 188160 (referenceBox7 (!canonicalBox7_105.bump)) = canonicalBox7_105 := by decide +kernel

theorem canonicalDecode7_105 : canonicalBox7_105.toKeyData 188160 = keys7Chunk3.get ⟨9, by decide⟩ := by
  change canonicalBox7_105.toKeyData 188160 = ⟨![(9 / 14), 0, (17 / 28), (10 / 7), (41 / 28), (2 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (-1 / 336), (64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_105 : keySolid (keys7Chunk3.get ⟨9, by decide⟩) = canonicalPose7_105.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_105 (box := canonicalBox7_105) (k := keys7Chunk3.get ⟨9, by decide⟩) (canonicalMatch7_105) (canonicalDecode7_105)

def canonicalPose7_106 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, false, true, false, true], ![0, 1, 0, 1, 2, 0, 2]⟩
def canonicalBox7_106 : BoxKey 7 :=
  ⟨![107520, 73920, 0, 309120, 248640, 134400, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 73472, 560, 309540, 248240, 134785, 274960], false⟩

theorem canonicalMatch7_106 :
    canonicalPose7_106.boxKey 188160 (referenceBox7 (!canonicalBox7_106.bump)) = canonicalBox7_106 := by decide +kernel

theorem canonicalDecode7_106 : canonicalBox7_106.toKeyData 188160 = keys7Chunk3.get ⟨10, by decide⟩ := by
  change canonicalBox7_106.toKeyData 188160 = ⟨![(4 / 7), (11 / 28), 0, (23 / 14), (37 / 28), (5 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (41 / 105), (1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_106 : keySolid (keys7Chunk3.get ⟨10, by decide⟩) = canonicalPose7_106.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_106 (box := canonicalBox7_106) (k := keys7Chunk3.get ⟨10, by decide⟩) (canonicalMatch7_106) (canonicalDecode7_106)

def canonicalPose7_107 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, true, false, true, false, true], ![0, 1, 0, 1, 2, 0, 2]⟩
def canonicalBox7_107 : BoxKey 7 :=
  ⟨![127680, 67200, 0, 302400, 268800, 100800, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 66780, -560, 302848, 268310, 101360, 241535], true⟩

theorem canonicalMatch7_107 :
    canonicalPose7_107.boxKey 188160 (referenceBox7 (!canonicalBox7_107.bump)) = canonicalBox7_107 := by decide +kernel

theorem canonicalDecode7_107 : canonicalBox7_107.toKeyData 188160 = keys7Chunk3.get ⟨11, by decide⟩ := by
  change canonicalBox7_107.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), 0, (45 / 28), (10 / 7), (15 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (-1 / 336), (169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_107 : keySolid (keys7Chunk3.get ⟨11, by decide⟩) = canonicalPose7_107.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_107 (box := canonicalBox7_107) (k := keys7Chunk3.get ⟨11, by decide⟩) (canonicalMatch7_107) (canonicalDecode7_107)

def canonicalPose7_108 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, false, true, true, true, false], ![0, 0, 0, 2, 2, 1, 1]⟩
def canonicalBox7_108 : BoxKey 7 :=
  ⟨![100800, 107520, 114240, 376320, 255360, 60480, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 114688, 375760, 254940, 60080, 322945], false⟩

theorem canonicalMatch7_108 :
    canonicalPose7_108.boxKey 188160 (referenceBox7 (!canonicalBox7_108.bump)) = canonicalBox7_108 := by decide +kernel

theorem canonicalDecode7_108 : canonicalBox7_108.toKeyData 188160 = keys7Chunk3.get ⟨12, by decide⟩ := by
  change canonicalBox7_108.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (64 / 105), (671 / 336), (607 / 448), (751 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_108 : keySolid (keys7Chunk3.get ⟨12, by decide⟩) = canonicalPose7_108.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_108 (box := canonicalBox7_108) (k := keys7Chunk3.get ⟨12, by decide⟩) (canonicalMatch7_108) (canonicalDecode7_108)

def canonicalPose7_109 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, true, true, false, true], ![0, 0, 1, 2, 2, 0, 2]⟩
def canonicalBox7_109 : BoxKey 7 :=
  ⟨![100800, 134400, 60480, 255360, 376320, 114240, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 60080, 254940, 375760, 114688, 268310], false⟩

theorem canonicalMatch7_109 :
    canonicalPose7_109.boxKey 188160 (referenceBox7 (!canonicalBox7_109.bump)) = canonicalBox7_109 := by decide +kernel

theorem canonicalDecode7_109 : canonicalBox7_109.toKeyData 188160 = keys7Chunk3.get ⟨13, by decide⟩ := by
  change canonicalBox7_109.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (751 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_109 : keySolid (keys7Chunk3.get ⟨13, by decide⟩) = canonicalPose7_109.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_109 (box := canonicalBox7_109) (k := keys7Chunk3.get ⟨13, by decide⟩) (canonicalMatch7_109) (canonicalDecode7_109)

def canonicalPose7_110 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, true, false, false, true, true, true], ![0, 1, 0, 1, 2, 0, 2]⟩
def canonicalBox7_110 : BoxKey 7 :=
  ⟨![100800, 53760, 127680, 309120, 262080, 0, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 53375, 128080, 309540, 261632, -560, 268310], true⟩

theorem canonicalMatch7_110 :
    canonicalPose7_110.boxKey 188160 (referenceBox7 (!canonicalBox7_110.bump)) = canonicalBox7_110 := by decide +kernel

theorem canonicalDecode7_110 : canonicalBox7_110.toKeyData 188160 = keys7Chunk3.get ⟨14, by decide⟩ := by
  change canonicalBox7_110.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (19 / 28), (23 / 14), (39 / 28), 0, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (1525 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (-1 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_110 : keySolid (keys7Chunk3.get ⟨14, by decide⟩) = canonicalPose7_110.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_110 (box := canonicalBox7_110) (k := keys7Chunk3.get ⟨14, by decide⟩) (canonicalMatch7_110) (canonicalDecode7_110)

def canonicalPose7_111 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, true, false, false, true, false, true], ![0, 1, 0, 1, 2, 0, 2]⟩
def canonicalBox7_111 : BoxKey 7 :=
  ⟨![114240, 67200, 127680, 322560, 275520, 107520, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 66780, 128080, 322945, 274960, 108010, 375760], false⟩

theorem canonicalMatch7_111 :
    canonicalPose7_111.boxKey 188160 (referenceBox7 (!canonicalBox7_111.bump)) = canonicalBox7_111 := by decide +kernel

theorem canonicalDecode7_111 : canonicalBox7_111.toKeyData 188160 = keys7Chunk3.get ⟨15, by decide⟩ := by
  change canonicalBox7_111.toKeyData 188160 = ⟨![(17 / 28), (5 / 14), (19 / 28), (12 / 7), (41 / 28), (4 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (159 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_111 : keySolid (keys7Chunk3.get ⟨15, by decide⟩) = canonicalPose7_111.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_111 (box := canonicalBox7_111) (k := keys7Chunk3.get ⟨15, by decide⟩) (canonicalMatch7_111) (canonicalDecode7_111)

def canonicalPose7_112 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, false, false, false, true, false, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_112 : BoxKey 7 :=
  ⟨![0, 107520, 100800, 322560, 248640, 309120, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![-560, 108010, 101360, 322945, 248240, 309540, 114688], true⟩

theorem canonicalMatch7_112 :
    canonicalPose7_112.boxKey 188160 (referenceBox7 (!canonicalBox7_112.bump)) = canonicalBox7_112 := by decide +kernel

theorem canonicalDecode7_112 : canonicalBox7_112.toKeyData 188160 = keys7Chunk3.get ⟨16, by decide⟩ := by
  change canonicalBox7_112.toKeyData 188160 = ⟨![0, (4 / 7), (15 / 28), (12 / 7), (37 / 28), (23 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(-1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_112 : keySolid (keys7Chunk3.get ⟨16, by decide⟩) = canonicalPose7_112.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_112 (box := canonicalBox7_112) (k := keys7Chunk3.get ⟨16, by decide⟩) (canonicalMatch7_112) (canonicalDecode7_112)

def canonicalPose7_113 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, false, false, false, true, false, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_113 : BoxKey 7 :=
  ⟨![107520, 0, 114240, 309120, 248640, 322560, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, 560, 114688, 309540, 248240, 322945, 101360], false⟩

theorem canonicalMatch7_113 :
    canonicalPose7_113.boxKey 188160 (referenceBox7 (!canonicalBox7_113.bump)) = canonicalBox7_113 := by decide +kernel

theorem canonicalDecode7_113 : canonicalBox7_113.toKeyData 188160 = keys7Chunk3.get ⟨17, by decide⟩ := by
  change canonicalBox7_113.toKeyData 188160 = ⟨![(4 / 7), 0, (17 / 28), (23 / 14), (37 / 28), (12 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (1 / 336), (64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_113 : keySolid (keys7Chunk3.get ⟨17, by decide⟩) = canonicalPose7_113.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_113 (box := canonicalBox7_113) (k := keys7Chunk3.get ⟨17, by decide⟩) (canonicalMatch7_113) (canonicalDecode7_113)

def canonicalPose7_114 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, true, false, true, false], ![0, 0, 0, 2, 1, 2, 0]⟩
def canonicalBox7_114 : BoxKey 7 :=
  ⟨![107520, 114240, 0, 255360, 315840, 241920, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, -560, 254940, 316240, 241535, 101360], true⟩

theorem canonicalMatch7_114 :
    canonicalPose7_114.boxKey 188160 (referenceBox7 (!canonicalBox7_114.bump)) = canonicalBox7_114 := by decide +kernel

theorem canonicalDecode7_114 : canonicalBox7_114.toKeyData 188160 = keys7Chunk3.get ⟨18, by decide⟩ := by
  change canonicalBox7_114.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 0, (19 / 14), (47 / 28), (9 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_114 : keySolid (keys7Chunk3.get ⟨18, by decide⟩) = canonicalPose7_114.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_114 (box := canonicalBox7_114) (k := keys7Chunk3.get ⟨18, by decide⟩) (canonicalMatch7_114) (canonicalDecode7_114)

def canonicalPose7_115 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, false, false, true, true, false], ![1, 1, 0, 2, 2, 2, 0]⟩
def canonicalBox7_115 : BoxKey 7 :=
  ⟨![53760, 60480, 120960, 376320, 262080, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 60080, 121380, 376880, 261632, 268310, 101360], true⟩

theorem canonicalMatch7_115 :
    canonicalPose7_115.boxKey 188160 (referenceBox7 (!canonicalBox7_115.bump)) = canonicalBox7_115 := by decide +kernel

theorem canonicalDecode7_115 : canonicalBox7_115.toKeyData 188160 = keys7Chunk3.get ⟨19, by decide⟩ := by
  change canonicalBox7_115.toKeyData 188160 = ⟨![(2 / 7), (9 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (751 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_115 : keySolid (keys7Chunk3.get ⟨19, by decide⟩) = canonicalPose7_115.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_115 (box := canonicalBox7_115) (k := keys7Chunk3.get ⟨19, by decide⟩) (canonicalMatch7_115) (canonicalDecode7_115)

def canonicalPose7_116 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, false, false, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_116 : BoxKey 7 :=
  ⟨![100800, 134400, 127680, 309120, 376320, 302400, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 128080, 309540, 376880, 302848, 108010], true⟩

theorem canonicalMatch7_116 :
    canonicalPose7_116.boxKey 188160 (referenceBox7 (!canonicalBox7_116.bump)) = canonicalBox7_116 := by decide +kernel

theorem canonicalDecode7_116 : canonicalBox7_116.toKeyData 188160 = keys7Chunk3.get ⟨20, by decide⟩ := by
  change canonicalBox7_116.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (19 / 28), (23 / 14), 2, (45 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448), (673 / 336), (169 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_116 : keySolid (keys7Chunk3.get ⟨20, by decide⟩) = canonicalPose7_116.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_116 (box := canonicalBox7_116) (k := keys7Chunk3.get ⟨20, by decide⟩) (canonicalMatch7_116) (canonicalDecode7_116)

def canonicalPose7_117 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, false, true, false, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_117 : BoxKey 7 :=
  ⟨![134400, 100800, 107520, 302400, 376320, 309120, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 108010, 302848, 375760, 309540, 128080], false⟩

theorem canonicalMatch7_117 :
    canonicalPose7_117.boxKey 188160 (referenceBox7 (!canonicalBox7_117.bump)) = canonicalBox7_117 := by decide +kernel

theorem canonicalDecode7_117 : canonicalBox7_117.toKeyData 188160 = keys7Chunk3.get ⟨21, by decide⟩ := by
  change canonicalBox7_117.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (4 / 7), (45 / 28), 2, (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105), (671 / 336), (737 / 448), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_117 : keySolid (keys7Chunk3.get ⟨21, by decide⟩) = canonicalPose7_117.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_117 (box := canonicalBox7_117) (k := keys7Chunk3.get ⟨21, by decide⟩) (canonicalMatch7_117) (canonicalDecode7_117)

def canonicalPose7_118 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, false, true, true, true, false], ![1, 1, 0, 2, 2, 2, 0]⟩
def canonicalBox7_118 : BoxKey 7 :=
  ⟨![60480, 53760, 100800, 268800, 262080, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 53375, 101360, 268310, 261632, 375760, 121380], false⟩

theorem canonicalMatch7_118 :
    canonicalPose7_118.boxKey 188160 (referenceBox7 (!canonicalBox7_118.bump)) = canonicalBox7_118 := by decide +kernel

theorem canonicalDecode7_118 : canonicalBox7_118.toKeyData 188160 = keys7Chunk3.get ⟨22, by decide⟩ := by
  change canonicalBox7_118.toKeyData 188160 = ⟨![(9 / 28), (2 / 7), (15 / 28), (10 / 7), (39 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_118 : keySolid (keys7Chunk3.get ⟨22, by decide⟩) = canonicalPose7_118.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_118 (box := canonicalBox7_118) (k := keys7Chunk3.get ⟨22, by decide⟩) (canonicalMatch7_118) (canonicalDecode7_118)

def canonicalPose7_119 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, true, false, true, false], ![0, 0, 0, 2, 1, 2, 0]⟩
def canonicalBox7_119 : BoxKey 7 :=
  ⟨![114240, 107520, 100800, 241920, 315840, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 101360, 241535, 316240, 254940, 560], false⟩

theorem canonicalMatch7_119 :
    canonicalPose7_119.boxKey 188160 (referenceBox7 (!canonicalBox7_119.bump)) = canonicalBox7_119 := by decide +kernel

theorem canonicalDecode7_119 : canonicalBox7_119.toKeyData 188160 = keys7Chunk3.get ⟨23, by decide⟩ := by
  change canonicalBox7_119.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (15 / 28), (9 / 7), (47 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_119 : keySolid (keys7Chunk3.get ⟨23, by decide⟩) = canonicalPose7_119.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_119 (box := canonicalBox7_119) (k := keys7Chunk3.get ⟨23, by decide⟩) (canonicalMatch7_119) (canonicalDecode7_119)

def canonicalPose7_120 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, true, false, false, true], ![0, 0, 0, 2, 1, 1, 2]⟩
def canonicalBox7_120 : BoxKey 7 :=
  ⟨![0, 114240, 107520, 275520, 322560, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 114688, 108010, 274960, 322945, 316240, 254940], false⟩

theorem canonicalMatch7_120 :
    canonicalPose7_120.boxKey 188160 (referenceBox7 (!canonicalBox7_120.bump)) = canonicalBox7_120 := by decide +kernel

theorem canonicalDecode7_120 : canonicalBox7_120.toKeyData 188160 = keys7Chunk3.get ⟨24, by decide⟩ := by
  change canonicalBox7_120.toKeyData 188160 = ⟨![0, (17 / 28), (4 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (64 / 105), (1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_120 : keySolid (keys7Chunk3.get ⟨24, by decide⟩) = canonicalPose7_120.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_120 (box := canonicalBox7_120) (k := keys7Chunk3.get ⟨24, by decide⟩) (canonicalMatch7_120) (canonicalDecode7_120)

def canonicalPose7_121 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, true, true, true, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_121 : BoxKey 7 :=
  ⟨![73920, 0, 67200, 248640, 241920, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, -560, 66780, 248240, 241535, 274960, 268310], true⟩

theorem canonicalMatch7_121 :
    canonicalPose7_121.boxKey 188160 (referenceBox7 (!canonicalBox7_121.bump)) = canonicalBox7_121 := by decide +kernel

theorem canonicalDecode7_121 : canonicalBox7_121.toKeyData 188160 = keys7Chunk3.get ⟨25, by decide⟩ := by
  change canonicalBox7_121.toKeyData 188160 = ⟨![(11 / 28), 0, (5 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (-1 / 336), (159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_121 : keySolid (keys7Chunk3.get ⟨25, by decide⟩) = canonicalPose7_121.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_121 (box := canonicalBox7_121) (k := keys7Chunk3.get ⟨25, by decide⟩) (canonicalMatch7_121) (canonicalDecode7_121)

def canonicalPose7_122 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, true, true, true, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_122 : BoxKey 7 :=
  ⟨![67200, 0, 73920, 268800, 275520, 241920, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 560, 73472, 268310, 274960, 241535, 248240], false⟩

theorem canonicalMatch7_122 :
    canonicalPose7_122.boxKey 188160 (referenceBox7 (!canonicalBox7_122.bump)) = canonicalBox7_122 := by decide +kernel

theorem canonicalDecode7_122 : canonicalBox7_122.toKeyData 188160 = keys7Chunk3.get ⟨26, by decide⟩ := by
  change canonicalBox7_122.toKeyData 188160 = ⟨![(5 / 14), 0, (11 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (1 / 336), (41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_122 : keySolid (keys7Chunk3.get ⟨26, by decide⟩) = canonicalPose7_122.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_122 (box := canonicalBox7_122) (k := keys7Chunk3.get ⟨26, by decide⟩) (canonicalMatch7_122) (canonicalDecode7_122)

def canonicalPose7_123 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, true, false, false, true], ![0, 0, 0, 2, 1, 1, 2]⟩
def canonicalBox7_123 : BoxKey 7 :=
  ⟨![107520, 114240, 0, 255360, 315840, 322560, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, -560, 254940, 316240, 322945, 274960], true⟩

theorem canonicalMatch7_123 :
    canonicalPose7_123.boxKey 188160 (referenceBox7 (!canonicalBox7_123.bump)) = canonicalBox7_123 := by decide +kernel

theorem canonicalDecode7_123 : canonicalBox7_123.toKeyData 188160 = keys7Chunk3.get ⟨27, by decide⟩ := by
  change canonicalBox7_123.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 0, (19 / 14), (47 / 28), (12 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_123 : keySolid (keys7Chunk3.get ⟨27, by decide⟩) = canonicalPose7_123.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_123 (box := canonicalBox7_123) (k := keys7Chunk3.get ⟨27, by decide⟩) (canonicalMatch7_123) (canonicalDecode7_123)

def canonicalPose7_124 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, false, false, true, true, true], ![0, 1, 0, 2, 2, 2, 2]⟩
def canonicalBox7_124 : BoxKey 7 :=
  ⟨![134400, 60480, 120960, 376320, 262080, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 60080, 121380, 376880, 261632, 268310, 274960], true⟩

theorem canonicalMatch7_124 :
    canonicalPose7_124.boxKey 188160 (referenceBox7 (!canonicalBox7_124.bump)) = canonicalBox7_124 := by decide +kernel

theorem canonicalDecode7_124 : canonicalBox7_124.toKeyData 188160 = keys7Chunk3.get ⟨28, by decide⟩ := by
  change canonicalBox7_124.toKeyData 188160 = ⟨![(5 / 7), (9 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (751 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_124 : keySolid (keys7Chunk3.get ⟨28, by decide⟩) = canonicalPose7_124.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_124 (box := canonicalBox7_124) (k := keys7Chunk3.get ⟨28, by decide⟩) (canonicalMatch7_124) (canonicalDecode7_124)

def canonicalPose7_125 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, false, true, true, true, true, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_125 : BoxKey 7 :=
  ⟨![53760, 127680, 67200, 262080, 376320, 268800, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 128080, 66780, 261632, 375760, 268310, 274960], false⟩

theorem canonicalMatch7_125 :
    canonicalPose7_125.boxKey 188160 (referenceBox7 (!canonicalBox7_125.bump)) = canonicalBox7_125 := by decide +kernel

theorem canonicalDecode7_125 : canonicalBox7_125.toKeyData 188160 = keys7Chunk3.get ⟨29, by decide⟩ := by
  change canonicalBox7_125.toKeyData 188160 = ⟨![(2 / 7), (19 / 28), (5 / 14), (39 / 28), 2, (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105), (671 / 336), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_125 : keySolid (keys7Chunk3.get ⟨29, by decide⟩) = canonicalPose7_125.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_125 (box := canonicalBox7_125) (k := keys7Chunk3.get ⟨29, by decide⟩) (canonicalMatch7_125) (canonicalDecode7_125)

def canonicalPose7_126 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, false, true, true, true, false, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_126 : BoxKey 7 :=
  ⟨![67200, 127680, 53760, 275520, 268800, 376320, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 128080, 53375, 274960, 268310, 376880, 261632], true⟩

theorem canonicalMatch7_126 :
    canonicalPose7_126.boxKey 188160 (referenceBox7 (!canonicalBox7_126.bump)) = canonicalBox7_126 := by decide +kernel

theorem canonicalDecode7_126 : canonicalBox7_126.toKeyData 188160 = keys7Chunk3.get ⟨30, by decide⟩ := by
  change canonicalBox7_126.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (2 / 7), (41 / 28), (10 / 7), 2, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (673 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_126 : keySolid (keys7Chunk3.get ⟨30, by decide⟩) = canonicalPose7_126.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_126 (box := canonicalBox7_126) (k := keys7Chunk3.get ⟨30, by decide⟩) (canonicalMatch7_126) (canonicalDecode7_126)

def canonicalPose7_127 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, false, true, true, true, true], ![0, 1, 0, 2, 2, 2, 2]⟩
def canonicalBox7_127 : BoxKey 7 :=
  ⟨![120960, 60480, 134400, 275520, 268800, 262080, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 60080, 134785, 274960, 268310, 261632, 375760], false⟩

theorem canonicalMatch7_127 :
    canonicalPose7_127.boxKey 188160 (referenceBox7 (!canonicalBox7_127.bump)) = canonicalBox7_127 := by decide +kernel

theorem canonicalDecode7_127 : canonicalBox7_127.toKeyData 188160 = keys7Chunk3.get ⟨31, by decide⟩ := by
  change canonicalBox7_127.toKeyData 188160 = ⟨![(9 / 14), (9 / 28), (5 / 7), (41 / 28), (10 / 7), (39 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (751 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_127 : keySolid (keys7Chunk3.get ⟨31, by decide⟩) = canonicalPose7_127.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_127 (box := canonicalBox7_127) (k := keys7Chunk3.get ⟨31, by decide⟩) (canonicalMatch7_127) (canonicalDecode7_127)

theorem keys7Chunk3_canonical : ∀ k ∈ keys7Chunk3,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk3, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_96, canonicalSolid7_96⟩
  · exact ⟨canonicalPose7_97, canonicalSolid7_97⟩
  · exact ⟨canonicalPose7_98, canonicalSolid7_98⟩
  · exact ⟨canonicalPose7_99, canonicalSolid7_99⟩
  · exact ⟨canonicalPose7_100, canonicalSolid7_100⟩
  · exact ⟨canonicalPose7_101, canonicalSolid7_101⟩
  · exact ⟨canonicalPose7_102, canonicalSolid7_102⟩
  · exact ⟨canonicalPose7_103, canonicalSolid7_103⟩
  · exact ⟨canonicalPose7_104, canonicalSolid7_104⟩
  · exact ⟨canonicalPose7_105, canonicalSolid7_105⟩
  · exact ⟨canonicalPose7_106, canonicalSolid7_106⟩
  · exact ⟨canonicalPose7_107, canonicalSolid7_107⟩
  · exact ⟨canonicalPose7_108, canonicalSolid7_108⟩
  · exact ⟨canonicalPose7_109, canonicalSolid7_109⟩
  · exact ⟨canonicalPose7_110, canonicalSolid7_110⟩
  · exact ⟨canonicalPose7_111, canonicalSolid7_111⟩
  · exact ⟨canonicalPose7_112, canonicalSolid7_112⟩
  · exact ⟨canonicalPose7_113, canonicalSolid7_113⟩
  · exact ⟨canonicalPose7_114, canonicalSolid7_114⟩
  · exact ⟨canonicalPose7_115, canonicalSolid7_115⟩
  · exact ⟨canonicalPose7_116, canonicalSolid7_116⟩
  · exact ⟨canonicalPose7_117, canonicalSolid7_117⟩
  · exact ⟨canonicalPose7_118, canonicalSolid7_118⟩
  · exact ⟨canonicalPose7_119, canonicalSolid7_119⟩
  · exact ⟨canonicalPose7_120, canonicalSolid7_120⟩
  · exact ⟨canonicalPose7_121, canonicalSolid7_121⟩
  · exact ⟨canonicalPose7_122, canonicalSolid7_122⟩
  · exact ⟨canonicalPose7_123, canonicalSolid7_123⟩
  · exact ⟨canonicalPose7_124, canonicalSolid7_124⟩
  · exact ⟨canonicalPose7_125, canonicalSolid7_125⟩
  · exact ⟨canonicalPose7_126, canonicalSolid7_126⟩
  · exact ⟨canonicalPose7_127, canonicalSolid7_127⟩

#print axioms keys7Chunk3_canonical

end SparseMonotiles.Canonical
