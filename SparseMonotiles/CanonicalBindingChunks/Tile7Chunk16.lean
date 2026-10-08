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

def canonicalPose7_512 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, true, true, true, true], ![1, 2, 2, 2, 2, 2, 2]⟩
def canonicalBox7_512 : BoxKey 7 :=
  ⟨![60480, 241920, 275520, 268800, 262080, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 241535, 274960, 268310, 261632, 375760, 254940], false⟩

theorem canonicalMatch7_512 :
    canonicalPose7_512.boxKey 188160 (referenceBox7 (!canonicalBox7_512.bump)) = canonicalBox7_512 := by decide +kernel

theorem canonicalDecode7_512 : canonicalBox7_512.toKeyData 188160 = keys7Chunk16.get ⟨0, by decide⟩ := by
  change canonicalBox7_512.toKeyData 188160 = ⟨![(9 / 28), (9 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_512 : keySolid (keys7Chunk16.get ⟨0, by decide⟩) = canonicalPose7_512.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_512 (box := canonicalBox7_512) (k := keys7Chunk16.get ⟨0, by decide⟩) (canonicalMatch7_512) (canonicalDecode7_512)

def canonicalPose7_513 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, true, false, false, true, true], ![0, 2, 2, 1, 1, 2, 2]⟩
def canonicalBox7_513 : BoxKey 7 :=
  ⟨![114240, 268800, 275520, 322560, 315840, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 268310, 274960, 322945, 316240, 254940, 375760], false⟩

theorem canonicalMatch7_513 :
    canonicalPose7_513.boxKey 188160 (referenceBox7 (!canonicalBox7_513.bump)) = canonicalBox7_513 := by decide +kernel

theorem canonicalDecode7_513 : canonicalBox7_513.toKeyData 188160 = keys7Chunk16.get ⟨1, by decide⟩ := by
  change canonicalBox7_513.toKeyData 188160 = ⟨![(17 / 28), (10 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (3833 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_513 : keySolid (keys7Chunk16.get ⟨1, by decide⟩) = canonicalPose7_513.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_513 (box := canonicalBox7_513) (k := keys7Chunk16.get ⟨1, by decide⟩) (canonicalMatch7_513) (canonicalDecode7_513)

def canonicalPose7_514 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, false, false, false, false, true], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_514 : BoxKey 7 :=
  ⟨![376320, 73920, 107520, 100800, 134400, 127680, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 73472, 108010, 101360, 134785, 128080, 66780], true⟩

theorem canonicalMatch7_514 :
    canonicalPose7_514.boxKey 188160 (referenceBox7 (!canonicalBox7_514.bump)) = canonicalBox7_514 := by decide +kernel

theorem canonicalDecode7_514 : canonicalBox7_514.toKeyData 188160 = keys7Chunk16.get ⟨2, by decide⟩ := by
  change canonicalBox7_514.toKeyData 188160 = ⟨![2, (11 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (41 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_514 : keySolid (keys7Chunk16.get ⟨2, by decide⟩) = canonicalPose7_514.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_514 (box := canonicalBox7_514) (k := keys7Chunk16.get ⟨2, by decide⟩) (canonicalMatch7_514) (canonicalDecode7_514)

def canonicalPose7_515 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, false, false, false, true], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_515 : BoxKey 7 :=
  ⟨![376320, 67200, 127680, 134400, 100800, 107520, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 66780, 128080, 134785, 101360, 108010, 73472], false⟩

theorem canonicalMatch7_515 :
    canonicalPose7_515.boxKey 188160 (referenceBox7 (!canonicalBox7_515.bump)) = canonicalBox7_515 := by decide +kernel

theorem canonicalDecode7_515 : canonicalBox7_515.toKeyData 188160 = keys7Chunk16.get ⟨3, by decide⟩ := by
  change canonicalBox7_515.toKeyData 188160 = ⟨![2, (5 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (159 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_515 : keySolid (keys7Chunk16.get ⟨3, by decide⟩) = canonicalPose7_515.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_515 (box := canonicalBox7_515) (k := keys7Chunk16.get ⟨3, by decide⟩) (canonicalMatch7_515) (canonicalDecode7_515)

def canonicalPose7_516 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, false, true, true, false, false], ![2, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_516 : BoxKey 7 :=
  ⟨![262080, 0, 120960, 60480, 53760, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 560, 121380, 60080, 53375, 101360, 108010], false⟩

theorem canonicalMatch7_516 :
    canonicalPose7_516.boxKey 188160 (referenceBox7 (!canonicalBox7_516.bump)) = canonicalBox7_516 := by decide +kernel

theorem canonicalDecode7_516 : canonicalBox7_516.toKeyData 188160 = keys7Chunk16.get ⟨4, by decide⟩ := by
  change canonicalBox7_516.toKeyData 188160 = ⟨![(39 / 28), 0, (9 / 14), (9 / 28), (2 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (1 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_516 : keySolid (keys7Chunk16.get ⟨4, by decide⟩) = canonicalPose7_516.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_516 (box := canonicalBox7_516) (k := keys7Chunk16.get ⟨4, by decide⟩) (canonicalMatch7_516) (canonicalDecode7_516)

def canonicalPose7_517 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, false, false, false, false], ![1, 0, 0, 0, 0, 0, 0]⟩
def canonicalBox7_517 : BoxKey 7 :=
  ⟨![315840, 120960, 0, 114240, 107520, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 560, 114688, 108010, 101360, 134785], false⟩

theorem canonicalMatch7_517 :
    canonicalPose7_517.boxKey 188160 (referenceBox7 (!canonicalBox7_517.bump)) = canonicalBox7_517 := by decide +kernel

theorem canonicalDecode7_517 : canonicalBox7_517.toKeyData 188160 = keys7Chunk16.get ⟨5, by decide⟩ := by
  change canonicalBox7_517.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_517 : keySolid (keys7Chunk16.get ⟨5, by decide⟩) = canonicalPose7_517.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_517 (box := canonicalBox7_517) (k := keys7Chunk16.get ⟨5, by decide⟩) (canonicalMatch7_517) (canonicalDecode7_517)

def canonicalPose7_518 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, true, false, true, false, false, true], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_518 : BoxKey 7 :=
  ⟨![248640, 67200, 114240, 0, 107520, 100800, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 66780, 114688, -560, 108010, 101360, 53375], true⟩

theorem canonicalMatch7_518 :
    canonicalPose7_518.boxKey 188160 (referenceBox7 (!canonicalBox7_518.bump)) = canonicalBox7_518 := by decide +kernel

theorem canonicalDecode7_518 : canonicalBox7_518.toKeyData 188160 = keys7Chunk16.get ⟨6, by decide⟩ := by
  change canonicalBox7_518.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), (17 / 28), 0, (4 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (64 / 105), (-1 / 336), (1543 / 2688), (181 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_518 : keySolid (keys7Chunk16.get ⟨6, by decide⟩) = canonicalPose7_518.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_518 (box := canonicalBox7_518) (k := keys7Chunk16.get ⟨6, by decide⟩) (canonicalMatch7_518) (canonicalDecode7_518)

def canonicalPose7_519 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, true, false, false, false, false, true], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_519 : BoxKey 7 :=
  ⟨![248640, 53760, 100800, 107520, 0, 114240, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 53375, 101360, 108010, 560, 114688, 66780], false⟩

theorem canonicalMatch7_519 :
    canonicalPose7_519.boxKey 188160 (referenceBox7 (!canonicalBox7_519.bump)) = canonicalBox7_519 := by decide +kernel

theorem canonicalDecode7_519 : canonicalBox7_519.toKeyData 188160 = keys7Chunk16.get ⟨7, by decide⟩ := by
  change canonicalBox7_519.toKeyData 188160 = ⟨![(37 / 28), (2 / 7), (15 / 28), (4 / 7), 0, (17 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688), (1 / 336), (64 / 105), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_519 : keySolid (keys7Chunk16.get ⟨7, by decide⟩) = canonicalPose7_519.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_519 (box := canonicalBox7_519) (k := keys7Chunk16.get ⟨7, by decide⟩) (canonicalMatch7_519) (canonicalDecode7_519)

def canonicalPose7_520 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, false, false, true, false], ![1, 0, 0, 0, 0, 0, 0]⟩
def canonicalBox7_520 : BoxKey 7 :=
  ⟨![315840, 134400, 100800, 107520, 114240, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 134785, 101360, 108010, 114688, -560, 121380], true⟩

theorem canonicalMatch7_520 :
    canonicalPose7_520.boxKey 188160 (referenceBox7 (!canonicalBox7_520.bump)) = canonicalBox7_520 := by decide +kernel

theorem canonicalDecode7_520 : canonicalBox7_520.toKeyData 188160 = keys7Chunk16.get ⟨8, by decide⟩ := by
  change canonicalBox7_520.toKeyData 188160 = ⟨![(47 / 28), (5 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_520 : keySolid (keys7Chunk16.get ⟨8, by decide⟩) = canonicalPose7_520.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_520 (box := canonicalBox7_520) (k := keys7Chunk16.get ⟨8, by decide⟩) (canonicalMatch7_520) (canonicalDecode7_520)

def canonicalPose7_521 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, false, true, true, false, true], ![2, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_521 : BoxKey 7 :=
  ⟨![262080, 107520, 100800, 53760, 60480, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 108010, 101360, 53375, 60080, 121380, -560], true⟩

theorem canonicalMatch7_521 :
    canonicalPose7_521.boxKey 188160 (referenceBox7 (!canonicalBox7_521.bump)) = canonicalBox7_521 := by decide +kernel

theorem canonicalDecode7_521 : canonicalBox7_521.toKeyData 188160 = keys7Chunk16.get ⟨9, by decide⟩ := by
  change canonicalBox7_521.toKeyData 188160 = ⟨![(39 / 28), (4 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (1543 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_521 : keySolid (keys7Chunk16.get ⟨9, by decide⟩) = canonicalPose7_521.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_521 (box := canonicalBox7_521) (k := keys7Chunk16.get ⟨9, by decide⟩) (canonicalMatch7_521) (canonicalDecode7_521)

def canonicalPose7_522 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, false, true, false, true, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_522 : BoxKey 7 :=
  ⟨![376320, 114240, 67200, 127680, 53760, 100800, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![376880, 114688, 66780, 128080, 53375, 101360, 268310], true⟩

theorem canonicalMatch7_522 :
    canonicalPose7_522.boxKey 188160 (referenceBox7 (!canonicalBox7_522.bump)) = canonicalBox7_522 := by decide +kernel

theorem canonicalDecode7_522 : canonicalBox7_522.toKeyData 188160 = keys7Chunk16.get ⟨10, by decide⟩ := by
  change canonicalBox7_522.toKeyData 188160 = ⟨![2, (17 / 28), (5 / 14), (19 / 28), (2 / 7), (15 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(673 / 336), (64 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_522 : keySolid (keys7Chunk16.get ⟨10, by decide⟩) = canonicalPose7_522.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_522 (box := canonicalBox7_522) (k := keys7Chunk16.get ⟨10, by decide⟩) (canonicalMatch7_522) (canonicalDecode7_522)

def canonicalPose7_523 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, false, true, false, false, true], ![2, 0, 0, 1, 0, 0, 2]⟩
def canonicalBox7_523 : BoxKey 7 :=
  ⟨![262080, 0, 120960, 60480, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 560, 121380, 60080, 134785, 101360, 268310], false⟩

theorem canonicalMatch7_523 :
    canonicalPose7_523.boxKey 188160 (referenceBox7 (!canonicalBox7_523.bump)) = canonicalBox7_523 := by decide +kernel

theorem canonicalDecode7_523 : canonicalBox7_523.toKeyData 188160 = keys7Chunk16.get ⟨11, by decide⟩ := by
  change canonicalBox7_523.toKeyData 188160 = ⟨![(39 / 28), 0, (9 / 14), (9 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (1 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_523 : keySolid (keys7Chunk16.get ⟨11, by decide⟩) = canonicalPose7_523.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_523 (box := canonicalBox7_523) (k := keys7Chunk16.get ⟨11, by decide⟩) (canonicalMatch7_523) (canonicalDecode7_523)

def canonicalPose7_524 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, false, false, false, false], ![1, 0, 0, 0, 0, 0, 1]⟩
def canonicalBox7_524 : BoxKey 7 :=
  ⟨![315840, 120960, 0, 114240, 107520, 100800, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 560, 114688, 108010, 101360, 322945], false⟩

theorem canonicalMatch7_524 :
    canonicalPose7_524.boxKey 188160 (referenceBox7 (!canonicalBox7_524.bump)) = canonicalBox7_524 := by decide +kernel

theorem canonicalDecode7_524 : canonicalBox7_524.toKeyData 188160 = keys7Chunk16.get ⟨12, by decide⟩ := by
  change canonicalBox7_524.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_524 : keySolid (keys7Chunk16.get ⟨12, by decide⟩) = canonicalPose7_524.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_524 (box := canonicalBox7_524) (k := keys7Chunk16.get ⟨12, by decide⟩) (canonicalMatch7_524) (canonicalDecode7_524)

def canonicalPose7_525 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, true, true, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_525 : BoxKey 7 :=
  ⟨![275520, 107520, 73920, 0, 67200, 127680, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 73472, -560, 66780, 128080, 241535], true⟩

theorem canonicalMatch7_525 :
    canonicalPose7_525.boxKey 188160 (referenceBox7 (!canonicalBox7_525.bump)) = canonicalBox7_525 := by decide +kernel

theorem canonicalDecode7_525 : canonicalBox7_525.toKeyData 188160 = keys7Chunk16.get ⟨13, by decide⟩ := by
  change canonicalBox7_525.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (11 / 28), 0, (5 / 14), (19 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (41 / 105), (-1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_525 : keySolid (keys7Chunk16.get ⟨13, by decide⟩) = canonicalPose7_525.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_525 (box := canonicalBox7_525) (k := keys7Chunk16.get ⟨13, by decide⟩) (canonicalMatch7_525) (canonicalDecode7_525)

def canonicalPose7_526 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, true, false, true, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_526 : BoxKey 7 :=
  ⟨![241920, 127680, 67200, 0, 73920, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 128080, 66780, 560, 73472, 108010, 274960], false⟩

theorem canonicalMatch7_526 :
    canonicalPose7_526.boxKey 188160 (referenceBox7 (!canonicalBox7_526.bump)) = canonicalBox7_526 := by decide +kernel

theorem canonicalDecode7_526 : canonicalBox7_526.toKeyData 188160 = keys7Chunk16.get ⟨14, by decide⟩ := by
  change canonicalBox7_526.toKeyData 188160 = ⟨![(9 / 7), (19 / 28), (5 / 14), 0, (11 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (1601 / 2352), (159 / 448), (1 / 336), (41 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_526 : keySolid (keys7Chunk16.get ⟨14, by decide⟩) = canonicalPose7_526.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_526 (box := canonicalBox7_526) (k := keys7Chunk16.get ⟨14, by decide⟩) (canonicalMatch7_526) (canonicalDecode7_526)

def canonicalPose7_527 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, false, true, false, false], ![1, 0, 0, 0, 0, 0, 1]⟩
def canonicalBox7_527 : BoxKey 7 :=
  ⟨![322560, 100800, 107520, 114240, 0, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 101360, 108010, 114688, -560, 121380, 316240], true⟩

theorem canonicalMatch7_527 :
    canonicalPose7_527.boxKey 188160 (referenceBox7 (!canonicalBox7_527.bump)) = canonicalBox7_527 := by decide +kernel

theorem canonicalDecode7_527 : canonicalBox7_527.toKeyData 188160 = keys7Chunk16.get ⟨15, by decide⟩ := by
  change canonicalBox7_527.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (289 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_527 : keySolid (keys7Chunk16.get ⟨15, by decide⟩) = canonicalPose7_527.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_527 (box := canonicalBox7_527) (k := keys7Chunk16.get ⟨15, by decide⟩) (canonicalMatch7_527) (canonicalDecode7_527)

def canonicalPose7_528 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, true, false, true, true], ![2, 0, 0, 1, 0, 0, 2]⟩
def canonicalBox7_528 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 60480, 120960, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 60080, 121380, -560, 261632], true⟩

theorem canonicalMatch7_528 :
    canonicalPose7_528.boxKey 188160 (referenceBox7 (!canonicalBox7_528.bump)) = canonicalBox7_528 := by decide +kernel

theorem canonicalDecode7_528 : canonicalBox7_528.toKeyData 188160 = keys7Chunk16.get ⟨16, by decide⟩ := by
  change canonicalBox7_528.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (9 / 28), (9 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_528 : keySolid (keys7Chunk16.get ⟨16, by decide⟩) = canonicalPose7_528.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_528 (box := canonicalBox7_528) (k := keys7Chunk16.get ⟨16, by decide⟩) (canonicalMatch7_528) (canonicalDecode7_528)

def canonicalPose7_529 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, false, true, false, true, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_529 : BoxKey 7 :=
  ⟨![268800, 100800, 53760, 127680, 67200, 114240, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 101360, 53375, 128080, 66780, 114688, 375760], false⟩

theorem canonicalMatch7_529 :
    canonicalPose7_529.boxKey 188160 (referenceBox7 (!canonicalBox7_529.bump)) = canonicalBox7_529 := by decide +kernel

theorem canonicalDecode7_529 : canonicalBox7_529.toKeyData 188160 = keys7Chunk16.get ⟨17, by decide⟩ := by
  change canonicalBox7_529.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (2 / 7), (19 / 28), (5 / 14), (17 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (64 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_529 : keySolid (keys7Chunk16.get ⟨17, by decide⟩) = canonicalPose7_529.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_529 (box := canonicalBox7_529) (k := keys7Chunk16.get ⟨17, by decide⟩) (canonicalMatch7_529) (canonicalDecode7_529)

def canonicalPose7_530 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, true, true, false, true, false], ![2, 0, 1, 1, 0, 2, 0]⟩
def canonicalBox7_530 : BoxKey 7 :=
  ⟨![376320, 120960, 60480, 53760, 100800, 268800, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 121380, 60080, 53375, 101360, 268310, 114688], true⟩

theorem canonicalMatch7_530 :
    canonicalPose7_530.boxKey 188160 (referenceBox7 (!canonicalBox7_530.bump)) = canonicalBox7_530 := by decide +kernel

theorem canonicalDecode7_530 : canonicalBox7_530.toKeyData 188160 = keys7Chunk16.get ⟨18, by decide⟩ := by
  change canonicalBox7_530.toKeyData 188160 = ⟨![2, (9 / 14), (9 / 28), (2 / 7), (15 / 28), (10 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_530 : keySolid (keys7Chunk16.get ⟨18, by decide⟩) = canonicalPose7_530.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_530 (box := canonicalBox7_530) (k := keys7Chunk16.get ⟨18, by decide⟩) (canonicalMatch7_530) (canonicalDecode7_530)

def canonicalPose7_531 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, false, false, false, true, true], ![2, 0, 0, 0, 0, 2, 1]⟩
def canonicalBox7_531 : BoxKey 7 :=
  ⟨![255360, 0, 114240, 107520, 100800, 241920, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, -560, 114688, 108010, 101360, 241535, 60080], true⟩

theorem canonicalMatch7_531 :
    canonicalPose7_531.boxKey 188160 (referenceBox7 (!canonicalBox7_531.bump)) = canonicalBox7_531 := by decide +kernel

theorem canonicalDecode7_531 : canonicalBox7_531.toKeyData 188160 = keys7Chunk16.get ⟨19, by decide⟩ := by
  change canonicalBox7_531.toKeyData 188160 = ⟨![(19 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (9 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (-1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_531 : keySolid (keys7Chunk16.get ⟨19, by decide⟩) = canonicalPose7_531.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_531 (box := canonicalBox7_531) (k := keys7Chunk16.get ⟨19, by decide⟩) (canonicalMatch7_531) (canonicalDecode7_531)

def canonicalPose7_532 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, false, false, false, false, false, false], ![1, 0, 0, 0, 0, 1, 0]⟩
def canonicalBox7_532 : BoxKey 7 :=
  ⟨![309120, 114240, 0, 107520, 100800, 322560, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 114688, 560, 108010, 101360, 322945, 128080], false⟩

theorem canonicalMatch7_532 :
    canonicalPose7_532.boxKey 188160 (referenceBox7 (!canonicalBox7_532.bump)) = canonicalBox7_532 := by decide +kernel

theorem canonicalDecode7_532 : canonicalBox7_532.toKeyData 188160 = keys7Chunk16.get ⟨20, by decide⟩ := by
  change canonicalBox7_532.toKeyData 188160 = ⟨![(23 / 14), (17 / 28), 0, (4 / 7), (15 / 28), (12 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (64 / 105), (1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_532 : keySolid (keys7Chunk16.get ⟨20, by decide⟩) = canonicalPose7_532.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_532 (box := canonicalBox7_532) (k := keys7Chunk16.get ⟨20, by decide⟩) (canonicalMatch7_532) (canonicalDecode7_532)

def canonicalPose7_533 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, false, false, true, false, false, false], ![1, 0, 0, 0, 0, 1, 0]⟩
def canonicalBox7_533 : BoxKey 7 :=
  ⟨![322560, 100800, 107520, 0, 114240, 309120, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 101360, 108010, -560, 114688, 309540, 128080], true⟩

theorem canonicalMatch7_533 :
    canonicalPose7_533.boxKey 188160 (referenceBox7 (!canonicalBox7_533.bump)) = canonicalBox7_533 := by decide +kernel

theorem canonicalDecode7_533 : canonicalBox7_533.toKeyData 188160 = keys7Chunk16.get ⟨21, by decide⟩ := by
  change canonicalBox7_533.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (4 / 7), 0, (17 / 28), (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (1543 / 2688), (-1 / 336), (64 / 105), (737 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_533 : keySolid (keys7Chunk16.get ⟨21, by decide⟩) = canonicalPose7_533.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_533 (box := canonicalBox7_533) (k := keys7Chunk16.get ⟨21, by decide⟩) (canonicalMatch7_533) (canonicalDecode7_533)

def canonicalPose7_534 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, false, false, false, true, true], ![2, 0, 0, 0, 0, 2, 1]⟩
def canonicalBox7_534 : BoxKey 7 :=
  ⟨![241920, 100800, 107520, 114240, 0, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 101360, 108010, 114688, 560, 254940, 60080], false⟩

theorem canonicalMatch7_534 :
    canonicalPose7_534.boxKey 188160 (referenceBox7 (!canonicalBox7_534.bump)) = canonicalBox7_534 := by decide +kernel

theorem canonicalDecode7_534 : canonicalBox7_534.toKeyData 188160 = keys7Chunk16.get ⟨22, by decide⟩ := by
  change canonicalBox7_534.toKeyData 188160 = ⟨![(9 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (1 / 336), (607 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_534 : keySolid (keys7Chunk16.get ⟨22, by decide⟩) = canonicalPose7_534.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_534 (box := canonicalBox7_534) (k := keys7Chunk16.get ⟨22, by decide⟩) (canonicalMatch7_534) (canonicalDecode7_534)

def canonicalPose7_535 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, true, true, false, true, false], ![2, 0, 1, 1, 0, 2, 0]⟩
def canonicalBox7_535 : BoxKey 7 :=
  ⟨![268800, 100800, 53760, 60480, 120960, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 53375, 60080, 121380, 375760, 114688], false⟩

theorem canonicalMatch7_535 :
    canonicalPose7_535.boxKey 188160 (referenceBox7 (!canonicalBox7_535.bump)) = canonicalBox7_535 := by decide +kernel

theorem canonicalDecode7_535 : canonicalBox7_535.toKeyData 188160 = keys7Chunk16.get ⟨23, by decide⟩ := by
  change canonicalBox7_535.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_535 : keySolid (keys7Chunk16.get ⟨23, by decide⟩) = canonicalPose7_535.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_535 (box := canonicalBox7_535) (k := keys7Chunk16.get ⟨23, by decide⟩) (canonicalMatch7_535) (canonicalDecode7_535)

def canonicalPose7_536 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, false, false, false, false], ![1, 0, 0, 0, 0, 1, 0]⟩
def canonicalBox7_536 : BoxKey 7 :=
  ⟨![302400, 107520, 100800, 134400, 127680, 309120, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 108010, 101360, 134785, 128080, 309540, 560], false⟩

theorem canonicalMatch7_536 :
    canonicalPose7_536.boxKey 188160 (referenceBox7 (!canonicalBox7_536.bump)) = canonicalBox7_536 := by decide +kernel

theorem canonicalDecode7_536 : canonicalBox7_536.toKeyData 188160 = keys7Chunk16.get ⟨24, by decide⟩ := by
  change canonicalBox7_536.toKeyData 188160 = ⟨![(45 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28), (23 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_536 : keySolid (keys7Chunk16.get ⟨24, by decide⟩) = canonicalPose7_536.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_536 (box := canonicalBox7_536) (k := keys7Chunk16.get ⟨24, by decide⟩) (canonicalMatch7_536) (canonicalDecode7_536)

def canonicalPose7_537 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, false, false, true], ![1, 0, 0, 0, 0, 1, 0]⟩
def canonicalBox7_537 : BoxKey 7 :=
  ⟨![309120, 127680, 134400, 100800, 107520, 302400, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 128080, 134785, 101360, 108010, 302848, -560], true⟩

theorem canonicalMatch7_537 :
    canonicalPose7_537.boxKey 188160 (referenceBox7 (!canonicalBox7_537.bump)) = canonicalBox7_537 := by decide +kernel

theorem canonicalDecode7_537 : canonicalBox7_537.toKeyData 188160 = keys7Chunk16.get ⟨25, by decide⟩ := by
  change canonicalBox7_537.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7), (45 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_537 : keySolid (keys7Chunk16.get ⟨25, by decide⟩) = canonicalPose7_537.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_537 (box := canonicalBox7_537) (k := keys7Chunk16.get ⟨25, by decide⟩) (canonicalMatch7_537) (canonicalDecode7_537)

def canonicalPose7_538 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, true, true, false, true, true], ![2, 0, 1, 1, 0, 2, 2]⟩
def canonicalBox7_538 : BoxKey 7 :=
  ⟨![376320, 120960, 60480, 53760, 100800, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 121380, 60080, 53375, 101360, 268310, 261632], false⟩

theorem canonicalMatch7_538 :
    canonicalPose7_538.boxKey 188160 (referenceBox7 (!canonicalBox7_538.bump)) = canonicalBox7_538 := by decide +kernel

theorem canonicalDecode7_538 : canonicalBox7_538.toKeyData 188160 = keys7Chunk16.get ⟨26, by decide⟩ := by
  change canonicalBox7_538.toKeyData 188160 = ⟨![2, (9 / 14), (9 / 28), (2 / 7), (15 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_538 : keySolid (keys7Chunk16.get ⟨26, by decide⟩) = canonicalPose7_538.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_538 (box := canonicalBox7_538) (k := keys7Chunk16.get ⟨26, by decide⟩) (canonicalMatch7_538) (canonicalDecode7_538)

def canonicalPose7_539 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, false, false, false, true, false], ![2, 0, 0, 0, 0, 2, 1]⟩
def canonicalBox7_539 : BoxKey 7 :=
  ⟨![255360, 0, 114240, 107520, 100800, 241920, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 560, 114688, 108010, 101360, 241535, 316240], false⟩

theorem canonicalMatch7_539 :
    canonicalPose7_539.boxKey 188160 (referenceBox7 (!canonicalBox7_539.bump)) = canonicalBox7_539 := by decide +kernel

theorem canonicalDecode7_539 : canonicalBox7_539.toKeyData 188160 = keys7Chunk16.get ⟨27, by decide⟩ := by
  change canonicalBox7_539.toKeyData 188160 = ⟨![(19 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (9 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_539 : keySolid (keys7Chunk16.get ⟨27, by decide⟩) = canonicalPose7_539.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_539 (box := canonicalBox7_539) (k := keys7Chunk16.get ⟨27, by decide⟩) (canonicalMatch7_539) (canonicalDecode7_539)

def canonicalPose7_540 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, false, true, false, false, false, true], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_540 : BoxKey 7 :=
  ⟨![309120, 114240, 0, 107520, 100800, 322560, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 114688, -560, 108010, 101360, 322945, 248240], true⟩

theorem canonicalMatch7_540 :
    canonicalPose7_540.boxKey 188160 (referenceBox7 (!canonicalBox7_540.bump)) = canonicalBox7_540 := by decide +kernel

theorem canonicalDecode7_540 : canonicalBox7_540.toKeyData 188160 = keys7Chunk16.get ⟨28, by decide⟩ := by
  change canonicalBox7_540.toKeyData 188160 = ⟨![(23 / 14), (17 / 28), 0, (4 / 7), (15 / 28), (12 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (64 / 105), (-1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_540 : keySolid (keys7Chunk16.get ⟨28, by decide⟩) = canonicalPose7_540.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_540 (box := canonicalBox7_540) (k := keys7Chunk16.get ⟨28, by decide⟩) (canonicalMatch7_540) (canonicalDecode7_540)

def canonicalPose7_541 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, false, false, false, false, false, true], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_541 : BoxKey 7 :=
  ⟨![322560, 100800, 107520, 0, 114240, 309120, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 101360, 108010, 560, 114688, 309540, 248240], false⟩

theorem canonicalMatch7_541 :
    canonicalPose7_541.boxKey 188160 (referenceBox7 (!canonicalBox7_541.bump)) = canonicalBox7_541 := by decide +kernel

theorem canonicalDecode7_541 : canonicalBox7_541.toKeyData 188160 = keys7Chunk16.get ⟨29, by decide⟩ := by
  change canonicalBox7_541.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (4 / 7), 0, (17 / 28), (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (1543 / 2688), (1 / 336), (64 / 105), (737 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_541 : keySolid (keys7Chunk16.get ⟨29, by decide⟩) = canonicalPose7_541.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_541 (box := canonicalBox7_541) (k := keys7Chunk16.get ⟨29, by decide⟩) (canonicalMatch7_541) (canonicalDecode7_541)

def canonicalPose7_542 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, false, false, true, true, false], ![2, 0, 0, 0, 0, 2, 1]⟩
def canonicalBox7_542 : BoxKey 7 :=
  ⟨![241920, 100800, 107520, 114240, 0, 255360, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 101360, 108010, 114688, -560, 254940, 316240], true⟩

theorem canonicalMatch7_542 :
    canonicalPose7_542.boxKey 188160 (referenceBox7 (!canonicalBox7_542.bump)) = canonicalBox7_542 := by decide +kernel

theorem canonicalDecode7_542 : canonicalBox7_542.toKeyData 188160 = keys7Chunk16.get ⟨30, by decide⟩ := by
  change canonicalBox7_542.toKeyData 188160 = ⟨![(9 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_542 : keySolid (keys7Chunk16.get ⟨30, by decide⟩) = canonicalPose7_542.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_542 (box := canonicalBox7_542) (k := keys7Chunk16.get ⟨30, by decide⟩) (canonicalMatch7_542) (canonicalDecode7_542)

def canonicalPose7_543 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, true, true, false, false, true], ![2, 0, 1, 1, 0, 2, 2]⟩
def canonicalBox7_543 : BoxKey 7 :=
  ⟨![268800, 100800, 53760, 60480, 120960, 376320, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 53375, 60080, 121380, 376880, 261632], true⟩

theorem canonicalMatch7_543 :
    canonicalPose7_543.boxKey 188160 (referenceBox7 (!canonicalBox7_543.bump)) = canonicalBox7_543 := by decide +kernel

theorem canonicalDecode7_543 : canonicalBox7_543.toKeyData 188160 = keys7Chunk16.get ⟨31, by decide⟩ := by
  change canonicalBox7_543.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14), 2, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (673 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_543 : keySolid (keys7Chunk16.get ⟨31, by decide⟩) = canonicalPose7_543.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_543 (box := canonicalBox7_543) (k := keys7Chunk16.get ⟨31, by decide⟩) (canonicalMatch7_543) (canonicalDecode7_543)

theorem keys7Chunk16_canonical : ∀ k ∈ keys7Chunk16,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk16, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_512, canonicalSolid7_512⟩
  · exact ⟨canonicalPose7_513, canonicalSolid7_513⟩
  · exact ⟨canonicalPose7_514, canonicalSolid7_514⟩
  · exact ⟨canonicalPose7_515, canonicalSolid7_515⟩
  · exact ⟨canonicalPose7_516, canonicalSolid7_516⟩
  · exact ⟨canonicalPose7_517, canonicalSolid7_517⟩
  · exact ⟨canonicalPose7_518, canonicalSolid7_518⟩
  · exact ⟨canonicalPose7_519, canonicalSolid7_519⟩
  · exact ⟨canonicalPose7_520, canonicalSolid7_520⟩
  · exact ⟨canonicalPose7_521, canonicalSolid7_521⟩
  · exact ⟨canonicalPose7_522, canonicalSolid7_522⟩
  · exact ⟨canonicalPose7_523, canonicalSolid7_523⟩
  · exact ⟨canonicalPose7_524, canonicalSolid7_524⟩
  · exact ⟨canonicalPose7_525, canonicalSolid7_525⟩
  · exact ⟨canonicalPose7_526, canonicalSolid7_526⟩
  · exact ⟨canonicalPose7_527, canonicalSolid7_527⟩
  · exact ⟨canonicalPose7_528, canonicalSolid7_528⟩
  · exact ⟨canonicalPose7_529, canonicalSolid7_529⟩
  · exact ⟨canonicalPose7_530, canonicalSolid7_530⟩
  · exact ⟨canonicalPose7_531, canonicalSolid7_531⟩
  · exact ⟨canonicalPose7_532, canonicalSolid7_532⟩
  · exact ⟨canonicalPose7_533, canonicalSolid7_533⟩
  · exact ⟨canonicalPose7_534, canonicalSolid7_534⟩
  · exact ⟨canonicalPose7_535, canonicalSolid7_535⟩
  · exact ⟨canonicalPose7_536, canonicalSolid7_536⟩
  · exact ⟨canonicalPose7_537, canonicalSolid7_537⟩
  · exact ⟨canonicalPose7_538, canonicalSolid7_538⟩
  · exact ⟨canonicalPose7_539, canonicalSolid7_539⟩
  · exact ⟨canonicalPose7_540, canonicalSolid7_540⟩
  · exact ⟨canonicalPose7_541, canonicalSolid7_541⟩
  · exact ⟨canonicalPose7_542, canonicalSolid7_542⟩
  · exact ⟨canonicalPose7_543, canonicalSolid7_543⟩

#print axioms keys7Chunk16_canonical

end SparseMonotiles.Canonical
