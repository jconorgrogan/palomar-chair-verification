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

def canonicalPose7_480 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, false, true, false, false], ![0, 2, 1, 1, 2, 0, 0]⟩
def canonicalBox7_480 : BoxKey 7 :=
  ⟨![0, 255360, 315840, 322560, 275520, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 254940, 316240, 322945, 274960, 108010, 114688], true⟩

theorem canonicalMatch7_480 :
    canonicalPose7_480.boxKey 188160 (referenceBox7 (!canonicalBox7_480.bump)) = canonicalBox7_480 := by decide +kernel

theorem canonicalDecode7_480 : canonicalBox7_480.toKeyData 188160 = keys7Chunk15.get ⟨0, by decide⟩ := by
  change canonicalBox7_480.toKeyData 188160 = ⟨![0, (19 / 14), (47 / 28), (12 / 7), (41 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_480 : keySolid (keys7Chunk15.get ⟨0, by decide⟩) = canonicalPose7_480.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_480 (box := canonicalBox7_480) (k := keys7Chunk15.get ⟨0, by decide⟩) (canonicalMatch7_480) (canonicalDecode7_480)

def canonicalPose7_481 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, true, true, true, false, true], ![0, 2, 2, 2, 2, 0, 1]⟩
def canonicalBox7_481 : BoxKey 7 :=
  ⟨![120960, 376320, 262080, 268800, 275520, 134400, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 376880, 261632, 268310, 274960, 134785, 60080], true⟩

theorem canonicalMatch7_481 :
    canonicalPose7_481.boxKey 188160 (referenceBox7 (!canonicalBox7_481.bump)) = canonicalBox7_481 := by decide +kernel

theorem canonicalDecode7_481 : canonicalBox7_481.toKeyData 188160 = keys7Chunk15.get ⟨1, by decide⟩ := by
  change canonicalBox7_481.toKeyData 188160 = ⟨![(9 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (5 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_481 : keySolid (keys7Chunk15.get ⟨1, by decide⟩) = canonicalPose7_481.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_481 (box := canonicalBox7_481) (k := keys7Chunk15.get ⟨1, by decide⟩) (canonicalMatch7_481) (canonicalDecode7_481)

def canonicalPose7_482 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, true, true, true, true, true, false], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_482 : BoxKey 7 :=
  ⟨![67200, 262080, 376320, 268800, 275520, 53760, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 261632, 375760, 268310, 274960, 53375, 128080], false⟩

theorem canonicalMatch7_482 :
    canonicalPose7_482.boxKey 188160 (referenceBox7 (!canonicalBox7_482.bump)) = canonicalBox7_482 := by decide +kernel

theorem canonicalDecode7_482 : canonicalBox7_482.toKeyData 188160 = keys7Chunk15.get ⟨2, by decide⟩ := by
  change canonicalBox7_482.toKeyData 188160 = ⟨![(5 / 14), (39 / 28), 2, (10 / 7), (41 / 28), (2 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (146 / 105), (671 / 336), (3833 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_482 : keySolid (keys7Chunk15.get ⟨2, by decide⟩) = canonicalPose7_482.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_482 (box := canonicalBox7_482) (k := keys7Chunk15.get ⟨2, by decide⟩) (canonicalMatch7_482) (canonicalDecode7_482)

def canonicalPose7_483 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, true, true, false, true, true, false], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_483 : BoxKey 7 :=
  ⟨![53760, 275520, 268800, 376320, 262080, 67200, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 274960, 268310, 376880, 261632, 66780, 128080], true⟩

theorem canonicalMatch7_483 :
    canonicalPose7_483.boxKey 188160 (referenceBox7 (!canonicalBox7_483.bump)) = canonicalBox7_483 := by decide +kernel

theorem canonicalDecode7_483 : canonicalBox7_483.toKeyData 188160 = keys7Chunk15.get ⟨3, by decide⟩ := by
  change canonicalBox7_483.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (10 / 7), 2, (39 / 28), (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (3833 / 2688), (673 / 336), (146 / 105), (159 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_483 : keySolid (keys7Chunk15.get ⟨3, by decide⟩) = canonicalPose7_483.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_483 (box := canonicalBox7_483) (k := keys7Chunk15.get ⟨3, by decide⟩) (canonicalMatch7_483) (canonicalDecode7_483)

def canonicalPose7_484 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, true, true, true, false, true], ![0, 2, 2, 2, 2, 0, 1]⟩
def canonicalBox7_484 : BoxKey 7 :=
  ⟨![134400, 275520, 268800, 262080, 376320, 120960, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 274960, 268310, 261632, 375760, 121380, 60080], false⟩

theorem canonicalMatch7_484 :
    canonicalPose7_484.boxKey 188160 (referenceBox7 (!canonicalBox7_484.bump)) = canonicalBox7_484 := by decide +kernel

theorem canonicalDecode7_484 : canonicalBox7_484.toKeyData 188160 = keys7Chunk15.get ⟨4, by decide⟩ := by
  change canonicalBox7_484.toKeyData 188160 = ⟨![(5 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_484 : keySolid (keys7Chunk15.get ⟨4, by decide⟩) = canonicalPose7_484.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_484 (box := canonicalBox7_484) (k := keys7Chunk15.get ⟨4, by decide⟩) (canonicalMatch7_484) (canonicalDecode7_484)

def canonicalPose7_485 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, false, false, true, false, false], ![0, 2, 1, 1, 2, 0, 0]⟩
def canonicalBox7_485 : BoxKey 7 :=
  ⟨![107520, 275520, 322560, 315840, 255360, 0, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 322945, 316240, 254940, 560, 114688], false⟩

theorem canonicalMatch7_485 :
    canonicalPose7_485.boxKey 188160 (referenceBox7 (!canonicalBox7_485.bump)) = canonicalBox7_485 := by decide +kernel

theorem canonicalDecode7_485 : canonicalBox7_485.toKeyData 188160 = keys7Chunk15.get ⟨5, by decide⟩ := by
  change canonicalBox7_485.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14), 0, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_485 : keySolid (keys7Chunk15.get ⟨5, by decide⟩) = canonicalPose7_485.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_485 (box := canonicalBox7_485) (k := keys7Chunk15.get ⟨5, by decide⟩) (canonicalMatch7_485) (canonicalDecode7_485)

def canonicalPose7_486 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, true, true, true, true, false], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_486 : BoxKey 7 :=
  ⟨![73920, 268800, 275520, 241920, 248640, 67200, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 268310, 274960, 241535, 248240, 66780, 560], false⟩

theorem canonicalMatch7_486 :
    canonicalPose7_486.boxKey 188160 (referenceBox7 (!canonicalBox7_486.bump)) = canonicalBox7_486 := by decide +kernel

theorem canonicalDecode7_486 : canonicalBox7_486.toKeyData 188160 = keys7Chunk15.get ⟨6, by decide⟩ := by
  change canonicalBox7_486.toKeyData 188160 = ⟨![(11 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28), (5 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_486 : keySolid (keys7Chunk15.get ⟨6, by decide⟩) = canonicalPose7_486.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_486 (box := canonicalBox7_486) (k := keys7Chunk15.get ⟨6, by decide⟩) (canonicalMatch7_486) (canonicalDecode7_486)

def canonicalPose7_487 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, true, true, true], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_487 : BoxKey 7 :=
  ⟨![67200, 248640, 241920, 275520, 268800, 73920, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 248240, 241535, 274960, 268310, 73472, -560], true⟩

theorem canonicalMatch7_487 :
    canonicalPose7_487.boxKey 188160 (referenceBox7 (!canonicalBox7_487.bump)) = canonicalBox7_487 := by decide +kernel

theorem canonicalDecode7_487 : canonicalBox7_487.toKeyData 188160 = keys7Chunk15.get ⟨7, by decide⟩ := by
  change canonicalBox7_487.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7), (11 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_487 : keySolid (keys7Chunk15.get ⟨7, by decide⟩) = canonicalPose7_487.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_487 (box := canonicalBox7_487) (k := keys7Chunk15.get ⟨7, by decide⟩) (canonicalMatch7_487) (canonicalDecode7_487)

def canonicalPose7_488 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, false, false, true, false, true], ![0, 2, 1, 1, 2, 0, 2]⟩
def canonicalBox7_488 : BoxKey 7 :=
  ⟨![0, 255360, 315840, 322560, 275520, 107520, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 254940, 316240, 322945, 274960, 108010, 261632], false⟩

theorem canonicalMatch7_488 :
    canonicalPose7_488.boxKey 188160 (referenceBox7 (!canonicalBox7_488.bump)) = canonicalBox7_488 := by decide +kernel

theorem canonicalDecode7_488 : canonicalBox7_488.toKeyData 188160 = keys7Chunk15.get ⟨8, by decide⟩ := by
  change canonicalBox7_488.toKeyData 188160 = ⟨![0, (19 / 14), (47 / 28), (12 / 7), (41 / 28), (4 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_488 : keySolid (keys7Chunk15.get ⟨8, by decide⟩) = canonicalPose7_488.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_488 (box := canonicalBox7_488) (k := keys7Chunk15.get ⟨8, by decide⟩) (canonicalMatch7_488) (canonicalDecode7_488)

def canonicalPose7_489 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, true, true, true, false, false], ![0, 2, 2, 2, 2, 0, 1]⟩
def canonicalBox7_489 : BoxKey 7 :=
  ⟨![120960, 376320, 262080, 268800, 275520, 134400, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 375760, 261632, 268310, 274960, 134785, 316240], false⟩

theorem canonicalMatch7_489 :
    canonicalPose7_489.boxKey 188160 (referenceBox7 (!canonicalBox7_489.bump)) = canonicalBox7_489 := by decide +kernel

theorem canonicalDecode7_489 : canonicalBox7_489.toKeyData 188160 = keys7Chunk15.get ⟨9, by decide⟩ := by
  change canonicalBox7_489.toKeyData 188160 = ⟨![(9 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (5 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (671 / 336), (146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_489 : keySolid (keys7Chunk15.get ⟨9, by decide⟩) = canonicalPose7_489.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_489 (box := canonicalBox7_489) (k := keys7Chunk15.get ⟨9, by decide⟩) (canonicalMatch7_489) (canonicalDecode7_489)

def canonicalPose7_490 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, true, false, true, true, true, true], ![1, 2, 2, 2, 2, 1, 2]⟩
def canonicalBox7_490 : BoxKey 7 :=
  ⟨![67200, 262080, 376320, 268800, 275520, 53760, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 261632, 376880, 268310, 274960, 53375, 248240], true⟩

theorem canonicalMatch7_490 :
    canonicalPose7_490.boxKey 188160 (referenceBox7 (!canonicalBox7_490.bump)) = canonicalBox7_490 := by decide +kernel

theorem canonicalDecode7_490 : canonicalBox7_490.toKeyData 188160 = keys7Chunk15.get ⟨10, by decide⟩ := by
  change canonicalBox7_490.toKeyData 188160 = ⟨![(5 / 14), (39 / 28), 2, (10 / 7), (41 / 28), (2 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (146 / 105), (673 / 336), (3833 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_490 : keySolid (keys7Chunk15.get ⟨10, by decide⟩) = canonicalPose7_490.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_490 (box := canonicalBox7_490) (k := keys7Chunk15.get ⟨10, by decide⟩) (canonicalMatch7_490) (canonicalDecode7_490)

def canonicalPose7_491 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, true, true, true, true, true, true], ![1, 2, 2, 2, 2, 1, 2]⟩
def canonicalBox7_491 : BoxKey 7 :=
  ⟨![53760, 275520, 268800, 376320, 262080, 67200, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 274960, 268310, 375760, 261632, 66780, 248240], false⟩

theorem canonicalMatch7_491 :
    canonicalPose7_491.boxKey 188160 (referenceBox7 (!canonicalBox7_491.bump)) = canonicalBox7_491 := by decide +kernel

theorem canonicalDecode7_491 : canonicalBox7_491.toKeyData 188160 = keys7Chunk15.get ⟨11, by decide⟩ := by
  change canonicalBox7_491.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (10 / 7), 2, (39 / 28), (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (3833 / 2688), (671 / 336), (146 / 105), (159 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_491 : keySolid (keys7Chunk15.get ⟨11, by decide⟩) = canonicalPose7_491.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_491 (box := canonicalBox7_491) (k := keys7Chunk15.get ⟨11, by decide⟩) (canonicalMatch7_491) (canonicalDecode7_491)

def canonicalPose7_492 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, true, true, false, false, false], ![0, 2, 2, 2, 2, 0, 1]⟩
def canonicalBox7_492 : BoxKey 7 :=
  ⟨![134400, 275520, 268800, 262080, 376320, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 274960, 268310, 261632, 376880, 121380, 316240], true⟩

theorem canonicalMatch7_492 :
    canonicalPose7_492.boxKey 188160 (referenceBox7 (!canonicalBox7_492.bump)) = canonicalBox7_492 := by decide +kernel

theorem canonicalDecode7_492 : canonicalBox7_492.toKeyData 188160 = keys7Chunk15.get ⟨12, by decide⟩ := by
  change canonicalBox7_492.toKeyData 188160 = ⟨![(5 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (673 / 336), (289 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_492 : keySolid (keys7Chunk15.get ⟨12, by decide⟩) = canonicalPose7_492.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_492 (box := canonicalBox7_492) (k := keys7Chunk15.get ⟨12, by decide⟩) (canonicalMatch7_492) (canonicalDecode7_492)

def canonicalPose7_493 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, false, false, true, true, true], ![0, 2, 1, 1, 2, 0, 2]⟩
def canonicalBox7_493 : BoxKey 7 :=
  ⟨![107520, 275520, 322560, 315840, 255360, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 322945, 316240, 254940, -560, 261632], true⟩

theorem canonicalMatch7_493 :
    canonicalPose7_493.boxKey 188160 (referenceBox7 (!canonicalBox7_493.bump)) = canonicalBox7_493 := by decide +kernel

theorem canonicalDecode7_493 : canonicalBox7_493.toKeyData 188160 = keys7Chunk15.get ⟨13, by decide⟩ := by
  change canonicalBox7_493.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_493 : keySolid (keys7Chunk15.get ⟨13, by decide⟩) = canonicalPose7_493.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_493 (box := canonicalBox7_493) (k := keys7Chunk15.get ⟨13, by decide⟩) (canonicalMatch7_493) (canonicalDecode7_493)

def canonicalPose7_494 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, true, true, true, true, false], ![1, 2, 2, 2, 2, 1, 2]⟩
def canonicalBox7_494 : BoxKey 7 :=
  ⟨![73920, 268800, 275520, 241920, 248640, 67200, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 268310, 274960, 241535, 248240, 66780, 376880], true⟩

theorem canonicalMatch7_494 :
    canonicalPose7_494.boxKey 188160 (referenceBox7 (!canonicalBox7_494.bump)) = canonicalBox7_494 := by decide +kernel

theorem canonicalDecode7_494 : canonicalBox7_494.toKeyData 188160 = keys7Chunk15.get ⟨14, by decide⟩ := by
  change canonicalBox7_494.toKeyData 188160 = ⟨![(11 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28), (5 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_494 : keySolid (keys7Chunk15.get ⟨14, by decide⟩) = canonicalPose7_494.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_494 (box := canonicalBox7_494) (k := keys7Chunk15.get ⟨14, by decide⟩) (canonicalMatch7_494) (canonicalDecode7_494)

def canonicalPose7_495 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, true, true, true], ![1, 2, 2, 2, 2, 1, 2]⟩
def canonicalBox7_495 : BoxKey 7 :=
  ⟨![67200, 248640, 241920, 275520, 268800, 73920, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 248240, 241535, 274960, 268310, 73472, 375760], false⟩

theorem canonicalMatch7_495 :
    canonicalPose7_495.boxKey 188160 (referenceBox7 (!canonicalBox7_495.bump)) = canonicalBox7_495 := by decide +kernel

theorem canonicalDecode7_495 : canonicalBox7_495.toKeyData 188160 = keys7Chunk15.get ⟨15, by decide⟩ := by
  change canonicalBox7_495.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7), (11 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_495 : keySolid (keys7Chunk15.get ⟨15, by decide⟩) = canonicalPose7_495.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_495 (box := canonicalBox7_495) (k := keys7Chunk15.get ⟨15, by decide⟩) (canonicalMatch7_495) (canonicalDecode7_495)

def canonicalPose7_496 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, true, false, true, false, true, false], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_496 : BoxKey 7 :=
  ⟨![0, 262080, 309120, 248640, 322560, 275520, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![560, 261632, 309540, 248240, 322945, 274960, 108010], false⟩

theorem canonicalMatch7_496 :
    canonicalPose7_496.boxKey 188160 (referenceBox7 (!canonicalBox7_496.bump)) = canonicalBox7_496 := by decide +kernel

theorem canonicalDecode7_496 : canonicalBox7_496.toKeyData 188160 = keys7Chunk15.get ⟨16, by decide⟩ := by
  change canonicalBox7_496.toKeyData 188160 = ⟨![0, (39 / 28), (23 / 14), (37 / 28), (12 / 7), (41 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(1 / 336), (146 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_496 : keySolid (keys7Chunk15.get ⟨16, by decide⟩) = canonicalPose7_496.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_496 (box := canonicalBox7_496) (k := keys7Chunk15.get ⟨16, by decide⟩) (canonicalMatch7_496) (canonicalDecode7_496)

def canonicalPose7_497 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, true, false, true, true, false], ![0, 2, 2, 1, 2, 2, 0]⟩
def canonicalBox7_497 : BoxKey 7 :=
  ⟨![114240, 376320, 255360, 315840, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 376880, 254940, 316240, 241535, 274960, 108010], true⟩

theorem canonicalMatch7_497 :
    canonicalPose7_497.boxKey 188160 (referenceBox7 (!canonicalBox7_497.bump)) = canonicalBox7_497 := by decide +kernel

theorem canonicalDecode7_497 : canonicalBox7_497.toKeyData 188160 = keys7Chunk15.get ⟨17, by decide⟩ := by
  change canonicalBox7_497.toKeyData 188160 = ⟨![(17 / 28), 2, (19 / 14), (47 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (673 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_497 : keySolid (keys7Chunk15.get ⟨17, by decide⟩) = canonicalPose7_497.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_497 (box := canonicalBox7_497) (k := keys7Chunk15.get ⟨17, by decide⟩) (canonicalMatch7_497) (canonicalDecode7_497)

def canonicalPose7_498 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, true, true, true, true], ![1, 2, 2, 2, 2, 2, 1]⟩
def canonicalBox7_498 : BoxKey 7 :=
  ⟨![60480, 255360, 376320, 262080, 268800, 275520, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 376880, 261632, 268310, 274960, 53375], true⟩

theorem canonicalMatch7_498 :
    canonicalPose7_498.boxKey 188160 (referenceBox7 (!canonicalBox7_498.bump)) = canonicalBox7_498 := by decide +kernel

theorem canonicalDecode7_498 : canonicalBox7_498.toKeyData 188160 = keys7Chunk15.get ⟨18, by decide⟩ := by
  change canonicalBox7_498.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_498 : keySolid (keys7Chunk15.get ⟨18, by decide⟩) = canonicalPose7_498.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_498 (box := canonicalBox7_498) (k := keys7Chunk15.get ⟨18, by decide⟩) (canonicalMatch7_498) (canonicalDecode7_498)

def canonicalPose7_499 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, true, false, true, false], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_499 : BoxKey 7 :=
  ⟨![100800, 268800, 302400, 376320, 309120, 248640, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 302848, 375760, 309540, 248240, 134785], false⟩

theorem canonicalMatch7_499 :
    canonicalPose7_499.boxKey 188160 (referenceBox7 (!canonicalBox7_499.bump)) = canonicalBox7_499 := by decide +kernel

theorem canonicalDecode7_499 : canonicalBox7_499.toKeyData 188160 = keys7Chunk15.get ⟨19, by decide⟩ := by
  change canonicalBox7_499.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (45 / 28), 2, (23 / 14), (37 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (169 / 105), (671 / 336), (737 / 448), (3103 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_499 : keySolid (keys7Chunk15.get ⟨19, by decide⟩) = canonicalPose7_499.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_499 (box := canonicalBox7_499) (k := keys7Chunk15.get ⟨19, by decide⟩) (canonicalMatch7_499) (canonicalDecode7_499)

def canonicalPose7_500 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, false, false, false, true, false], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_500 : BoxKey 7 :=
  ⟨![134400, 248640, 309120, 376320, 302400, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 248240, 309540, 376880, 302848, 268310, 101360], true⟩

theorem canonicalMatch7_500 :
    canonicalPose7_500.boxKey 188160 (referenceBox7 (!canonicalBox7_500.bump)) = canonicalBox7_500 := by decide +kernel

theorem canonicalDecode7_500 : canonicalBox7_500.toKeyData 188160 = keys7Chunk15.get ⟨20, by decide⟩ := by
  change canonicalBox7_500.toKeyData 188160 = ⟨![(5 / 7), (37 / 28), (23 / 14), 2, (45 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3103 / 2352), (737 / 448), (673 / 336), (169 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_500 : keySolid (keys7Chunk15.get ⟨20, by decide⟩) = canonicalPose7_500.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_500 (box := canonicalBox7_500) (k := keys7Chunk15.get ⟨20, by decide⟩) (canonicalMatch7_500) (canonicalDecode7_500)

def canonicalPose7_501 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, true, true, true, true], ![1, 2, 2, 2, 2, 2, 1]⟩
def canonicalBox7_501 : BoxKey 7 :=
  ⟨![53760, 275520, 268800, 262080, 376320, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 274960, 268310, 261632, 375760, 254940, 60080], false⟩

theorem canonicalMatch7_501 :
    canonicalPose7_501.boxKey 188160 (referenceBox7 (!canonicalBox7_501.bump)) = canonicalBox7_501 := by decide +kernel

theorem canonicalDecode7_501 : canonicalBox7_501.toKeyData 188160 = keys7Chunk15.get ⟨21, by decide⟩ := by
  change canonicalBox7_501.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (607 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_501 : keySolid (keys7Chunk15.get ⟨21, by decide⟩) = canonicalPose7_501.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_501 (box := canonicalBox7_501) (k := keys7Chunk15.get ⟨21, by decide⟩) (canonicalMatch7_501) (canonicalDecode7_501)

def canonicalPose7_502 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, false, true, true, false], ![0, 2, 2, 1, 2, 2, 0]⟩
def canonicalBox7_502 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 315840, 255360, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 316240, 254940, 375760, 114688], false⟩

theorem canonicalMatch7_502 :
    canonicalPose7_502.boxKey 188160 (referenceBox7 (!canonicalBox7_502.bump)) = canonicalBox7_502 := by decide +kernel

theorem canonicalDecode7_502 : canonicalBox7_502.toKeyData 188160 = keys7Chunk15.get ⟨22, by decide⟩ := by
  change canonicalBox7_502.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (47 / 28), (19 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_502 : keySolid (keys7Chunk15.get ⟨22, by decide⟩) = canonicalPose7_502.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_502 (box := canonicalBox7_502) (k := keys7Chunk15.get ⟨22, by decide⟩) (canonicalMatch7_502) (canonicalDecode7_502)

def canonicalPose7_503 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, true, false, true, false, true, true], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_503 : BoxKey 7 :=
  ⟨![107520, 275520, 322560, 248640, 309120, 262080, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 274960, 322945, 248240, 309540, 261632, -560], true⟩

theorem canonicalMatch7_503 :
    canonicalPose7_503.boxKey 188160 (referenceBox7 (!canonicalBox7_503.bump)) = canonicalBox7_503 := by decide +kernel

theorem canonicalDecode7_503 : canonicalBox7_503.toKeyData 188160 = keys7Chunk15.get ⟨23, by decide⟩ := by
  change canonicalBox7_503.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (12 / 7), (37 / 28), (23 / 14), (39 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (146 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_503 : keySolid (keys7Chunk15.get ⟨23, by decide⟩) = canonicalPose7_503.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_503 (box := canonicalBox7_503) (k := keys7Chunk15.get ⟨23, by decide⟩) (canonicalMatch7_503) (canonicalDecode7_503)

def canonicalPose7_504 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, true, true, true, true, false], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_504 : BoxKey 7 :=
  ⟨![0, 302400, 268800, 275520, 241920, 248640, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 302848, 268310, 274960, 241535, 248240, 309540], false⟩

theorem canonicalMatch7_504 :
    canonicalPose7_504.boxKey 188160 (referenceBox7 (!canonicalBox7_504.bump)) = canonicalBox7_504 := by decide +kernel

theorem canonicalDecode7_504 : canonicalBox7_504.toKeyData 188160 = keys7Chunk15.get ⟨24, by decide⟩ := by
  change canonicalBox7_504.toKeyData 188160 = ⟨![0, (45 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (169 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_504 : keySolid (keys7Chunk15.get ⟨24, by decide⟩) = canonicalPose7_504.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_504 (box := canonicalBox7_504) (k := keys7Chunk15.get ⟨24, by decide⟩) (canonicalMatch7_504) (canonicalDecode7_504)

def canonicalPose7_505 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, true, true, true, true, false], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_505 : BoxKey 7 :=
  ⟨![0, 309120, 248640, 241920, 275520, 268800, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 309540, 248240, 241535, 274960, 268310, 302848], true⟩

theorem canonicalMatch7_505 :
    canonicalPose7_505.boxKey 188160 (referenceBox7 (!canonicalBox7_505.bump)) = canonicalBox7_505 := by decide +kernel

theorem canonicalDecode7_505 : canonicalBox7_505.toKeyData 188160 = keys7Chunk15.get ⟨25, by decide⟩ := by
  change canonicalBox7_505.toKeyData 188160 = ⟨![0, (23 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (737 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_505 : keySolid (keys7Chunk15.get ⟨25, by decide⟩) = canonicalPose7_505.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_505 (box := canonicalBox7_505) (k := keys7Chunk15.get ⟨25, by decide⟩) (canonicalMatch7_505) (canonicalDecode7_505)

def canonicalPose7_506 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, false, false, false, false, true], ![1, 2, 1, 1, 1, 1, 2]⟩
def canonicalBox7_506 : BoxKey 7 :=
  ⟨![188160, 262080, 295680, 288960, 322560, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![188720, 261632, 296170, 289520, 322945, 316240, 254940], true⟩

theorem canonicalMatch7_506 :
    canonicalPose7_506.boxKey 188160 (referenceBox7 (!canonicalBox7_506.bump)) = canonicalBox7_506 := by decide +kernel

theorem canonicalDecode7_506 : canonicalBox7_506.toKeyData 188160 = keys7Chunk15.get ⟨26, by decide⟩ := by
  change canonicalBox7_506.toKeyData 188160 = ⟨![1, (39 / 28), (11 / 7), (43 / 28), (12 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(337 / 336), (146 / 105), (4231 / 2688), (517 / 336), (9227 / 5376), (3953 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_506 : keySolid (keys7Chunk15.get ⟨26, by decide⟩) = canonicalPose7_506.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_506 (box := canonicalBox7_506) (k := keys7Chunk15.get ⟨26, by decide⟩) (canonicalMatch7_506) (canonicalDecode7_506)

def canonicalPose7_507 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, false, false, false, true], ![1, 2, 1, 1, 1, 1, 2]⟩
def canonicalBox7_507 : BoxKey 7 :=
  ⟨![188160, 255360, 315840, 322560, 288960, 295680, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![187600, 254940, 316240, 322945, 289520, 296170, 261632], false⟩

theorem canonicalMatch7_507 :
    canonicalPose7_507.boxKey 188160 (referenceBox7 (!canonicalBox7_507.bump)) = canonicalBox7_507 := by decide +kernel

theorem canonicalDecode7_507 : canonicalBox7_507.toKeyData 188160 = keys7Chunk15.get ⟨27, by decide⟩ := by
  change canonicalBox7_507.toKeyData 188160 = ⟨![1, (19 / 14), (47 / 28), (12 / 7), (43 / 28), (11 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(335 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (517 / 336), (4231 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_507 : keySolid (keys7Chunk15.get ⟨27, by decide⟩) = canonicalPose7_507.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_507 (box := canonicalBox7_507) (k := keys7Chunk15.get ⟨27, by decide⟩) (canonicalMatch7_507) (canonicalDecode7_507)

def canonicalPose7_508 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, true, false, false, true, true], ![0, 2, 2, 1, 1, 2, 2]⟩
def canonicalBox7_508 : BoxKey 7 :=
  ⟨![114240, 376320, 255360, 315840, 322560, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 376880, 254940, 316240, 322945, 274960, 268310], true⟩

theorem canonicalMatch7_508 :
    canonicalPose7_508.boxKey 188160 (referenceBox7 (!canonicalBox7_508.bump)) = canonicalBox7_508 := by decide +kernel

theorem canonicalDecode7_508 : canonicalBox7_508.toKeyData 188160 = keys7Chunk15.get ⟨28, by decide⟩ := by
  change canonicalBox7_508.toKeyData 188160 = ⟨![(17 / 28), 2, (19 / 14), (47 / 28), (12 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (673 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_508 : keySolid (keys7Chunk15.get ⟨28, by decide⟩) = canonicalPose7_508.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_508 (box := canonicalBox7_508) (k := keys7Chunk15.get ⟨28, by decide⟩) (canonicalMatch7_508) (canonicalDecode7_508)

def canonicalPose7_509 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, true, true, true, true], ![1, 2, 2, 2, 2, 2, 2]⟩
def canonicalBox7_509 : BoxKey 7 :=
  ⟨![60480, 255360, 376320, 262080, 268800, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 376880, 261632, 268310, 274960, 241535], true⟩

theorem canonicalMatch7_509 :
    canonicalPose7_509.boxKey 188160 (referenceBox7 (!canonicalBox7_509.bump)) = canonicalBox7_509 := by decide +kernel

theorem canonicalDecode7_509 : canonicalBox7_509.toKeyData 188160 = keys7Chunk15.get ⟨29, by decide⟩ := by
  change canonicalBox7_509.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_509 : keySolid (keys7Chunk15.get ⟨29, by decide⟩) = canonicalPose7_509.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_509 (box := canonicalBox7_509) (k := keys7Chunk15.get ⟨29, by decide⟩) (canonicalMatch7_509) (canonicalDecode7_509)

def canonicalPose7_510 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, false, true, true, true, true, false], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_510 : BoxKey 7 :=
  ⟨![127680, 309120, 262080, 376320, 268800, 275520, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 309540, 261632, 375760, 268310, 274960, 322945], false⟩

theorem canonicalMatch7_510 :
    canonicalPose7_510.boxKey 188160 (referenceBox7 (!canonicalBox7_510.bump)) = canonicalBox7_510 := by decide +kernel

theorem canonicalDecode7_510 : canonicalBox7_510.toKeyData 188160 = keys7Chunk15.get ⟨30, by decide⟩ := by
  change canonicalBox7_510.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), (39 / 28), 2, (10 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (146 / 105), (671 / 336), (3833 / 2688), (491 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_510 : keySolid (keys7Chunk15.get ⟨30, by decide⟩) = canonicalPose7_510.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_510 (box := canonicalBox7_510) (k := keys7Chunk15.get ⟨30, by decide⟩) (canonicalMatch7_510) (canonicalDecode7_510)

def canonicalPose7_511 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, false, true, true, false, true, false], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_511 : BoxKey 7 :=
  ⟨![127680, 322560, 275520, 268800, 376320, 262080, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 322945, 274960, 268310, 376880, 261632, 309540], true⟩

theorem canonicalMatch7_511 :
    canonicalPose7_511.boxKey 188160 (referenceBox7 (!canonicalBox7_511.bump)) = canonicalBox7_511 := by decide +kernel

theorem canonicalDecode7_511 : canonicalBox7_511.toKeyData 188160 = keys7Chunk15.get ⟨31, by decide⟩ := by
  change canonicalBox7_511.toKeyData 188160 = ⟨![(19 / 28), (12 / 7), (41 / 28), (10 / 7), 2, (39 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688), (673 / 336), (146 / 105), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_511 : keySolid (keys7Chunk15.get ⟨31, by decide⟩) = canonicalPose7_511.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_511 (box := canonicalBox7_511) (k := keys7Chunk15.get ⟨31, by decide⟩) (canonicalMatch7_511) (canonicalDecode7_511)

theorem keys7Chunk15_canonical : ∀ k ∈ keys7Chunk15,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk15, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_480, canonicalSolid7_480⟩
  · exact ⟨canonicalPose7_481, canonicalSolid7_481⟩
  · exact ⟨canonicalPose7_482, canonicalSolid7_482⟩
  · exact ⟨canonicalPose7_483, canonicalSolid7_483⟩
  · exact ⟨canonicalPose7_484, canonicalSolid7_484⟩
  · exact ⟨canonicalPose7_485, canonicalSolid7_485⟩
  · exact ⟨canonicalPose7_486, canonicalSolid7_486⟩
  · exact ⟨canonicalPose7_487, canonicalSolid7_487⟩
  · exact ⟨canonicalPose7_488, canonicalSolid7_488⟩
  · exact ⟨canonicalPose7_489, canonicalSolid7_489⟩
  · exact ⟨canonicalPose7_490, canonicalSolid7_490⟩
  · exact ⟨canonicalPose7_491, canonicalSolid7_491⟩
  · exact ⟨canonicalPose7_492, canonicalSolid7_492⟩
  · exact ⟨canonicalPose7_493, canonicalSolid7_493⟩
  · exact ⟨canonicalPose7_494, canonicalSolid7_494⟩
  · exact ⟨canonicalPose7_495, canonicalSolid7_495⟩
  · exact ⟨canonicalPose7_496, canonicalSolid7_496⟩
  · exact ⟨canonicalPose7_497, canonicalSolid7_497⟩
  · exact ⟨canonicalPose7_498, canonicalSolid7_498⟩
  · exact ⟨canonicalPose7_499, canonicalSolid7_499⟩
  · exact ⟨canonicalPose7_500, canonicalSolid7_500⟩
  · exact ⟨canonicalPose7_501, canonicalSolid7_501⟩
  · exact ⟨canonicalPose7_502, canonicalSolid7_502⟩
  · exact ⟨canonicalPose7_503, canonicalSolid7_503⟩
  · exact ⟨canonicalPose7_504, canonicalSolid7_504⟩
  · exact ⟨canonicalPose7_505, canonicalSolid7_505⟩
  · exact ⟨canonicalPose7_506, canonicalSolid7_506⟩
  · exact ⟨canonicalPose7_507, canonicalSolid7_507⟩
  · exact ⟨canonicalPose7_508, canonicalSolid7_508⟩
  · exact ⟨canonicalPose7_509, canonicalSolid7_509⟩
  · exact ⟨canonicalPose7_510, canonicalSolid7_510⟩
  · exact ⟨canonicalPose7_511, canonicalSolid7_511⟩

#print axioms keys7Chunk15_canonical

end SparseMonotiles.Canonical
