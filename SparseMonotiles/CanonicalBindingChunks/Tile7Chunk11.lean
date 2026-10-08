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

def canonicalPose7_352 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, false, true, true, true, false], ![0, 2, 0, 2, 2, 1, 0]⟩
def canonicalBox7_352 : BoxKey 7 :=
  ⟨![0, 262080, 107520, 275520, 241920, 60480, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 261632, 108010, 274960, 241535, 60080, 121380], false⟩

theorem canonicalMatch7_352 :
    canonicalPose7_352.boxKey 188160 (referenceBox7 (!canonicalBox7_352.bump)) = canonicalBox7_352 := by decide +kernel

theorem canonicalDecode7_352 : canonicalBox7_352.toKeyData 188160 = keys7Chunk11.get ⟨0, by decide⟩ := by
  change canonicalBox7_352.toKeyData 188160 = ⟨![0, (39 / 28), (4 / 7), (41 / 28), (9 / 7), (9 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_352 : keySolid (keys7Chunk11.get ⟨0, by decide⟩) = canonicalPose7_352.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_352 (box := canonicalBox7_352) (k := keys7Chunk11.get ⟨0, by decide⟩) (canonicalMatch7_352) (canonicalDecode7_352)

def canonicalPose7_353 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, false, false, true, false, false, true], ![0, 2, 0, 2, 1, 0, 1]⟩
def canonicalBox7_353 : BoxKey 7 :=
  ⟨![114240, 376320, 107520, 275520, 322560, 127680, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, 376880, 108010, 274960, 322945, 128080, 66780], true⟩

theorem canonicalMatch7_353 :
    canonicalPose7_353.boxKey 188160 (referenceBox7 (!canonicalBox7_353.bump)) = canonicalBox7_353 := by decide +kernel

theorem canonicalDecode7_353 : canonicalBox7_353.toKeyData 188160 = keys7Chunk11.get ⟨1, by decide⟩ := by
  change canonicalBox7_353.toKeyData 188160 = ⟨![(17 / 28), 2, (4 / 7), (41 / 28), (12 / 7), (19 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (673 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_353 : keySolid (keys7Chunk11.get ⟨1, by decide⟩) = canonicalPose7_353.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_353 (box := canonicalBox7_353) (k := keys7Chunk11.get ⟨1, by decide⟩) (canonicalMatch7_353) (canonicalDecode7_353)

def canonicalPose7_354 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, true, false, true, false, false, true], ![0, 2, 0, 2, 1, 0, 1]⟩
def canonicalBox7_354 : BoxKey 7 :=
  ⟨![100800, 268800, 0, 262080, 309120, 127680, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 268310, 560, 261632, 309540, 128080, 53375], false⟩

theorem canonicalMatch7_354 :
    canonicalPose7_354.boxKey 188160 (referenceBox7 (!canonicalBox7_354.bump)) = canonicalBox7_354 := by decide +kernel

theorem canonicalDecode7_354 : canonicalBox7_354.toKeyData 188160 = keys7Chunk11.get ⟨2, by decide⟩ := by
  change canonicalBox7_354.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), 0, (39 / 28), (23 / 14), (19 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (1 / 336), (146 / 105), (737 / 448), (1601 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_354 : keySolid (keys7Chunk11.get ⟨2, by decide⟩) = canonicalPose7_354.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_354 (box := canonicalBox7_354) (k := keys7Chunk11.get ⟨2, by decide⟩) (canonicalMatch7_354) (canonicalDecode7_354)

def canonicalPose7_355 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, false, true, true, false], ![0, 2, 0, 2, 2, 1, 0]⟩
def canonicalBox7_355 : BoxKey 7 :=
  ⟨![100800, 268800, 114240, 376320, 255360, 60480, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 114688, 376880, 254940, 60080, 134785], true⟩

theorem canonicalMatch7_355 :
    canonicalPose7_355.boxKey 188160 (referenceBox7 (!canonicalBox7_355.bump)) = canonicalBox7_355 := by decide +kernel

theorem canonicalDecode7_355 : canonicalBox7_355.toKeyData 188160 = keys7Chunk11.get ⟨3, by decide⟩ := by
  change canonicalBox7_355.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (751 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_355 : keySolid (keys7Chunk11.get ⟨3, by decide⟩) = canonicalPose7_355.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_355 (box := canonicalBox7_355) (k := keys7Chunk11.get ⟨3, by decide⟩) (canonicalMatch7_355) (canonicalDecode7_355)

def canonicalPose7_356 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, true, false, false, false], ![0, 1, 1, 2, 2, 0, 0]⟩
def canonicalBox7_356 : BoxKey 7 :=
  ⟨![100800, 322560, 60480, 255360, 376320, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 322945, 60080, 254940, 376880, 114688, 108010], true⟩

theorem canonicalMatch7_356 :
    canonicalPose7_356.boxKey 188160 (referenceBox7 (!canonicalBox7_356.bump)) = canonicalBox7_356 := by decide +kernel

theorem canonicalDecode7_356 : canonicalBox7_356.toKeyData 188160 = keys7Chunk11.get ⟨4, by decide⟩ := by
  change canonicalBox7_356.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (9227 / 5376), (751 / 2352), (607 / 448), (673 / 336), (64 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_356 : keySolid (keys7Chunk11.get ⟨4, by decide⟩) = canonicalPose7_356.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_356 (box := canonicalBox7_356) (k := keys7Chunk11.get ⟨4, by decide⟩) (canonicalMatch7_356) (canonicalDecode7_356)

def canonicalPose7_357 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, false, true, false, true, true], ![0, 2, 0, 2, 1, 0, 1]⟩
def canonicalBox7_357 : BoxKey 7 :=
  ⟨![107520, 275520, 134400, 248640, 309120, 0, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 134785, 248240, 309540, -560, 73472], true⟩

theorem canonicalMatch7_357 :
    canonicalPose7_357.boxKey 188160 (referenceBox7 (!canonicalBox7_357.bump)) = canonicalBox7_357 := by decide +kernel

theorem canonicalDecode7_357 : canonicalBox7_357.toKeyData 188160 = keys7Chunk11.get ⟨5, by decide⟩ := by
  change canonicalBox7_357.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (5 / 7), (37 / 28), (23 / 14), 0, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (-1 / 336), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_357 : keySolid (keys7Chunk11.get ⟨5, by decide⟩) = canonicalPose7_357.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_357 (box := canonicalBox7_357) (k := keys7Chunk11.get ⟨5, by decide⟩) (canonicalMatch7_357) (canonicalDecode7_357)

def canonicalPose7_358 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, false, true, false, false, true], ![0, 2, 0, 2, 1, 0, 1]⟩
def canonicalBox7_358 : BoxKey 7 :=
  ⟨![127680, 241920, 100800, 268800, 302400, 0, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 241535, 101360, 268310, 302848, 560, 66780], false⟩

theorem canonicalMatch7_358 :
    canonicalPose7_358.boxKey 188160 (referenceBox7 (!canonicalBox7_358.bump)) = canonicalBox7_358 := by decide +kernel

theorem canonicalDecode7_358 : canonicalBox7_358.toKeyData 188160 = keys7Chunk11.get ⟨6, by decide⟩ := by
  change canonicalBox7_358.toKeyData 188160 = ⟨![(19 / 28), (9 / 7), (15 / 28), (10 / 7), (45 / 28), 0, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (1 / 336), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_358 : keySolid (keys7Chunk11.get ⟨6, by decide⟩) = canonicalPose7_358.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_358 (box := canonicalBox7_358) (k := keys7Chunk11.get ⟨6, by decide⟩) (canonicalMatch7_358) (canonicalDecode7_358)

def canonicalPose7_359 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, true, true, true, false, false], ![0, 1, 1, 2, 2, 0, 0]⟩
def canonicalBox7_359 : BoxKey 7 :=
  ⟨![120960, 315840, 53760, 275520, 268800, 114240, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 53375, 274960, 268310, 114688, 560], false⟩

theorem canonicalMatch7_359 :
    canonicalPose7_359.boxKey 188160 (referenceBox7 (!canonicalBox7_359.bump)) = canonicalBox7_359 := by decide +kernel

theorem canonicalDecode7_359 : canonicalBox7_359.toKeyData 188160 = keys7Chunk11.get ⟨7, by decide⟩ := by
  change canonicalBox7_359.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (2 / 7), (41 / 28), (10 / 7), (17 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_359 : keySolid (keys7Chunk11.get ⟨7, by decide⟩) = canonicalPose7_359.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_359 (box := canonicalBox7_359) (k := keys7Chunk11.get ⟨7, by decide⟩) (canonicalMatch7_359) (canonicalDecode7_359)

def canonicalPose7_360 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, true, true, false, false], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_360 : BoxKey 7 :=
  ⟨![0, 302400, 107520, 275520, 241920, 127680, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 302848, 108010, 274960, 241535, 128080, 309540], false⟩

theorem canonicalMatch7_360 :
    canonicalPose7_360.boxKey 188160 (referenceBox7 (!canonicalBox7_360.bump)) = canonicalBox7_360 := by decide +kernel

theorem canonicalDecode7_360 : canonicalBox7_360.toKeyData 188160 = keys7Chunk11.get ⟨8, by decide⟩ := by
  change canonicalBox7_360.toKeyData 188160 = ⟨![0, (45 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_360 : keySolid (keys7Chunk11.get ⟨8, by decide⟩) = canonicalPose7_360.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_360 (box := canonicalBox7_360) (k := keys7Chunk11.get ⟨8, by decide⟩) (canonicalMatch7_360) (canonicalDecode7_360)

def canonicalPose7_361 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, true, true, false, false], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_361 : BoxKey 7 :=
  ⟨![0, 309120, 127680, 241920, 275520, 107520, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 309540, 128080, 241535, 274960, 108010, 302848], true⟩

theorem canonicalMatch7_361 :
    canonicalPose7_361.boxKey 188160 (referenceBox7 (!canonicalBox7_361.bump)) = canonicalBox7_361 := by decide +kernel

theorem canonicalDecode7_361 : canonicalBox7_361.toKeyData 188160 = keys7Chunk11.get ⟨9, by decide⟩ := by
  change canonicalBox7_361.toKeyData 188160 = ⟨![0, (23 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_361 : keySolid (keys7Chunk11.get ⟨9, by decide⟩) = canonicalPose7_361.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_361 (box := canonicalBox7_361) (k := keys7Chunk11.get ⟨9, by decide⟩) (canonicalMatch7_361) (canonicalDecode7_361)

def canonicalPose7_362 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, false, false, false, false, true], ![0, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_362 : BoxKey 7 :=
  ⟨![114240, 376320, 120960, 315840, 322560, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 376880, 121380, 316240, 322945, 101360, 268310], true⟩

theorem canonicalMatch7_362 :
    canonicalPose7_362.boxKey 188160 (referenceBox7 (!canonicalBox7_362.bump)) = canonicalBox7_362 := by decide +kernel

theorem canonicalDecode7_362 : canonicalBox7_362.toKeyData 188160 = keys7Chunk11.get ⟨10, by decide⟩ := by
  change canonicalBox7_362.toKeyData 188160 = ⟨![(17 / 28), 2, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (673 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_362 : keySolid (keys7Chunk11.get ⟨10, by decide⟩) = canonicalPose7_362.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_362 (box := canonicalBox7_362) (k := keys7Chunk11.get ⟨10, by decide⟩) (canonicalMatch7_362) (canonicalDecode7_362)

def canonicalPose7_363 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, true, true, true, false, true], ![1, 2, 0, 2, 2, 0, 2]⟩
def canonicalBox7_363 : BoxKey 7 :=
  ⟨![60480, 255360, 0, 262080, 268800, 100800, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, -560, 261632, 268310, 101360, 241535], true⟩

theorem canonicalMatch7_363 :
    canonicalPose7_363.boxKey 188160 (referenceBox7 (!canonicalBox7_363.bump)) = canonicalBox7_363 := by decide +kernel

theorem canonicalDecode7_363 : canonicalBox7_363.toKeyData 188160 = keys7Chunk11.get ⟨11, by decide⟩ := by
  change canonicalBox7_363.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (-1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_363 : keySolid (keys7Chunk11.get ⟨11, by decide⟩) = canonicalPose7_363.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_363 (box := canonicalBox7_363) (k := keys7Chunk11.get ⟨11, by decide⟩) (canonicalMatch7_363) (canonicalDecode7_363)

def canonicalPose7_364 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, false, false, true, true, false, false], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_364 : BoxKey 7 :=
  ⟨![127680, 309120, 114240, 376320, 268800, 100800, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 309540, 114688, 375760, 268310, 101360, 322945], false⟩

theorem canonicalMatch7_364 :
    canonicalPose7_364.boxKey 188160 (referenceBox7 (!canonicalBox7_364.bump)) = canonicalBox7_364 := by decide +kernel

theorem canonicalDecode7_364 : canonicalBox7_364.toKeyData 188160 = keys7Chunk11.get ⟨12, by decide⟩ := by
  change canonicalBox7_364.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (64 / 105), (671 / 336), (3833 / 2688), (181 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_364 : keySolid (keys7Chunk11.get ⟨12, by decide⟩) = canonicalPose7_364.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_364 (box := canonicalBox7_364) (k := keys7Chunk11.get ⟨12, by decide⟩) (canonicalMatch7_364) (canonicalDecode7_364)

def canonicalPose7_365 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, false, false, true, false, false, false], ![0, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_365 : BoxKey 7 :=
  ⟨![127680, 322560, 100800, 268800, 376320, 114240, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 322945, 101360, 268310, 376880, 114688, 309540], true⟩

theorem canonicalMatch7_365 :
    canonicalPose7_365.boxKey 188160 (referenceBox7 (!canonicalBox7_365.bump)) = canonicalBox7_365 := by decide +kernel

theorem canonicalDecode7_365 : canonicalBox7_365.toKeyData 188160 = keys7Chunk11.get ⟨13, by decide⟩ := by
  change canonicalBox7_365.toKeyData 188160 = ⟨![(19 / 28), (12 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (673 / 336), (64 / 105), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_365 : keySolid (keys7Chunk11.get ⟨13, by decide⟩) = canonicalPose7_365.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_365 (box := canonicalBox7_365) (k := keys7Chunk11.get ⟨13, by decide⟩) (canonicalMatch7_365) (canonicalDecode7_365)

def canonicalPose7_366 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, false, true, true, false, true], ![1, 2, 0, 2, 2, 0, 2]⟩
def canonicalBox7_366 : BoxKey 7 :=
  ⟨![60480, 241920, 100800, 268800, 262080, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 241535, 101360, 268310, 261632, 560, 254940], false⟩

theorem canonicalMatch7_366 :
    canonicalPose7_366.boxKey 188160 (referenceBox7 (!canonicalBox7_366.bump)) = canonicalBox7_366 := by decide +kernel

theorem canonicalDecode7_366 : canonicalBox7_366.toKeyData 188160 = keys7Chunk11.get ⟨14, by decide⟩ := by
  change canonicalBox7_366.toKeyData 188160 = ⟨![(9 / 28), (9 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (1 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_366 : keySolid (keys7Chunk11.get ⟨14, by decide⟩) = canonicalPose7_366.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_366 (box := canonicalBox7_366) (k := keys7Chunk11.get ⟨14, by decide⟩) (canonicalMatch7_366) (canonicalDecode7_366)

def canonicalPose7_367 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, false, false, false, true], ![0, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_367 : BoxKey 7 :=
  ⟨![114240, 268800, 100800, 322560, 315840, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 268310, 101360, 322945, 316240, 121380, 375760], false⟩

theorem canonicalMatch7_367 :
    canonicalPose7_367.boxKey 188160 (referenceBox7 (!canonicalBox7_367.bump)) = canonicalBox7_367 := by decide +kernel

theorem canonicalDecode7_367 : canonicalBox7_367.toKeyData 188160 = keys7Chunk11.get ⟨15, by decide⟩ := by
  change canonicalBox7_367.toKeyData 188160 = ⟨![(17 / 28), (10 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_367 : keySolid (keys7Chunk11.get ⟨15, by decide⟩) = canonicalPose7_367.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_367 (box := canonicalBox7_367) (k := keys7Chunk11.get ⟨15, by decide⟩) (canonicalMatch7_367) (canonicalDecode7_367)

def canonicalPose7_368 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, true, true, false, false], ![0, 2, 0, 2, 2, 1, 0]⟩
def canonicalBox7_368 : BoxKey 7 :=
  ⟨![0, 262080, 107520, 275520, 241920, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 261632, 108010, 274960, 241535, 316240, 121380], true⟩

theorem canonicalMatch7_368 :
    canonicalPose7_368.boxKey 188160 (referenceBox7 (!canonicalBox7_368.bump)) = canonicalBox7_368 := by decide +kernel

theorem canonicalDecode7_368 : canonicalBox7_368.toKeyData 188160 = keys7Chunk11.get ⟨16, by decide⟩ := by
  change canonicalBox7_368.toKeyData 188160 = ⟨![0, (39 / 28), (4 / 7), (41 / 28), (9 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_368 : keySolid (keys7Chunk11.get ⟨16, by decide⟩) = canonicalPose7_368.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_368 (box := canonicalBox7_368) (k := keys7Chunk11.get ⟨16, by decide⟩) (canonicalMatch7_368) (canonicalDecode7_368)

def canonicalPose7_369 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, true, false, true, false, true, true], ![0, 2, 0, 2, 1, 2, 1]⟩
def canonicalBox7_369 : BoxKey 7 :=
  ⟨![114240, 376320, 107520, 275520, 322560, 248640, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, 375760, 108010, 274960, 322945, 248240, 66780], false⟩

theorem canonicalMatch7_369 :
    canonicalPose7_369.boxKey 188160 (referenceBox7 (!canonicalBox7_369.bump)) = canonicalBox7_369 := by decide +kernel

theorem canonicalDecode7_369 : canonicalBox7_369.toKeyData 188160 = keys7Chunk11.get ⟨17, by decide⟩ := by
  change canonicalBox7_369.toKeyData 188160 = ⟨![(17 / 28), 2, (4 / 7), (41 / 28), (12 / 7), (37 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (671 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_369 : keySolid (keys7Chunk11.get ⟨17, by decide⟩) = canonicalPose7_369.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_369 (box := canonicalBox7_369) (k := keys7Chunk11.get ⟨17, by decide⟩) (canonicalMatch7_369) (canonicalDecode7_369)

def canonicalPose7_370 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, true, true, true, false, true, true], ![0, 2, 0, 2, 1, 2, 1]⟩
def canonicalBox7_370 : BoxKey 7 :=
  ⟨![100800, 268800, 0, 262080, 309120, 248640, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 268310, -560, 261632, 309540, 248240, 53375], true⟩

theorem canonicalMatch7_370 :
    canonicalPose7_370.boxKey 188160 (referenceBox7 (!canonicalBox7_370.bump)) = canonicalBox7_370 := by decide +kernel

theorem canonicalDecode7_370 : canonicalBox7_370.toKeyData 188160 = keys7Chunk11.get ⟨18, by decide⟩ := by
  change canonicalBox7_370.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), 0, (39 / 28), (23 / 14), (37 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (-1 / 336), (146 / 105), (737 / 448), (3103 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_370 : keySolid (keys7Chunk11.get ⟨18, by decide⟩) = canonicalPose7_370.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_370 (box := canonicalBox7_370) (k := keys7Chunk11.get ⟨18, by decide⟩) (canonicalMatch7_370) (canonicalDecode7_370)

def canonicalPose7_371 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, true, true, false, false], ![0, 2, 0, 2, 2, 1, 0]⟩
def canonicalBox7_371 : BoxKey 7 :=
  ⟨![100800, 268800, 114240, 376320, 255360, 315840, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 114688, 375760, 254940, 316240, 134785], false⟩

theorem canonicalMatch7_371 :
    canonicalPose7_371.boxKey 188160 (referenceBox7 (!canonicalBox7_371.bump)) = canonicalBox7_371 := by decide +kernel

theorem canonicalDecode7_371 : canonicalBox7_371.toKeyData 188160 = keys7Chunk11.get ⟨19, by decide⟩ := by
  change canonicalBox7_371.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (47 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (64 / 105), (671 / 336), (607 / 448), (3953 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_371 : keySolid (keys7Chunk11.get ⟨19, by decide⟩) = canonicalPose7_371.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_371 (box := canonicalBox7_371) (k := keys7Chunk11.get ⟨19, by decide⟩) (canonicalMatch7_371) (canonicalDecode7_371)

def canonicalPose7_372 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, true, true, true, false], ![0, 1, 1, 2, 2, 2, 0]⟩
def canonicalBox7_372 : BoxKey 7 :=
  ⟨![100800, 322560, 60480, 255360, 376320, 262080, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 322945, 60080, 254940, 375760, 261632, 108010], false⟩

theorem canonicalMatch7_372 :
    canonicalPose7_372.boxKey 188160 (referenceBox7 (!canonicalBox7_372.bump)) = canonicalBox7_372 := by decide +kernel

theorem canonicalDecode7_372 : canonicalBox7_372.toKeyData 188160 = keys7Chunk11.get ⟨20, by decide⟩ := by
  change canonicalBox7_372.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (9 / 28), (19 / 14), 2, (39 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (9227 / 5376), (751 / 2352), (607 / 448), (671 / 336), (146 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_372 : keySolid (keys7Chunk11.get ⟨20, by decide⟩) = canonicalPose7_372.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_372 (box := canonicalBox7_372) (k := keys7Chunk11.get ⟨20, by decide⟩) (canonicalMatch7_372) (canonicalDecode7_372)

def canonicalPose7_373 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, false, true, false, true, true], ![0, 2, 0, 2, 1, 2, 1]⟩
def canonicalBox7_373 : BoxKey 7 :=
  ⟨![107520, 275520, 134400, 248640, 309120, 376320, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 134785, 248240, 309540, 375760, 73472], false⟩

theorem canonicalMatch7_373 :
    canonicalPose7_373.boxKey 188160 (referenceBox7 (!canonicalBox7_373.bump)) = canonicalBox7_373 := by decide +kernel

theorem canonicalDecode7_373 : canonicalBox7_373.toKeyData 188160 = keys7Chunk11.get ⟨21, by decide⟩ := by
  change canonicalBox7_373.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (5 / 7), (37 / 28), (23 / 14), 2, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (671 / 336), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_373 : keySolid (keys7Chunk11.get ⟨21, by decide⟩) = canonicalPose7_373.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_373 (box := canonicalBox7_373) (k := keys7Chunk11.get ⟨21, by decide⟩) (canonicalMatch7_373) (canonicalDecode7_373)

def canonicalPose7_374 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, false, true, false, false, true], ![0, 2, 0, 2, 1, 2, 1]⟩
def canonicalBox7_374 : BoxKey 7 :=
  ⟨![127680, 241920, 100800, 268800, 302400, 376320, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 241535, 101360, 268310, 302848, 376880, 66780], true⟩

theorem canonicalMatch7_374 :
    canonicalPose7_374.boxKey 188160 (referenceBox7 (!canonicalBox7_374.bump)) = canonicalBox7_374 := by decide +kernel

theorem canonicalDecode7_374 : canonicalBox7_374.toKeyData 188160 = keys7Chunk11.get ⟨22, by decide⟩ := by
  change canonicalBox7_374.toKeyData 188160 = ⟨![(19 / 28), (9 / 7), (15 / 28), (10 / 7), (45 / 28), 2, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (673 / 336), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_374 : keySolid (keys7Chunk11.get ⟨22, by decide⟩) = canonicalPose7_374.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_374 (box := canonicalBox7_374) (k := keys7Chunk11.get ⟨22, by decide⟩) (canonicalMatch7_374) (canonicalDecode7_374)

def canonicalPose7_375 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, true, true, true, true, true], ![0, 1, 1, 2, 2, 2, 0]⟩
def canonicalBox7_375 : BoxKey 7 :=
  ⟨![120960, 315840, 53760, 275520, 268800, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 53375, 274960, 268310, 261632, -560], true⟩

theorem canonicalMatch7_375 :
    canonicalPose7_375.boxKey 188160 (referenceBox7 (!canonicalBox7_375.bump)) = canonicalBox7_375 := by decide +kernel

theorem canonicalDecode7_375 : canonicalBox7_375.toKeyData 188160 = keys7Chunk11.get ⟨23, by decide⟩ := by
  change canonicalBox7_375.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (2 / 7), (41 / 28), (10 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_375 : keySolid (keys7Chunk11.get ⟨23, by decide⟩) = canonicalPose7_375.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_375 (box := canonicalBox7_375) (k := keys7Chunk11.get ⟨23, by decide⟩) (canonicalMatch7_375) (canonicalDecode7_375)

def canonicalPose7_376 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, true, false, false, true], ![0, 2, 0, 2, 1, 1, 2]⟩
def canonicalBox7_376 : BoxKey 7 :=
  ⟨![0, 262080, 107520, 275520, 322560, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 261632, 108010, 274960, 322945, 316240, 254940], true⟩

theorem canonicalMatch7_376 :
    canonicalPose7_376.boxKey 188160 (referenceBox7 (!canonicalBox7_376.bump)) = canonicalBox7_376 := by decide +kernel

theorem canonicalDecode7_376 : canonicalBox7_376.toKeyData 188160 = keys7Chunk11.get ⟨24, by decide⟩ := by
  change canonicalBox7_376.toKeyData 188160 = ⟨![0, (39 / 28), (4 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_376 : keySolid (keys7Chunk11.get ⟨24, by decide⟩) = canonicalPose7_376.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_376 (box := canonicalBox7_376) (k := keys7Chunk11.get ⟨24, by decide⟩) (canonicalMatch7_376) (canonicalDecode7_376)

def canonicalPose7_377 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, true, true, true, true], ![1, 2, 1, 2, 2, 2, 2]⟩
def canonicalBox7_377 : BoxKey 7 :=
  ⟨![73920, 376320, 67200, 248640, 241920, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, 375760, 66780, 248240, 241535, 274960, 268310], false⟩

theorem canonicalMatch7_377 :
    canonicalPose7_377.boxKey 188160 (referenceBox7 (!canonicalBox7_377.bump)) = canonicalBox7_377 := by decide +kernel

theorem canonicalDecode7_377 : canonicalBox7_377.toKeyData 188160 = keys7Chunk11.get ⟨25, by decide⟩ := by
  change canonicalBox7_377.toKeyData 188160 = ⟨![(11 / 28), 2, (5 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (671 / 336), (159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_377 : keySolid (keys7Chunk11.get ⟨25, by decide⟩) = canonicalPose7_377.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_377 (box := canonicalBox7_377) (k := keys7Chunk11.get ⟨25, by decide⟩) (canonicalMatch7_377) (canonicalDecode7_377)

def canonicalPose7_378 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, true, true, true, true], ![1, 2, 1, 2, 2, 2, 2]⟩
def canonicalBox7_378 : BoxKey 7 :=
  ⟨![67200, 376320, 73920, 268800, 275520, 241920, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 376880, 73472, 268310, 274960, 241535, 248240], true⟩

theorem canonicalMatch7_378 :
    canonicalPose7_378.boxKey 188160 (referenceBox7 (!canonicalBox7_378.bump)) = canonicalBox7_378 := by decide +kernel

theorem canonicalDecode7_378 : canonicalBox7_378.toKeyData 188160 = keys7Chunk11.get ⟨26, by decide⟩ := by
  change canonicalBox7_378.toKeyData 188160 = ⟨![(5 / 14), 2, (11 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (673 / 336), (41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_378 : keySolid (keys7Chunk11.get ⟨26, by decide⟩) = canonicalPose7_378.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_378 (box := canonicalBox7_378) (k := keys7Chunk11.get ⟨26, by decide⟩) (canonicalMatch7_378) (canonicalDecode7_378)

def canonicalPose7_379 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, true, false, false, true], ![0, 2, 0, 2, 1, 1, 2]⟩
def canonicalBox7_379 : BoxKey 7 :=
  ⟨![107520, 262080, 0, 255360, 315840, 322560, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 261632, 560, 254940, 316240, 322945, 274960], false⟩

theorem canonicalMatch7_379 :
    canonicalPose7_379.boxKey 188160 (referenceBox7 (!canonicalBox7_379.bump)) = canonicalBox7_379 := by decide +kernel

theorem canonicalDecode7_379 : canonicalBox7_379.toKeyData 188160 = keys7Chunk11.get ⟨27, by decide⟩ := by
  change canonicalBox7_379.toKeyData 188160 = ⟨![(4 / 7), (39 / 28), 0, (19 / 14), (47 / 28), (12 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (146 / 105), (1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_379 : keySolid (keys7Chunk11.get ⟨27, by decide⟩) = canonicalPose7_379.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_379 (box := canonicalBox7_379) (k := keys7Chunk11.get ⟨27, by decide⟩) (canonicalMatch7_379) (canonicalDecode7_379)

def canonicalPose7_380 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, true, true, true, true], ![0, 1, 0, 2, 2, 2, 2]⟩
def canonicalBox7_380 : BoxKey 7 :=
  ⟨![134400, 315840, 120960, 376320, 262080, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 316240, 121380, 375760, 261632, 268310, 274960], false⟩

theorem canonicalMatch7_380 :
    canonicalPose7_380.boxKey 188160 (referenceBox7 (!canonicalBox7_380.bump)) = canonicalBox7_380 := by decide +kernel

theorem canonicalDecode7_380 : canonicalBox7_380.toKeyData 188160 = keys7Chunk11.get ⟨28, by decide⟩ := by
  change canonicalBox7_380.toKeyData 188160 = ⟨![(5 / 7), (47 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (146 / 105), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_380 : keySolid (keys7Chunk11.get ⟨28, by decide⟩) = canonicalPose7_380.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_380 (box := canonicalBox7_380) (k := keys7Chunk11.get ⟨28, by decide⟩) (canonicalMatch7_380) (canonicalDecode7_380)

def canonicalPose7_381 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, true, true, true, false, true, true], ![1, 2, 1, 2, 2, 2, 2]⟩
def canonicalBox7_381 : BoxKey 7 :=
  ⟨![53760, 248640, 67200, 262080, 376320, 268800, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 248240, 66780, 261632, 376880, 268310, 274960], true⟩

theorem canonicalMatch7_381 :
    canonicalPose7_381.boxKey 188160 (referenceBox7 (!canonicalBox7_381.bump)) = canonicalBox7_381 := by decide +kernel

theorem canonicalDecode7_381 : canonicalBox7_381.toKeyData 188160 = keys7Chunk11.get ⟨29, by decide⟩ := by
  change canonicalBox7_381.toKeyData 188160 = ⟨![(2 / 7), (37 / 28), (5 / 14), (39 / 28), 2, (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105), (673 / 336), (3833 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_381 : keySolid (keys7Chunk11.get ⟨29, by decide⟩) = canonicalPose7_381.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_381 (box := canonicalBox7_381) (k := keys7Chunk11.get ⟨29, by decide⟩) (canonicalMatch7_381) (canonicalDecode7_381)

def canonicalPose7_382 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, true, true, true, true, true, true], ![1, 2, 1, 2, 2, 2, 2]⟩
def canonicalBox7_382 : BoxKey 7 :=
  ⟨![67200, 248640, 53760, 275520, 268800, 376320, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 248240, 53375, 274960, 268310, 375760, 261632], false⟩

theorem canonicalMatch7_382 :
    canonicalPose7_382.boxKey 188160 (referenceBox7 (!canonicalBox7_382.bump)) = canonicalBox7_382 := by decide +kernel

theorem canonicalDecode7_382 : canonicalBox7_382.toKeyData 188160 = keys7Chunk11.get ⟨30, by decide⟩ := by
  change canonicalBox7_382.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (2 / 7), (41 / 28), (10 / 7), 2, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (671 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_382 : keySolid (keys7Chunk11.get ⟨30, by decide⟩) = canonicalPose7_382.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_382 (box := canonicalBox7_382) (k := keys7Chunk11.get ⟨30, by decide⟩) (canonicalMatch7_382) (canonicalDecode7_382)

def canonicalPose7_383 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, true, true, true, false], ![0, 1, 0, 2, 2, 2, 2]⟩
def canonicalBox7_383 : BoxKey 7 :=
  ⟨![120960, 315840, 134400, 275520, 268800, 262080, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 134785, 274960, 268310, 261632, 376880], true⟩

theorem canonicalMatch7_383 :
    canonicalPose7_383.boxKey 188160 (referenceBox7 (!canonicalBox7_383.bump)) = canonicalBox7_383 := by decide +kernel

theorem canonicalDecode7_383 : canonicalBox7_383.toKeyData 188160 = keys7Chunk11.get ⟨31, by decide⟩ := by
  change canonicalBox7_383.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (5 / 7), (41 / 28), (10 / 7), (39 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_383 : keySolid (keys7Chunk11.get ⟨31, by decide⟩) = canonicalPose7_383.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_383 (box := canonicalBox7_383) (k := keys7Chunk11.get ⟨31, by decide⟩) (canonicalMatch7_383) (canonicalDecode7_383)

theorem keys7Chunk11_canonical : ∀ k ∈ keys7Chunk11,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk11, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_352, canonicalSolid7_352⟩
  · exact ⟨canonicalPose7_353, canonicalSolid7_353⟩
  · exact ⟨canonicalPose7_354, canonicalSolid7_354⟩
  · exact ⟨canonicalPose7_355, canonicalSolid7_355⟩
  · exact ⟨canonicalPose7_356, canonicalSolid7_356⟩
  · exact ⟨canonicalPose7_357, canonicalSolid7_357⟩
  · exact ⟨canonicalPose7_358, canonicalSolid7_358⟩
  · exact ⟨canonicalPose7_359, canonicalSolid7_359⟩
  · exact ⟨canonicalPose7_360, canonicalSolid7_360⟩
  · exact ⟨canonicalPose7_361, canonicalSolid7_361⟩
  · exact ⟨canonicalPose7_362, canonicalSolid7_362⟩
  · exact ⟨canonicalPose7_363, canonicalSolid7_363⟩
  · exact ⟨canonicalPose7_364, canonicalSolid7_364⟩
  · exact ⟨canonicalPose7_365, canonicalSolid7_365⟩
  · exact ⟨canonicalPose7_366, canonicalSolid7_366⟩
  · exact ⟨canonicalPose7_367, canonicalSolid7_367⟩
  · exact ⟨canonicalPose7_368, canonicalSolid7_368⟩
  · exact ⟨canonicalPose7_369, canonicalSolid7_369⟩
  · exact ⟨canonicalPose7_370, canonicalSolid7_370⟩
  · exact ⟨canonicalPose7_371, canonicalSolid7_371⟩
  · exact ⟨canonicalPose7_372, canonicalSolid7_372⟩
  · exact ⟨canonicalPose7_373, canonicalSolid7_373⟩
  · exact ⟨canonicalPose7_374, canonicalSolid7_374⟩
  · exact ⟨canonicalPose7_375, canonicalSolid7_375⟩
  · exact ⟨canonicalPose7_376, canonicalSolid7_376⟩
  · exact ⟨canonicalPose7_377, canonicalSolid7_377⟩
  · exact ⟨canonicalPose7_378, canonicalSolid7_378⟩
  · exact ⟨canonicalPose7_379, canonicalSolid7_379⟩
  · exact ⟨canonicalPose7_380, canonicalSolid7_380⟩
  · exact ⟨canonicalPose7_381, canonicalSolid7_381⟩
  · exact ⟨canonicalPose7_382, canonicalSolid7_382⟩
  · exact ⟨canonicalPose7_383, canonicalSolid7_383⟩

#print axioms keys7Chunk11_canonical

end SparseMonotiles.Canonical
