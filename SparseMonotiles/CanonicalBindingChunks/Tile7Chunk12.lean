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

def canonicalPose7_384 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, true, false, false, true, false], ![0, 2, 2, 0, 0, 1, 0]⟩
def canonicalBox7_384 : BoxKey 7 :=
  ⟨![0, 262080, 268800, 100800, 134400, 60480, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 261632, 268310, 101360, 134785, 60080, 121380], true⟩

theorem canonicalMatch7_384 :
    canonicalPose7_384.boxKey 188160 (referenceBox7 (!canonicalBox7_384.bump)) = canonicalBox7_384 := by decide +kernel

theorem canonicalDecode7_384 : canonicalBox7_384.toKeyData 188160 = keys7Chunk12.get ⟨0, by decide⟩ := by
  change canonicalBox7_384.toKeyData 188160 = ⟨![0, (39 / 28), (10 / 7), (15 / 28), (5 / 7), (9 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_384 : keySolid (keys7Chunk12.get ⟨0, by decide⟩) = canonicalPose7_384.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_384 (box := canonicalBox7_384) (k := keys7Chunk12.get ⟨0, by decide⟩) (canonicalMatch7_384) (canonicalDecode7_384)

def canonicalPose7_385 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, true, true, false, true, false, true], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_385 : BoxKey 7 :=
  ⟨![114240, 376320, 268800, 100800, 53760, 127680, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, 375760, 268310, 101360, 53375, 128080, 66780], false⟩

theorem canonicalMatch7_385 :
    canonicalPose7_385.boxKey 188160 (referenceBox7 (!canonicalBox7_385.bump)) = canonicalBox7_385 := by decide +kernel

theorem canonicalDecode7_385 : canonicalBox7_385.toKeyData 188160 = keys7Chunk12.get ⟨1, by decide⟩ := by
  change canonicalBox7_385.toKeyData 188160 = ⟨![(17 / 28), 2, (10 / 7), (15 / 28), (2 / 7), (19 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (671 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_385 : keySolid (keys7Chunk12.get ⟨1, by decide⟩) = canonicalPose7_385.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_385 (box := canonicalBox7_385) (k := keys7Chunk12.get ⟨1, by decide⟩) (canonicalMatch7_385) (canonicalDecode7_385)

def canonicalPose7_386 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, true, false, false, true, false, true], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_386 : BoxKey 7 :=
  ⟨![100800, 268800, 376320, 114240, 67200, 127680, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 268310, 376880, 114688, 66780, 128080, 53375], true⟩

theorem canonicalMatch7_386 :
    canonicalPose7_386.boxKey 188160 (referenceBox7 (!canonicalBox7_386.bump)) = canonicalBox7_386 := by decide +kernel

theorem canonicalDecode7_386 : canonicalBox7_386.toKeyData 188160 = keys7Chunk12.get ⟨2, by decide⟩ := by
  change canonicalBox7_386.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), 2, (17 / 28), (5 / 14), (19 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (673 / 336), (64 / 105), (159 / 448), (1601 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_386 : keySolid (keys7Chunk12.get ⟨2, by decide⟩) = canonicalPose7_386.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_386 (box := canonicalBox7_386) (k := keys7Chunk12.get ⟨2, by decide⟩) (canonicalMatch7_386) (canonicalDecode7_386)

def canonicalPose7_387 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, false, false, true, false], ![0, 2, 2, 0, 0, 1, 0]⟩
def canonicalBox7_387 : BoxKey 7 :=
  ⟨![100800, 268800, 262080, 0, 120960, 60480, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 261632, 560, 121380, 60080, 134785], false⟩

theorem canonicalMatch7_387 :
    canonicalPose7_387.boxKey 188160 (referenceBox7 (!canonicalBox7_387.bump)) = canonicalBox7_387 := by decide +kernel

theorem canonicalDecode7_387 : canonicalBox7_387.toKeyData 188160 = keys7Chunk12.get ⟨3, by decide⟩ := by
  change canonicalBox7_387.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (39 / 28), 0, (9 / 14), (9 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (146 / 105), (1 / 336), (289 / 448), (751 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_387 : keySolid (keys7Chunk12.get ⟨3, by decide⟩) = canonicalPose7_387.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_387 (box := canonicalBox7_387) (k := keys7Chunk12.get ⟨3, by decide⟩) (canonicalMatch7_387) (canonicalDecode7_387)

def canonicalPose7_388 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, false, false, false], ![0, 1, 1, 0, 0, 0, 0]⟩
def canonicalBox7_388 : BoxKey 7 :=
  ⟨![100800, 322560, 315840, 120960, 0, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 322945, 316240, 121380, 560, 114688, 108010], false⟩

theorem canonicalMatch7_388 :
    canonicalPose7_388.boxKey 188160 (referenceBox7 (!canonicalBox7_388.bump)) = canonicalBox7_388 := by decide +kernel

theorem canonicalDecode7_388 : canonicalBox7_388.toKeyData 188160 = keys7Chunk12.get ⟨4, by decide⟩ := by
  change canonicalBox7_388.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (47 / 28), (9 / 14), 0, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (64 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_388 : keySolid (keys7Chunk12.get ⟨4, by decide⟩) = canonicalPose7_388.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_388 (box := canonicalBox7_388) (k := keys7Chunk12.get ⟨4, by decide⟩) (canonicalMatch7_388) (canonicalDecode7_388)

def canonicalPose7_389 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, false, true, false, true], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_389 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 127680, 67200, 0, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 128080, 66780, 560, 73472], false⟩

theorem canonicalMatch7_389 :
    canonicalPose7_389.boxKey 188160 (referenceBox7 (!canonicalBox7_389.bump)) = canonicalBox7_389 := by decide +kernel

theorem canonicalDecode7_389 : canonicalBox7_389.toKeyData 188160 = keys7Chunk12.get ⟨5, by decide⟩ := by
  change canonicalBox7_389.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (19 / 28), (5 / 14), 0, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (1 / 336), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_389 : keySolid (keys7Chunk12.get ⟨5, by decide⟩) = canonicalPose7_389.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_389 (box := canonicalBox7_389) (k := keys7Chunk12.get ⟨5, by decide⟩) (canonicalMatch7_389) (canonicalDecode7_389)

def canonicalPose7_390 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, false, true, true, true], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_390 : BoxKey 7 :=
  ⟨![127680, 241920, 275520, 107520, 73920, 0, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 241535, 274960, 108010, 73472, -560, 66780], true⟩

theorem canonicalMatch7_390 :
    canonicalPose7_390.boxKey 188160 (referenceBox7 (!canonicalBox7_390.bump)) = canonicalBox7_390 := by decide +kernel

theorem canonicalDecode7_390 : canonicalBox7_390.toKeyData 188160 = keys7Chunk12.get ⟨6, by decide⟩ := by
  change canonicalBox7_390.toKeyData 188160 = ⟨![(19 / 28), (9 / 7), (41 / 28), (4 / 7), (11 / 28), 0, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (-1 / 336), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_390 : keySolid (keys7Chunk12.get ⟨6, by decide⟩) = canonicalPose7_390.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_390 (box := canonicalBox7_390) (k := keys7Chunk12.get ⟨6, by decide⟩) (canonicalMatch7_390) (canonicalDecode7_390)

def canonicalPose7_391 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, false, false, true], ![0, 1, 1, 0, 0, 0, 0]⟩
def canonicalBox7_391 : BoxKey 7 :=
  ⟨![120960, 315840, 322560, 100800, 107520, 114240, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 322945, 101360, 108010, 114688, -560], true⟩

theorem canonicalMatch7_391 :
    canonicalPose7_391.boxKey 188160 (referenceBox7 (!canonicalBox7_391.bump)) = canonicalBox7_391 := by decide +kernel

theorem canonicalDecode7_391 : canonicalBox7_391.toKeyData 188160 = keys7Chunk12.get ⟨7, by decide⟩ := by
  change canonicalBox7_391.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (12 / 7), (15 / 28), (4 / 7), (17 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_391 : keySolid (keys7Chunk12.get ⟨7, by decide⟩) = canonicalPose7_391.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_391 (box := canonicalBox7_391) (k := keys7Chunk12.get ⟨7, by decide⟩) (canonicalMatch7_391) (canonicalDecode7_391)

def canonicalPose7_392 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, true, false, false, true, false, true], ![0, 2, 1, 0, 1, 0, 2]⟩
def canonicalBox7_392 : BoxKey 7 :=
  ⟨![0, 262080, 309120, 127680, 53760, 100800, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![560, 261632, 309540, 128080, 53375, 101360, 268310], false⟩

theorem canonicalMatch7_392 :
    canonicalPose7_392.boxKey 188160 (referenceBox7 (!canonicalBox7_392.bump)) = canonicalBox7_392 := by decide +kernel

theorem canonicalDecode7_392 : canonicalBox7_392.toKeyData 188160 = keys7Chunk12.get ⟨8, by decide⟩ := by
  change canonicalBox7_392.toKeyData 188160 = ⟨![0, (39 / 28), (23 / 14), (19 / 28), (2 / 7), (15 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(1 / 336), (146 / 105), (737 / 448), (1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_392 : keySolid (keys7Chunk12.get ⟨8, by decide⟩) = canonicalPose7_392.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_392 (box := canonicalBox7_392) (k := keys7Chunk12.get ⟨8, by decide⟩) (canonicalMatch7_392) (canonicalDecode7_392)

def canonicalPose7_393 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, true, true, false, false, true], ![0, 2, 2, 1, 0, 0, 2]⟩
def canonicalBox7_393 : BoxKey 7 :=
  ⟨![114240, 376320, 255360, 60480, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 376880, 254940, 60080, 134785, 101360, 268310], true⟩

theorem canonicalMatch7_393 :
    canonicalPose7_393.boxKey 188160 (referenceBox7 (!canonicalBox7_393.bump)) = canonicalBox7_393 := by decide +kernel

theorem canonicalDecode7_393 : canonicalBox7_393.toKeyData 188160 = keys7Chunk12.get ⟨9, by decide⟩ := by
  change canonicalBox7_393.toKeyData 188160 = ⟨![(17 / 28), 2, (19 / 14), (9 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (673 / 336), (607 / 448), (751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_393 : keySolid (keys7Chunk12.get ⟨9, by decide⟩) = canonicalPose7_393.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_393 (box := canonicalBox7_393) (k := keys7Chunk12.get ⟨9, by decide⟩) (canonicalMatch7_393) (canonicalDecode7_393)

def canonicalPose7_394 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, false, false, false, false], ![1, 2, 2, 0, 0, 0, 1]⟩
def canonicalBox7_394 : BoxKey 7 :=
  ⟨![60480, 255360, 376320, 114240, 107520, 100800, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 376880, 114688, 108010, 101360, 322945], true⟩

theorem canonicalMatch7_394 :
    canonicalPose7_394.boxKey 188160 (referenceBox7 (!canonicalBox7_394.bump)) = canonicalBox7_394 := by decide +kernel

theorem canonicalDecode7_394 : canonicalBox7_394.toKeyData 188160 = keys7Chunk12.get ⟨10, by decide⟩ := by
  change canonicalBox7_394.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 2, (17 / 28), (4 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (673 / 336), (64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_394 : keySolid (keys7Chunk12.get ⟨10, by decide⟩) = canonicalPose7_394.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_394 (box := canonicalBox7_394) (k := keys7Chunk12.get ⟨10, by decide⟩) (canonicalMatch7_394) (canonicalDecode7_394)

def canonicalPose7_395 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, false, true, false, true], ![0, 2, 1, 0, 1, 0, 2]⟩
def canonicalBox7_395 : BoxKey 7 :=
  ⟨![100800, 268800, 302400, 0, 67200, 127680, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 302848, 560, 66780, 128080, 241535], false⟩

theorem canonicalMatch7_395 :
    canonicalPose7_395.boxKey 188160 (referenceBox7 (!canonicalBox7_395.bump)) = canonicalBox7_395 := by decide +kernel

theorem canonicalDecode7_395 : canonicalBox7_395.toKeyData 188160 = keys7Chunk12.get ⟨11, by decide⟩ := by
  change canonicalBox7_395.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (45 / 28), 0, (5 / 14), (19 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (169 / 105), (1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_395 : keySolid (keys7Chunk12.get ⟨11, by decide⟩) = canonicalPose7_395.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_395 (box := canonicalBox7_395) (k := keys7Chunk12.get ⟨11, by decide⟩) (canonicalMatch7_395) (canonicalDecode7_395)

def canonicalPose7_396 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, false, true, true, false, true], ![0, 2, 1, 0, 1, 0, 2]⟩
def canonicalBox7_396 : BoxKey 7 :=
  ⟨![134400, 248640, 309120, 0, 73920, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 248240, 309540, -560, 73472, 108010, 274960], true⟩

theorem canonicalMatch7_396 :
    canonicalPose7_396.boxKey 188160 (referenceBox7 (!canonicalBox7_396.bump)) = canonicalBox7_396 := by decide +kernel

theorem canonicalDecode7_396 : canonicalBox7_396.toKeyData 188160 = keys7Chunk12.get ⟨12, by decide⟩ := by
  change canonicalBox7_396.toKeyData 188160 = ⟨![(5 / 7), (37 / 28), (23 / 14), 0, (11 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3103 / 2352), (737 / 448), (-1 / 336), (41 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_396 : keySolid (keys7Chunk12.get ⟨12, by decide⟩) = canonicalPose7_396.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_396 (box := canonicalBox7_396) (k := keys7Chunk12.get ⟨12, by decide⟩) (canonicalMatch7_396) (canonicalDecode7_396)

def canonicalPose7_397 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, false, false, false, false], ![1, 2, 2, 0, 0, 0, 1]⟩
def canonicalBox7_397 : BoxKey 7 :=
  ⟨![53760, 275520, 268800, 114240, 0, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 274960, 268310, 114688, 560, 121380, 316240], false⟩

theorem canonicalMatch7_397 :
    canonicalPose7_397.boxKey 188160 (referenceBox7 (!canonicalBox7_397.bump)) = canonicalBox7_397 := by decide +kernel

theorem canonicalDecode7_397 : canonicalBox7_397.toKeyData 188160 = keys7Chunk12.get ⟨13, by decide⟩ := by
  change canonicalBox7_397.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (10 / 7), (17 / 28), 0, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (1 / 336), (289 / 448), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_397 : keySolid (keys7Chunk12.get ⟨13, by decide⟩) = canonicalPose7_397.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_397 (box := canonicalBox7_397) (k := keys7Chunk12.get ⟨13, by decide⟩) (canonicalMatch7_397) (canonicalDecode7_397)

def canonicalPose7_398 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, true, false, false, true], ![0, 2, 2, 1, 0, 0, 2]⟩
def canonicalBox7_398 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 60480, 120960, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 60080, 121380, 560, 261632], false⟩

theorem canonicalMatch7_398 :
    canonicalPose7_398.boxKey 188160 (referenceBox7 (!canonicalBox7_398.bump)) = canonicalBox7_398 := by decide +kernel

theorem canonicalDecode7_398 : canonicalBox7_398.toKeyData 188160 = keys7Chunk12.get ⟨14, by decide⟩ := by
  change canonicalBox7_398.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (9 / 28), (9 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (289 / 448), (1 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_398 : keySolid (keys7Chunk12.get ⟨14, by decide⟩) = canonicalPose7_398.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_398 (box := canonicalBox7_398) (k := keys7Chunk12.get ⟨14, by decide⟩) (canonicalMatch7_398) (canonicalDecode7_398)

def canonicalPose7_399 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, true, false, false, true, false, false], ![0, 2, 1, 0, 1, 0, 2]⟩
def canonicalBox7_399 : BoxKey 7 :=
  ⟨![107520, 275520, 322560, 127680, 67200, 114240, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 274960, 322945, 128080, 66780, 114688, 376880], true⟩

theorem canonicalMatch7_399 :
    canonicalPose7_399.boxKey 188160 (referenceBox7 (!canonicalBox7_399.bump)) = canonicalBox7_399 := by decide +kernel

theorem canonicalDecode7_399 : canonicalBox7_399.toKeyData 188160 = keys7Chunk12.get ⟨15, by decide⟩ := by
  change canonicalBox7_399.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (12 / 7), (19 / 28), (5 / 14), (17 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (159 / 448), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_399 : keySolid (keys7Chunk12.get ⟨15, by decide⟩) = canonicalPose7_399.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_399 (box := canonicalBox7_399) (k := keys7Chunk12.get ⟨15, by decide⟩) (canonicalMatch7_399) (canonicalDecode7_399)

def canonicalPose7_400 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, false, false, false, false], ![0, 2, 2, 0, 0, 1, 0]⟩
def canonicalBox7_400 : BoxKey 7 :=
  ⟨![0, 262080, 268800, 100800, 134400, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 261632, 268310, 101360, 134785, 316240, 121380], false⟩

theorem canonicalMatch7_400 :
    canonicalPose7_400.boxKey 188160 (referenceBox7 (!canonicalBox7_400.bump)) = canonicalBox7_400 := by decide +kernel

theorem canonicalDecode7_400 : canonicalBox7_400.toKeyData 188160 = keys7Chunk12.get ⟨16, by decide⟩ := by
  change canonicalBox7_400.toKeyData 188160 = ⟨![0, (39 / 28), (10 / 7), (15 / 28), (5 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_400 : keySolid (keys7Chunk12.get ⟨16, by decide⟩) = canonicalPose7_400.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_400 (box := canonicalBox7_400) (k := keys7Chunk12.get ⟨16, by decide⟩) (canonicalMatch7_400) (canonicalDecode7_400)

def canonicalPose7_401 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, false, true, false, true, true, true], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_401 : BoxKey 7 :=
  ⟨![114240, 376320, 268800, 100800, 53760, 248640, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, 376880, 268310, 101360, 53375, 248240, 66780], true⟩

theorem canonicalMatch7_401 :
    canonicalPose7_401.boxKey 188160 (referenceBox7 (!canonicalBox7_401.bump)) = canonicalBox7_401 := by decide +kernel

theorem canonicalDecode7_401 : canonicalBox7_401.toKeyData 188160 = keys7Chunk12.get ⟨17, by decide⟩ := by
  change canonicalBox7_401.toKeyData 188160 = ⟨![(17 / 28), 2, (10 / 7), (15 / 28), (2 / 7), (37 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (673 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_401 : keySolid (keys7Chunk12.get ⟨17, by decide⟩) = canonicalPose7_401.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_401 (box := canonicalBox7_401) (k := keys7Chunk12.get ⟨17, by decide⟩) (canonicalMatch7_401) (canonicalDecode7_401)

def canonicalPose7_402 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, true, true, false, true, true, true], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_402 : BoxKey 7 :=
  ⟨![100800, 268800, 376320, 114240, 67200, 248640, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 268310, 375760, 114688, 66780, 248240, 53375], false⟩

theorem canonicalMatch7_402 :
    canonicalPose7_402.boxKey 188160 (referenceBox7 (!canonicalBox7_402.bump)) = canonicalBox7_402 := by decide +kernel

theorem canonicalDecode7_402 : canonicalBox7_402.toKeyData 188160 = keys7Chunk12.get ⟨18, by decide⟩ := by
  change canonicalBox7_402.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), 2, (17 / 28), (5 / 14), (37 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (671 / 336), (64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_402 : keySolid (keys7Chunk12.get ⟨18, by decide⟩) = canonicalPose7_402.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_402 (box := canonicalBox7_402) (k := keys7Chunk12.get ⟨18, by decide⟩) (canonicalMatch7_402) (canonicalDecode7_402)

def canonicalPose7_403 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, true, false, false, false], ![0, 2, 2, 0, 0, 1, 0]⟩
def canonicalBox7_403 : BoxKey 7 :=
  ⟨![100800, 268800, 262080, 0, 120960, 315840, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 261632, -560, 121380, 316240, 134785], true⟩

theorem canonicalMatch7_403 :
    canonicalPose7_403.boxKey 188160 (referenceBox7 (!canonicalBox7_403.bump)) = canonicalBox7_403 := by decide +kernel

theorem canonicalDecode7_403 : canonicalBox7_403.toKeyData 188160 = keys7Chunk12.get ⟨19, by decide⟩ := by
  change canonicalBox7_403.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_403 : keySolid (keys7Chunk12.get ⟨19, by decide⟩) = canonicalPose7_403.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_403 (box := canonicalBox7_403) (k := keys7Chunk12.get ⟨19, by decide⟩) (canonicalMatch7_403) (canonicalDecode7_403)

def canonicalPose7_404 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, true, true, false], ![0, 1, 1, 0, 0, 2, 0]⟩
def canonicalBox7_404 : BoxKey 7 :=
  ⟨![100800, 322560, 315840, 120960, 0, 262080, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 322945, 316240, 121380, -560, 261632, 108010], true⟩

theorem canonicalMatch7_404 :
    canonicalPose7_404.boxKey 188160 (referenceBox7 (!canonicalBox7_404.bump)) = canonicalBox7_404 := by decide +kernel

theorem canonicalDecode7_404 : canonicalBox7_404.toKeyData 188160 = keys7Chunk12.get ⟨20, by decide⟩ := by
  change canonicalBox7_404.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_404 : keySolid (keys7Chunk12.get ⟨20, by decide⟩) = canonicalPose7_404.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_404 (box := canonicalBox7_404) (k := keys7Chunk12.get ⟨20, by decide⟩) (canonicalMatch7_404) (canonicalDecode7_404)

def canonicalPose7_405 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, false, true, false, true], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_405 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 127680, 67200, 376320, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 128080, 66780, 376880, 73472], true⟩

theorem canonicalMatch7_405 :
    canonicalPose7_405.boxKey 188160 (referenceBox7 (!canonicalBox7_405.bump)) = canonicalBox7_405 := by decide +kernel

theorem canonicalDecode7_405 : canonicalBox7_405.toKeyData 188160 = keys7Chunk12.get ⟨21, by decide⟩ := by
  change canonicalBox7_405.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (19 / 28), (5 / 14), 2, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (673 / 336), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_405 : keySolid (keys7Chunk12.get ⟨21, by decide⟩) = canonicalPose7_405.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_405 (box := canonicalBox7_405) (k := keys7Chunk12.get ⟨21, by decide⟩) (canonicalMatch7_405) (canonicalDecode7_405)

def canonicalPose7_406 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, false, true, true, true], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_406 : BoxKey 7 :=
  ⟨![127680, 241920, 275520, 107520, 73920, 376320, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 241535, 274960, 108010, 73472, 375760, 66780], false⟩

theorem canonicalMatch7_406 :
    canonicalPose7_406.boxKey 188160 (referenceBox7 (!canonicalBox7_406.bump)) = canonicalBox7_406 := by decide +kernel

theorem canonicalDecode7_406 : canonicalBox7_406.toKeyData 188160 = keys7Chunk12.get ⟨22, by decide⟩ := by
  change canonicalBox7_406.toKeyData 188160 = ⟨![(19 / 28), (9 / 7), (41 / 28), (4 / 7), (11 / 28), 2, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (671 / 336), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_406 : keySolid (keys7Chunk12.get ⟨22, by decide⟩) = canonicalPose7_406.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_406 (box := canonicalBox7_406) (k := keys7Chunk12.get ⟨22, by decide⟩) (canonicalMatch7_406) (canonicalDecode7_406)

def canonicalPose7_407 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, false, true, false], ![0, 1, 1, 0, 0, 2, 0]⟩
def canonicalBox7_407 : BoxKey 7 :=
  ⟨![120960, 315840, 322560, 100800, 107520, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 322945, 101360, 108010, 261632, 560], false⟩

theorem canonicalMatch7_407 :
    canonicalPose7_407.boxKey 188160 (referenceBox7 (!canonicalBox7_407.bump)) = canonicalBox7_407 := by decide +kernel

theorem canonicalDecode7_407 : canonicalBox7_407.toKeyData 188160 = keys7Chunk12.get ⟨23, by decide⟩ := by
  change canonicalBox7_407.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (12 / 7), (15 / 28), (4 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_407 : keySolid (keys7Chunk12.get ⟨23, by decide⟩) = canonicalPose7_407.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_407 (box := canonicalBox7_407) (k := keys7Chunk12.get ⟨23, by decide⟩) (canonicalMatch7_407) (canonicalDecode7_407)

def canonicalPose7_408 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, true, false, false, true, false], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_408 : BoxKey 7 :=
  ⟨![0, 302400, 268800, 100800, 134400, 248640, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 302848, 268310, 101360, 134785, 248240, 309540], false⟩

theorem canonicalMatch7_408 :
    canonicalPose7_408.boxKey 188160 (referenceBox7 (!canonicalBox7_408.bump)) = canonicalBox7_408 := by decide +kernel

theorem canonicalDecode7_408 : canonicalBox7_408.toKeyData 188160 = keys7Chunk12.get ⟨24, by decide⟩ := by
  change canonicalBox7_408.toKeyData 188160 = ⟨![0, (45 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_408 : keySolid (keys7Chunk12.get ⟨24, by decide⟩) = canonicalPose7_408.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_408 (box := canonicalBox7_408) (k := keys7Chunk12.get ⟨24, by decide⟩) (canonicalMatch7_408) (canonicalDecode7_408)

def canonicalPose7_409 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, true, false, false, true, false], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_409 : BoxKey 7 :=
  ⟨![0, 309120, 248640, 134400, 100800, 268800, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 309540, 248240, 134785, 101360, 268310, 302848], true⟩

theorem canonicalMatch7_409 :
    canonicalPose7_409.boxKey 188160 (referenceBox7 (!canonicalBox7_409.bump)) = canonicalBox7_409 := by decide +kernel

theorem canonicalDecode7_409 : canonicalBox7_409.toKeyData 188160 = keys7Chunk12.get ⟨25, by decide⟩ := by
  change canonicalBox7_409.toKeyData 188160 = ⟨![0, (23 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_409 : keySolid (keys7Chunk12.get ⟨25, by decide⟩) = canonicalPose7_409.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_409 (box := canonicalBox7_409) (k := keys7Chunk12.get ⟨25, by decide⟩) (canonicalMatch7_409) (canonicalDecode7_409)

def canonicalPose7_410 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, true, true, true, true, true], ![0, 2, 2, 1, 1, 2, 2]⟩
def canonicalBox7_410 : BoxKey 7 :=
  ⟨![114240, 376320, 255360, 60480, 53760, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 376880, 254940, 60080, 53375, 274960, 268310], true⟩

theorem canonicalMatch7_410 :
    canonicalPose7_410.boxKey 188160 (referenceBox7 (!canonicalBox7_410.bump)) = canonicalBox7_410 := by decide +kernel

theorem canonicalDecode7_410 : canonicalBox7_410.toKeyData 188160 = keys7Chunk12.get ⟨26, by decide⟩ := by
  change canonicalBox7_410.toKeyData 188160 = ⟨![(17 / 28), 2, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (673 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_410 : keySolid (keys7Chunk12.get ⟨26, by decide⟩) = canonicalPose7_410.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_410 (box := canonicalBox7_410) (k := keys7Chunk12.get ⟨26, by decide⟩) (canonicalMatch7_410) (canonicalDecode7_410)

def canonicalPose7_411 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, false, false, true, true], ![1, 2, 2, 0, 0, 2, 2]⟩
def canonicalBox7_411 : BoxKey 7 :=
  ⟨![60480, 255360, 376320, 114240, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 376880, 114688, 108010, 274960, 241535], true⟩

theorem canonicalMatch7_411 :
    canonicalPose7_411.boxKey 188160 (referenceBox7 (!canonicalBox7_411.bump)) = canonicalBox7_411 := by decide +kernel

theorem canonicalDecode7_411 : canonicalBox7_411.toKeyData 188160 = keys7Chunk12.get ⟨27, by decide⟩ := by
  change canonicalBox7_411.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (673 / 336), (64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_411 : keySolid (keys7Chunk12.get ⟨27, by decide⟩) = canonicalPose7_411.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_411 (box := canonicalBox7_411) (k := keys7Chunk12.get ⟨27, by decide⟩) (canonicalMatch7_411) (canonicalDecode7_411)

def canonicalPose7_412 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, false, true, false, false, true, false], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_412 : BoxKey 7 :=
  ⟨![127680, 309120, 262080, 0, 107520, 275520, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 309540, 261632, 560, 108010, 274960, 322945], false⟩

theorem canonicalMatch7_412 :
    canonicalPose7_412.boxKey 188160 (referenceBox7 (!canonicalBox7_412.bump)) = canonicalBox7_412 := by decide +kernel

theorem canonicalDecode7_412 : canonicalBox7_412.toKeyData 188160 = keys7Chunk12.get ⟨28, by decide⟩ := by
  change canonicalBox7_412.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (146 / 105), (1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_412 : keySolid (keys7Chunk12.get ⟨28, by decide⟩) = canonicalPose7_412.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_412 (box := canonicalBox7_412) (k := keys7Chunk12.get ⟨28, by decide⟩) (canonicalMatch7_412) (canonicalDecode7_412)

def canonicalPose7_413 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, false, true, false, true, true, false], ![0, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_413 : BoxKey 7 :=
  ⟨![127680, 322560, 275520, 107520, 0, 262080, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 322945, 274960, 108010, -560, 261632, 309540], true⟩

theorem canonicalMatch7_413 :
    canonicalPose7_413.boxKey 188160 (referenceBox7 (!canonicalBox7_413.bump)) = canonicalBox7_413 := by decide +kernel

theorem canonicalDecode7_413 : canonicalBox7_413.toKeyData 188160 = keys7Chunk12.get ⟨29, by decide⟩ := by
  change canonicalBox7_413.toKeyData 188160 = ⟨![(19 / 28), (12 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (-1 / 336), (146 / 105), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_413 : keySolid (keys7Chunk12.get ⟨29, by decide⟩) = canonicalPose7_413.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_413 (box := canonicalBox7_413) (k := keys7Chunk12.get ⟨29, by decide⟩) (canonicalMatch7_413) (canonicalDecode7_413)

def canonicalPose7_414 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, false, false, true, true], ![1, 2, 2, 0, 0, 2, 2]⟩
def canonicalBox7_414 : BoxKey 7 :=
  ⟨![60480, 241920, 275520, 107520, 114240, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 241535, 274960, 108010, 114688, 375760, 254940], false⟩

theorem canonicalMatch7_414 :
    canonicalPose7_414.boxKey 188160 (referenceBox7 (!canonicalBox7_414.bump)) = canonicalBox7_414 := by decide +kernel

theorem canonicalDecode7_414 : canonicalBox7_414.toKeyData 188160 = keys7Chunk12.get ⟨30, by decide⟩ := by
  change canonicalBox7_414.toKeyData 188160 = ⟨![(9 / 28), (9 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (671 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_414 : keySolid (keys7Chunk12.get ⟨30, by decide⟩) = canonicalPose7_414.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_414 (box := canonicalBox7_414) (k := keys7Chunk12.get ⟨30, by decide⟩) (canonicalMatch7_414) (canonicalDecode7_414)

def canonicalPose7_415 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, true, true, true, true, true], ![0, 2, 2, 1, 1, 2, 2]⟩
def canonicalBox7_415 : BoxKey 7 :=
  ⟨![114240, 268800, 275520, 53760, 60480, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 268310, 274960, 53375, 60080, 254940, 375760], false⟩

theorem canonicalMatch7_415 :
    canonicalPose7_415.boxKey 188160 (referenceBox7 (!canonicalBox7_415.bump)) = canonicalBox7_415 := by decide +kernel

theorem canonicalDecode7_415 : canonicalBox7_415.toKeyData 188160 = keys7Chunk12.get ⟨31, by decide⟩ := by
  change canonicalBox7_415.toKeyData 188160 = ⟨![(17 / 28), (10 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_415 : keySolid (keys7Chunk12.get ⟨31, by decide⟩) = canonicalPose7_415.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_415 (box := canonicalBox7_415) (k := keys7Chunk12.get ⟨31, by decide⟩) (canonicalMatch7_415) (canonicalDecode7_415)

theorem keys7Chunk12_canonical : ∀ k ∈ keys7Chunk12,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk12, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_384, canonicalSolid7_384⟩
  · exact ⟨canonicalPose7_385, canonicalSolid7_385⟩
  · exact ⟨canonicalPose7_386, canonicalSolid7_386⟩
  · exact ⟨canonicalPose7_387, canonicalSolid7_387⟩
  · exact ⟨canonicalPose7_388, canonicalSolid7_388⟩
  · exact ⟨canonicalPose7_389, canonicalSolid7_389⟩
  · exact ⟨canonicalPose7_390, canonicalSolid7_390⟩
  · exact ⟨canonicalPose7_391, canonicalSolid7_391⟩
  · exact ⟨canonicalPose7_392, canonicalSolid7_392⟩
  · exact ⟨canonicalPose7_393, canonicalSolid7_393⟩
  · exact ⟨canonicalPose7_394, canonicalSolid7_394⟩
  · exact ⟨canonicalPose7_395, canonicalSolid7_395⟩
  · exact ⟨canonicalPose7_396, canonicalSolid7_396⟩
  · exact ⟨canonicalPose7_397, canonicalSolid7_397⟩
  · exact ⟨canonicalPose7_398, canonicalSolid7_398⟩
  · exact ⟨canonicalPose7_399, canonicalSolid7_399⟩
  · exact ⟨canonicalPose7_400, canonicalSolid7_400⟩
  · exact ⟨canonicalPose7_401, canonicalSolid7_401⟩
  · exact ⟨canonicalPose7_402, canonicalSolid7_402⟩
  · exact ⟨canonicalPose7_403, canonicalSolid7_403⟩
  · exact ⟨canonicalPose7_404, canonicalSolid7_404⟩
  · exact ⟨canonicalPose7_405, canonicalSolid7_405⟩
  · exact ⟨canonicalPose7_406, canonicalSolid7_406⟩
  · exact ⟨canonicalPose7_407, canonicalSolid7_407⟩
  · exact ⟨canonicalPose7_408, canonicalSolid7_408⟩
  · exact ⟨canonicalPose7_409, canonicalSolid7_409⟩
  · exact ⟨canonicalPose7_410, canonicalSolid7_410⟩
  · exact ⟨canonicalPose7_411, canonicalSolid7_411⟩
  · exact ⟨canonicalPose7_412, canonicalSolid7_412⟩
  · exact ⟨canonicalPose7_413, canonicalSolid7_413⟩
  · exact ⟨canonicalPose7_414, canonicalSolid7_414⟩
  · exact ⟨canonicalPose7_415, canonicalSolid7_415⟩

#print axioms keys7Chunk12_canonical

end SparseMonotiles.Canonical
