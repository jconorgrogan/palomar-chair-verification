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

def canonicalPose7_416 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, false, true, false, true], ![0, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_416 : BoxKey 7 :=
  ⟨![0, 302400, 268800, 100800, 241920, 127680, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 302848, 268310, 101360, 241535, 128080, 66780], true⟩

theorem canonicalMatch7_416 :
    canonicalPose7_416.boxKey 188160 (referenceBox7 (!canonicalBox7_416.bump)) = canonicalBox7_416 := by decide +kernel

theorem canonicalDecode7_416 : canonicalBox7_416.toKeyData 188160 = keys7Chunk13.get ⟨0, by decide⟩ := by
  change canonicalBox7_416.toKeyData 188160 = ⟨![0, (45 / 28), (10 / 7), (15 / 28), (9 / 7), (19 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_416 : keySolid (keys7Chunk13.get ⟨0, by decide⟩) = canonicalPose7_416.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_416 (box := canonicalBox7_416) (k := keys7Chunk13.get ⟨0, by decide⟩) (canonicalMatch7_416) (canonicalDecode7_416)

def canonicalPose7_417 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, true, false, true, false, true], ![0, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_417 : BoxKey 7 :=
  ⟨![0, 309120, 248640, 134400, 275520, 107520, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 309540, 248240, 134785, 274960, 108010, 73472], false⟩

theorem canonicalMatch7_417 :
    canonicalPose7_417.boxKey 188160 (referenceBox7 (!canonicalBox7_417.bump)) = canonicalBox7_417 := by decide +kernel

theorem canonicalDecode7_417 : canonicalBox7_417.toKeyData 188160 = keys7Chunk13.get ⟨1, by decide⟩ := by
  change canonicalBox7_417.toKeyData 188160 = ⟨![0, (23 / 14), (37 / 28), (5 / 7), (41 / 28), (4 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_417 : keySolid (keys7Chunk13.get ⟨1, by decide⟩) = canonicalPose7_417.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_417 (box := canonicalBox7_417) (k := keys7Chunk13.get ⟨1, by decide⟩) (canonicalMatch7_417) (canonicalDecode7_417)

def canonicalPose7_418 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, true, true, false, false, false], ![0, 2, 2, 1, 1, 0, 0]⟩
def canonicalBox7_418 : BoxKey 7 :=
  ⟨![114240, 376320, 255360, 60480, 322560, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 375760, 254940, 60080, 322945, 101360, 108010], false⟩

theorem canonicalMatch7_418 :
    canonicalPose7_418.boxKey 188160 (referenceBox7 (!canonicalBox7_418.bump)) = canonicalBox7_418 := by decide +kernel

theorem canonicalDecode7_418 : canonicalBox7_418.toKeyData 188160 = keys7Chunk13.get ⟨2, by decide⟩ := by
  change canonicalBox7_418.toKeyData 188160 = ⟨![(17 / 28), 2, (19 / 14), (9 / 28), (12 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (671 / 336), (607 / 448), (751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_418 : keySolid (keys7Chunk13.get ⟨2, by decide⟩) = canonicalPose7_418.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_418 (box := canonicalBox7_418) (k := keys7Chunk13.get ⟨2, by decide⟩) (canonicalMatch7_418) (canonicalDecode7_418)

def canonicalPose7_419 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, true, false, true, false, false], ![1, 2, 2, 0, 2, 0, 0]⟩
def canonicalBox7_419 : BoxKey 7 :=
  ⟨![60480, 255360, 376320, 114240, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 375760, 114688, 268310, 101360, 134785], false⟩

theorem canonicalMatch7_419 :
    canonicalPose7_419.boxKey 188160 (referenceBox7 (!canonicalBox7_419.bump)) = canonicalBox7_419 := by decide +kernel

theorem canonicalDecode7_419 : canonicalBox7_419.toKeyData 188160 = keys7Chunk13.get ⟨3, by decide⟩ := by
  change canonicalBox7_419.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_419 : keySolid (keys7Chunk13.get ⟨3, by decide⟩) = canonicalPose7_419.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_419 (box := canonicalBox7_419) (k := keys7Chunk13.get ⟨3, by decide⟩) (canonicalMatch7_419) (canonicalDecode7_419)

def canonicalPose7_420 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, false, true, true, true, false, true], ![0, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_420 : BoxKey 7 :=
  ⟨![127680, 309120, 262080, 0, 268800, 100800, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 309540, 261632, -560, 268310, 101360, 53375], true⟩

theorem canonicalMatch7_420 :
    canonicalPose7_420.boxKey 188160 (referenceBox7 (!canonicalBox7_420.bump)) = canonicalBox7_420 := by decide +kernel

theorem canonicalDecode7_420 : canonicalBox7_420.toKeyData 188160 = keys7Chunk13.get ⟨4, by decide⟩ := by
  change canonicalBox7_420.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), (39 / 28), 0, (10 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (146 / 105), (-1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_420 : keySolid (keys7Chunk13.get ⟨4, by decide⟩) = canonicalPose7_420.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_420 (box := canonicalBox7_420) (k := keys7Chunk13.get ⟨4, by decide⟩) (canonicalMatch7_420) (canonicalDecode7_420)

def canonicalPose7_421 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, false, true, false, true, false, true], ![0, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_421 : BoxKey 7 :=
  ⟨![127680, 322560, 275520, 107520, 376320, 114240, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 322945, 274960, 108010, 375760, 114688, 66780], false⟩

theorem canonicalMatch7_421 :
    canonicalPose7_421.boxKey 188160 (referenceBox7 (!canonicalBox7_421.bump)) = canonicalBox7_421 := by decide +kernel

theorem canonicalDecode7_421 : canonicalBox7_421.toKeyData 188160 = keys7Chunk13.get ⟨5, by decide⟩ := by
  change canonicalBox7_421.toKeyData 188160 = ⟨![(19 / 28), (12 / 7), (41 / 28), (4 / 7), 2, (17 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (671 / 336), (64 / 105), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_421 : keySolid (keys7Chunk13.get ⟨5, by decide⟩) = canonicalPose7_421.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_421 (box := canonicalBox7_421) (k := keys7Chunk13.get ⟨5, by decide⟩) (canonicalMatch7_421) (canonicalDecode7_421)

def canonicalPose7_422 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, false, true, true, false], ![1, 2, 2, 0, 2, 0, 0]⟩
def canonicalBox7_422 : BoxKey 7 :=
  ⟨![60480, 241920, 275520, 107520, 262080, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 241535, 274960, 108010, 261632, -560, 121380], true⟩

theorem canonicalMatch7_422 :
    canonicalPose7_422.boxKey 188160 (referenceBox7 (!canonicalBox7_422.bump)) = canonicalBox7_422 := by decide +kernel

theorem canonicalDecode7_422 : canonicalBox7_422.toKeyData 188160 = keys7Chunk13.get ⟨6, by decide⟩ := by
  change canonicalBox7_422.toKeyData 188160 = ⟨![(9 / 28), (9 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (-1 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_422 : keySolid (keys7Chunk13.get ⟨6, by decide⟩) = canonicalPose7_422.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_422 (box := canonicalBox7_422) (k := keys7Chunk13.get ⟨6, by decide⟩) (canonicalMatch7_422) (canonicalDecode7_422)

def canonicalPose7_423 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, true, true, false, false, true], ![0, 2, 2, 1, 1, 0, 0]⟩
def canonicalBox7_423 : BoxKey 7 :=
  ⟨![114240, 268800, 275520, 53760, 315840, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 268310, 274960, 53375, 316240, 121380, -560], true⟩

theorem canonicalMatch7_423 :
    canonicalPose7_423.boxKey 188160 (referenceBox7 (!canonicalBox7_423.bump)) = canonicalBox7_423 := by decide +kernel

theorem canonicalDecode7_423 : canonicalBox7_423.toKeyData 188160 = keys7Chunk13.get ⟨7, by decide⟩ := by
  change canonicalBox7_423.toKeyData 188160 = ⟨![(17 / 28), (10 / 7), (41 / 28), (2 / 7), (47 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_423 : keySolid (keys7Chunk13.get ⟨7, by decide⟩) = canonicalPose7_423.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_423 (box := canonicalBox7_423) (k := keys7Chunk13.get ⟨7, by decide⟩) (canonicalMatch7_423) (canonicalDecode7_423)

def canonicalPose7_424 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, true, false, true, true, true], ![0, 2, 2, 0, 2, 1, 2]⟩
def canonicalBox7_424 : BoxKey 7 :=
  ⟨![0, 262080, 268800, 100800, 241920, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 261632, 268310, 101360, 241535, 60080, 254940], true⟩

theorem canonicalMatch7_424 :
    canonicalPose7_424.boxKey 188160 (referenceBox7 (!canonicalBox7_424.bump)) = canonicalBox7_424 := by decide +kernel

theorem canonicalDecode7_424 : canonicalBox7_424.toKeyData 188160 = keys7Chunk13.get ⟨8, by decide⟩ := by
  change canonicalBox7_424.toKeyData 188160 = ⟨![0, (39 / 28), (10 / 7), (15 / 28), (9 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (751 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_424 : keySolid (keys7Chunk13.get ⟨8, by decide⟩) = canonicalPose7_424.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_424 (box := canonicalBox7_424) (k := keys7Chunk13.get ⟨8, by decide⟩) (canonicalMatch7_424) (canonicalDecode7_424)

def canonicalPose7_425 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, true, true, false, false, false, false], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_425 : BoxKey 7 :=
  ⟨![114240, 376320, 268800, 100800, 322560, 127680, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, 375760, 268310, 101360, 322945, 128080, 309540], false⟩

theorem canonicalMatch7_425 :
    canonicalPose7_425.boxKey 188160 (referenceBox7 (!canonicalBox7_425.bump)) = canonicalBox7_425 := by decide +kernel

theorem canonicalDecode7_425 : canonicalBox7_425.toKeyData 188160 = keys7Chunk13.get ⟨9, by decide⟩ := by
  change canonicalBox7_425.toKeyData 188160 = ⟨![(17 / 28), 2, (10 / 7), (15 / 28), (12 / 7), (19 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (671 / 336), (3833 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_425 : keySolid (keys7Chunk13.get ⟨9, by decide⟩) = canonicalPose7_425.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_425 (box := canonicalBox7_425) (k := keys7Chunk13.get ⟨9, by decide⟩) (canonicalMatch7_425) (canonicalDecode7_425)

def canonicalPose7_426 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, true, false, false, false, false, false], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_426 : BoxKey 7 :=
  ⟨![100800, 268800, 376320, 114240, 309120, 127680, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 268310, 376880, 114688, 309540, 128080, 322945], true⟩

theorem canonicalMatch7_426 :
    canonicalPose7_426.boxKey 188160 (referenceBox7 (!canonicalBox7_426.bump)) = canonicalBox7_426 := by decide +kernel

theorem canonicalDecode7_426 : canonicalBox7_426.toKeyData 188160 = keys7Chunk13.get ⟨10, by decide⟩ := by
  change canonicalBox7_426.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), 2, (17 / 28), (23 / 14), (19 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (673 / 336), (64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_426 : keySolid (keys7Chunk13.get ⟨10, by decide⟩) = canonicalPose7_426.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_426 (box := canonicalBox7_426) (k := keys7Chunk13.get ⟨10, by decide⟩) (canonicalMatch7_426) (canonicalDecode7_426)

def canonicalPose7_427 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, false, true, true, true], ![0, 2, 2, 0, 2, 1, 2]⟩
def canonicalBox7_427 : BoxKey 7 :=
  ⟨![100800, 268800, 262080, 0, 255360, 60480, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 261632, 560, 254940, 60080, 241535], false⟩

theorem canonicalMatch7_427 :
    canonicalPose7_427.boxKey 188160 (referenceBox7 (!canonicalBox7_427.bump)) = canonicalBox7_427 := by decide +kernel

theorem canonicalDecode7_427 : canonicalBox7_427.toKeyData 188160 = keys7Chunk13.get ⟨11, by decide⟩ := by
  change canonicalBox7_427.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (39 / 28), 0, (19 / 14), (9 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (146 / 105), (1 / 336), (607 / 448), (751 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_427 : keySolid (keys7Chunk13.get ⟨11, by decide⟩) = canonicalPose7_427.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_427 (box := canonicalBox7_427) (k := keys7Chunk13.get ⟨11, by decide⟩) (canonicalMatch7_427) (canonicalDecode7_427)

def canonicalPose7_428 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, true, false, true], ![0, 1, 1, 0, 2, 0, 2]⟩
def canonicalBox7_428 : BoxKey 7 :=
  ⟨![100800, 322560, 315840, 120960, 376320, 114240, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 322945, 316240, 121380, 375760, 114688, 268310], false⟩

theorem canonicalMatch7_428 :
    canonicalPose7_428.boxKey 188160 (referenceBox7 (!canonicalBox7_428.bump)) = canonicalBox7_428 := by decide +kernel

theorem canonicalDecode7_428 : canonicalBox7_428.toKeyData 188160 = keys7Chunk13.get ⟨12, by decide⟩ := by
  change canonicalBox7_428.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (47 / 28), (9 / 14), 2, (17 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (64 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_428 : keySolid (keys7Chunk13.get ⟨12, by decide⟩) = canonicalPose7_428.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_428 (box := canonicalBox7_428) (k := keys7Chunk13.get ⟨12, by decide⟩) (canonicalMatch7_428) (canonicalDecode7_428)

def canonicalPose7_429 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, false, false, false, false], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_429 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 127680, 309120, 0, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 128080, 309540, 560, 302848], false⟩

theorem canonicalMatch7_429 :
    canonicalPose7_429.boxKey 188160 (referenceBox7 (!canonicalBox7_429.bump)) = canonicalBox7_429 := by decide +kernel

theorem canonicalDecode7_429 : canonicalBox7_429.toKeyData 188160 = keys7Chunk13.get ⟨13, by decide⟩ := by
  change canonicalBox7_429.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (19 / 28), (23 / 14), 0, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448), (1 / 336), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_429 : keySolid (keys7Chunk13.get ⟨13, by decide⟩) = canonicalPose7_429.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_429 (box := canonicalBox7_429) (k := keys7Chunk13.get ⟨13, by decide⟩) (canonicalMatch7_429) (canonicalDecode7_429)

def canonicalPose7_430 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, false, false, true, false], ![0, 2, 2, 0, 1, 0, 1]⟩
def canonicalBox7_430 : BoxKey 7 :=
  ⟨![127680, 241920, 275520, 107520, 302400, 0, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 241535, 274960, 108010, 302848, -560, 309540], true⟩

theorem canonicalMatch7_430 :
    canonicalPose7_430.boxKey 188160 (referenceBox7 (!canonicalBox7_430.bump)) = canonicalBox7_430 := by decide +kernel

theorem canonicalDecode7_430 : canonicalBox7_430.toKeyData 188160 = keys7Chunk13.get ⟨14, by decide⟩ := by
  change canonicalBox7_430.toKeyData 188160 = ⟨![(19 / 28), (9 / 7), (41 / 28), (4 / 7), (45 / 28), 0, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105), (-1 / 336), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_430 : keySolid (keys7Chunk13.get ⟨14, by decide⟩) = canonicalPose7_430.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_430 (box := canonicalBox7_430) (k := keys7Chunk13.get ⟨14, by decide⟩) (canonicalMatch7_430) (canonicalDecode7_430)

def canonicalPose7_431 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, true, false, false], ![0, 1, 1, 0, 2, 0, 2]⟩
def canonicalBox7_431 : BoxKey 7 :=
  ⟨![120960, 315840, 322560, 100800, 268800, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 322945, 101360, 268310, 114688, 376880], true⟩

theorem canonicalMatch7_431 :
    canonicalPose7_431.boxKey 188160 (referenceBox7 (!canonicalBox7_431.bump)) = canonicalBox7_431 := by decide +kernel

theorem canonicalDecode7_431 : canonicalBox7_431.toKeyData 188160 = keys7Chunk13.get ⟨15, by decide⟩ := by
  change canonicalBox7_431.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (12 / 7), (15 / 28), (10 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_431 : keySolid (keys7Chunk13.get ⟨15, by decide⟩) = canonicalPose7_431.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_431 (box := canonicalBox7_431) (k := keys7Chunk13.get ⟨15, by decide⟩) (canonicalMatch7_431) (canonicalDecode7_431)

def canonicalPose7_432 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, true, false, false, false, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_432 : BoxKey 7 :=
  ⟨![0, 262080, 309120, 127680, 322560, 275520, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![-560, 261632, 309540, 128080, 322945, 274960, 108010], true⟩

theorem canonicalMatch7_432 :
    canonicalPose7_432.boxKey 188160 (referenceBox7 (!canonicalBox7_432.bump)) = canonicalBox7_432 := by decide +kernel

theorem canonicalDecode7_432 : canonicalBox7_432.toKeyData 188160 = keys7Chunk13.get ⟨16, by decide⟩ := by
  change canonicalBox7_432.toKeyData 188160 = ⟨![0, (39 / 28), (23 / 14), (19 / 28), (12 / 7), (41 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(-1 / 336), (146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_432 : keySolid (keys7Chunk13.get ⟨16, by decide⟩) = canonicalPose7_432.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_432 (box := canonicalBox7_432) (k := keys7Chunk13.get ⟨16, by decide⟩) (canonicalMatch7_432) (canonicalDecode7_432)

def canonicalPose7_433 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, true, true, true, true, false], ![0, 2, 2, 1, 2, 2, 0]⟩
def canonicalBox7_433 : BoxKey 7 :=
  ⟨![114240, 376320, 255360, 60480, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 375760, 254940, 60080, 241535, 274960, 108010], false⟩

theorem canonicalMatch7_433 :
    canonicalPose7_433.boxKey 188160 (referenceBox7 (!canonicalBox7_433.bump)) = canonicalBox7_433 := by decide +kernel

theorem canonicalDecode7_433 : canonicalBox7_433.toKeyData 188160 = keys7Chunk13.get ⟨17, by decide⟩ := by
  change canonicalBox7_433.toKeyData 188160 = ⟨![(17 / 28), 2, (19 / 14), (9 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (671 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_433 : keySolid (keys7Chunk13.get ⟨17, by decide⟩) = canonicalPose7_433.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_433 (box := canonicalBox7_433) (k := keys7Chunk13.get ⟨17, by decide⟩) (canonicalMatch7_433) (canonicalDecode7_433)

def canonicalPose7_434 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, true, false, true, true, true], ![1, 2, 2, 0, 2, 2, 1]⟩
def canonicalBox7_434 : BoxKey 7 :=
  ⟨![60480, 255360, 376320, 114240, 268800, 275520, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 375760, 114688, 268310, 274960, 53375], false⟩

theorem canonicalMatch7_434 :
    canonicalPose7_434.boxKey 188160 (referenceBox7 (!canonicalBox7_434.bump)) = canonicalBox7_434 := by decide +kernel

theorem canonicalDecode7_434 : canonicalBox7_434.toKeyData 188160 = keys7Chunk13.get ⟨18, by decide⟩ := by
  change canonicalBox7_434.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_434 : keySolid (keys7Chunk13.get ⟨18, by decide⟩) = canonicalPose7_434.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_434 (box := canonicalBox7_434) (k := keys7Chunk13.get ⟨18, by decide⟩) (canonicalMatch7_434) (canonicalDecode7_434)

def canonicalPose7_435 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, true, false, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_435 : BoxKey 7 :=
  ⟨![100800, 268800, 302400, 0, 309120, 248640, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 302848, -560, 309540, 248240, 134785], true⟩

theorem canonicalMatch7_435 :
    canonicalPose7_435.boxKey 188160 (referenceBox7 (!canonicalBox7_435.bump)) = canonicalBox7_435 := by decide +kernel

theorem canonicalDecode7_435 : canonicalBox7_435.toKeyData 188160 = keys7Chunk13.get ⟨19, by decide⟩ := by
  change canonicalBox7_435.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (45 / 28), 0, (23 / 14), (37 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (169 / 105), (-1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_435 : keySolid (keys7Chunk13.get ⟨19, by decide⟩) = canonicalPose7_435.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_435 (box := canonicalBox7_435) (k := keys7Chunk13.get ⟨19, by decide⟩) (canonicalMatch7_435) (canonicalDecode7_435)

def canonicalPose7_436 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, false, false, false, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_436 : BoxKey 7 :=
  ⟨![134400, 248640, 309120, 0, 302400, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 248240, 309540, 560, 302848, 268310, 101360], false⟩

theorem canonicalMatch7_436 :
    canonicalPose7_436.boxKey 188160 (referenceBox7 (!canonicalBox7_436.bump)) = canonicalBox7_436 := by decide +kernel

theorem canonicalDecode7_436 : canonicalBox7_436.toKeyData 188160 = keys7Chunk13.get ⟨20, by decide⟩ := by
  change canonicalBox7_436.toKeyData 188160 = ⟨![(5 / 7), (37 / 28), (23 / 14), 0, (45 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3103 / 2352), (737 / 448), (1 / 336), (169 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_436 : keySolid (keys7Chunk13.get ⟨20, by decide⟩) = canonicalPose7_436.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_436 (box := canonicalBox7_436) (k := keys7Chunk13.get ⟨20, by decide⟩) (canonicalMatch7_436) (canonicalDecode7_436)

def canonicalPose7_437 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, false, false, true, true], ![1, 2, 2, 0, 2, 2, 1]⟩
def canonicalBox7_437 : BoxKey 7 :=
  ⟨![53760, 275520, 268800, 114240, 376320, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 274960, 268310, 114688, 376880, 254940, 60080], true⟩

theorem canonicalMatch7_437 :
    canonicalPose7_437.boxKey 188160 (referenceBox7 (!canonicalBox7_437.bump)) = canonicalBox7_437 := by decide +kernel

theorem canonicalDecode7_437 : canonicalBox7_437.toKeyData 188160 = keys7Chunk13.get ⟨21, by decide⟩ := by
  change canonicalBox7_437.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_437 : keySolid (keys7Chunk13.get ⟨21, by decide⟩) = canonicalPose7_437.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_437 (box := canonicalBox7_437) (k := keys7Chunk13.get ⟨21, by decide⟩) (canonicalMatch7_437) (canonicalDecode7_437)

def canonicalPose7_438 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, true, true, false, false], ![0, 2, 2, 1, 2, 2, 0]⟩
def canonicalBox7_438 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 60480, 255360, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 60080, 254940, 376880, 114688], true⟩

theorem canonicalMatch7_438 :
    canonicalPose7_438.boxKey 188160 (referenceBox7 (!canonicalBox7_438.bump)) = canonicalBox7_438 := by decide +kernel

theorem canonicalDecode7_438 : canonicalBox7_438.toKeyData 188160 = keys7Chunk13.get ⟨22, by decide⟩ := by
  change canonicalBox7_438.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (9 / 28), (19 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (673 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_438 : keySolid (keys7Chunk13.get ⟨22, by decide⟩) = canonicalPose7_438.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_438 (box := canonicalBox7_438) (k := keys7Chunk13.get ⟨22, by decide⟩) (canonicalMatch7_438) (canonicalDecode7_438)

def canonicalPose7_439 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, true, false, false, false, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_439 : BoxKey 7 :=
  ⟨![107520, 275520, 322560, 127680, 309120, 262080, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 274960, 322945, 128080, 309540, 261632, 560], false⟩

theorem canonicalMatch7_439 :
    canonicalPose7_439.boxKey 188160 (referenceBox7 (!canonicalBox7_439.bump)) = canonicalBox7_439 := by decide +kernel

theorem canonicalDecode7_439 : canonicalBox7_439.toKeyData 188160 = keys7Chunk13.get ⟨23, by decide⟩ := by
  change canonicalBox7_439.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (12 / 7), (19 / 28), (23 / 14), (39 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_439 : keySolid (keys7Chunk13.get ⟨23, by decide⟩) = canonicalPose7_439.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_439 (box := canonicalBox7_439) (k := keys7Chunk13.get ⟨23, by decide⟩) (canonicalMatch7_439) (canonicalDecode7_439)

def canonicalPose7_440 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, false, true, false, true], ![0, 2, 2, 0, 2, 1, 2]⟩
def canonicalBox7_440 : BoxKey 7 :=
  ⟨![0, 262080, 268800, 100800, 241920, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 261632, 268310, 101360, 241535, 316240, 254940], false⟩

theorem canonicalMatch7_440 :
    canonicalPose7_440.boxKey 188160 (referenceBox7 (!canonicalBox7_440.bump)) = canonicalBox7_440 := by decide +kernel

theorem canonicalDecode7_440 : canonicalBox7_440.toKeyData 188160 = keys7Chunk13.get ⟨24, by decide⟩ := by
  change canonicalBox7_440.toKeyData 188160 = ⟨![0, (39 / 28), (10 / 7), (15 / 28), (9 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_440 : keySolid (keys7Chunk13.get ⟨24, by decide⟩) = canonicalPose7_440.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_440 (box := canonicalBox7_440) (k := keys7Chunk13.get ⟨24, by decide⟩) (canonicalMatch7_440) (canonicalDecode7_440)

def canonicalPose7_441 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, false, true, false, false, true, false], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_441 : BoxKey 7 :=
  ⟨![114240, 376320, 268800, 100800, 322560, 248640, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, 376880, 268310, 101360, 322945, 248240, 309540], true⟩

theorem canonicalMatch7_441 :
    canonicalPose7_441.boxKey 188160 (referenceBox7 (!canonicalBox7_441.bump)) = canonicalBox7_441 := by decide +kernel

theorem canonicalDecode7_441 : canonicalBox7_441.toKeyData 188160 = keys7Chunk13.get ⟨25, by decide⟩ := by
  change canonicalBox7_441.toKeyData 188160 = ⟨![(17 / 28), 2, (10 / 7), (15 / 28), (12 / 7), (37 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (673 / 336), (3833 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_441 : keySolid (keys7Chunk13.get ⟨25, by decide⟩) = canonicalPose7_441.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_441 (box := canonicalBox7_441) (k := keys7Chunk13.get ⟨25, by decide⟩) (canonicalMatch7_441) (canonicalDecode7_441)

def canonicalPose7_442 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, true, true, false, false, true, false], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_442 : BoxKey 7 :=
  ⟨![100800, 268800, 376320, 114240, 309120, 248640, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 268310, 375760, 114688, 309540, 248240, 322945], false⟩

theorem canonicalMatch7_442 :
    canonicalPose7_442.boxKey 188160 (referenceBox7 (!canonicalBox7_442.bump)) = canonicalBox7_442 := by decide +kernel

theorem canonicalDecode7_442 : canonicalBox7_442.toKeyData 188160 = keys7Chunk13.get ⟨26, by decide⟩ := by
  change canonicalBox7_442.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), 2, (17 / 28), (23 / 14), (37 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (671 / 336), (64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_442 : keySolid (keys7Chunk13.get ⟨26, by decide⟩) = canonicalPose7_442.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_442 (box := canonicalBox7_442) (k := keys7Chunk13.get ⟨26, by decide⟩) (canonicalMatch7_442) (canonicalDecode7_442)

def canonicalPose7_443 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, true, true, false, true], ![0, 2, 2, 0, 2, 1, 2]⟩
def canonicalBox7_443 : BoxKey 7 :=
  ⟨![100800, 268800, 262080, 0, 255360, 315840, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 261632, -560, 254940, 316240, 241535], true⟩

theorem canonicalMatch7_443 :
    canonicalPose7_443.boxKey 188160 (referenceBox7 (!canonicalBox7_443.bump)) = canonicalBox7_443 := by decide +kernel

theorem canonicalDecode7_443 : canonicalBox7_443.toKeyData 188160 = keys7Chunk13.get ⟨27, by decide⟩ := by
  change canonicalBox7_443.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (39 / 28), 0, (19 / 14), (47 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_443 : keySolid (keys7Chunk13.get ⟨27, by decide⟩) = canonicalPose7_443.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_443 (box := canonicalBox7_443) (k := keys7Chunk13.get ⟨27, by decide⟩) (canonicalMatch7_443) (canonicalDecode7_443)

def canonicalPose7_444 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, false, true, true], ![0, 1, 1, 0, 2, 2, 2]⟩
def canonicalBox7_444 : BoxKey 7 :=
  ⟨![100800, 322560, 315840, 120960, 376320, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 322945, 316240, 121380, 376880, 261632, 268310], true⟩

theorem canonicalMatch7_444 :
    canonicalPose7_444.boxKey 188160 (referenceBox7 (!canonicalBox7_444.bump)) = canonicalBox7_444 := by decide +kernel

theorem canonicalDecode7_444 : canonicalBox7_444.toKeyData 188160 = keys7Chunk13.get ⟨28, by decide⟩ := by
  change canonicalBox7_444.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (47 / 28), (9 / 14), 2, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_444 : keySolid (keys7Chunk13.get ⟨28, by decide⟩) = canonicalPose7_444.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_444 (box := canonicalBox7_444) (k := keys7Chunk13.get ⟨28, by decide⟩) (canonicalMatch7_444) (canonicalDecode7_444)

def canonicalPose7_445 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, false, false, false, false], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_445 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 127680, 309120, 376320, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 128080, 309540, 376880, 302848], true⟩

theorem canonicalMatch7_445 :
    canonicalPose7_445.boxKey 188160 (referenceBox7 (!canonicalBox7_445.bump)) = canonicalBox7_445 := by decide +kernel

theorem canonicalDecode7_445 : canonicalBox7_445.toKeyData 188160 = keys7Chunk13.get ⟨29, by decide⟩ := by
  change canonicalBox7_445.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (19 / 28), (23 / 14), 2, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448), (673 / 336), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_445 : keySolid (keys7Chunk13.get ⟨29, by decide⟩) = canonicalPose7_445.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_445 (box := canonicalBox7_445) (k := keys7Chunk13.get ⟨29, by decide⟩) (canonicalMatch7_445) (canonicalDecode7_445)

def canonicalPose7_446 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, false, false, true, false], ![0, 2, 2, 0, 1, 2, 1]⟩
def canonicalBox7_446 : BoxKey 7 :=
  ⟨![127680, 241920, 275520, 107520, 302400, 376320, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 241535, 274960, 108010, 302848, 375760, 309540], false⟩

theorem canonicalMatch7_446 :
    canonicalPose7_446.boxKey 188160 (referenceBox7 (!canonicalBox7_446.bump)) = canonicalBox7_446 := by decide +kernel

theorem canonicalDecode7_446 : canonicalBox7_446.toKeyData 188160 = keys7Chunk13.get ⟨30, by decide⟩ := by
  change canonicalBox7_446.toKeyData 188160 = ⟨![(19 / 28), (9 / 7), (41 / 28), (4 / 7), (45 / 28), 2, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105), (671 / 336), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_446 : keySolid (keys7Chunk13.get ⟨30, by decide⟩) = canonicalPose7_446.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_446 (box := canonicalBox7_446) (k := keys7Chunk13.get ⟨30, by decide⟩) (canonicalMatch7_446) (canonicalDecode7_446)

def canonicalPose7_447 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, true, true, true], ![0, 1, 1, 0, 2, 2, 2]⟩
def canonicalBox7_447 : BoxKey 7 :=
  ⟨![120960, 315840, 322560, 100800, 268800, 262080, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 322945, 101360, 268310, 261632, 375760], false⟩

theorem canonicalMatch7_447 :
    canonicalPose7_447.boxKey 188160 (referenceBox7 (!canonicalBox7_447.bump)) = canonicalBox7_447 := by decide +kernel

theorem canonicalDecode7_447 : canonicalBox7_447.toKeyData 188160 = keys7Chunk13.get ⟨31, by decide⟩ := by
  change canonicalBox7_447.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (12 / 7), (15 / 28), (10 / 7), (39 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_447 : keySolid (keys7Chunk13.get ⟨31, by decide⟩) = canonicalPose7_447.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_447 (box := canonicalBox7_447) (k := keys7Chunk13.get ⟨31, by decide⟩) (canonicalMatch7_447) (canonicalDecode7_447)

theorem keys7Chunk13_canonical : ∀ k ∈ keys7Chunk13,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk13, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_416, canonicalSolid7_416⟩
  · exact ⟨canonicalPose7_417, canonicalSolid7_417⟩
  · exact ⟨canonicalPose7_418, canonicalSolid7_418⟩
  · exact ⟨canonicalPose7_419, canonicalSolid7_419⟩
  · exact ⟨canonicalPose7_420, canonicalSolid7_420⟩
  · exact ⟨canonicalPose7_421, canonicalSolid7_421⟩
  · exact ⟨canonicalPose7_422, canonicalSolid7_422⟩
  · exact ⟨canonicalPose7_423, canonicalSolid7_423⟩
  · exact ⟨canonicalPose7_424, canonicalSolid7_424⟩
  · exact ⟨canonicalPose7_425, canonicalSolid7_425⟩
  · exact ⟨canonicalPose7_426, canonicalSolid7_426⟩
  · exact ⟨canonicalPose7_427, canonicalSolid7_427⟩
  · exact ⟨canonicalPose7_428, canonicalSolid7_428⟩
  · exact ⟨canonicalPose7_429, canonicalSolid7_429⟩
  · exact ⟨canonicalPose7_430, canonicalSolid7_430⟩
  · exact ⟨canonicalPose7_431, canonicalSolid7_431⟩
  · exact ⟨canonicalPose7_432, canonicalSolid7_432⟩
  · exact ⟨canonicalPose7_433, canonicalSolid7_433⟩
  · exact ⟨canonicalPose7_434, canonicalSolid7_434⟩
  · exact ⟨canonicalPose7_435, canonicalSolid7_435⟩
  · exact ⟨canonicalPose7_436, canonicalSolid7_436⟩
  · exact ⟨canonicalPose7_437, canonicalSolid7_437⟩
  · exact ⟨canonicalPose7_438, canonicalSolid7_438⟩
  · exact ⟨canonicalPose7_439, canonicalSolid7_439⟩
  · exact ⟨canonicalPose7_440, canonicalSolid7_440⟩
  · exact ⟨canonicalPose7_441, canonicalSolid7_441⟩
  · exact ⟨canonicalPose7_442, canonicalSolid7_442⟩
  · exact ⟨canonicalPose7_443, canonicalSolid7_443⟩
  · exact ⟨canonicalPose7_444, canonicalSolid7_444⟩
  · exact ⟨canonicalPose7_445, canonicalSolid7_445⟩
  · exact ⟨canonicalPose7_446, canonicalSolid7_446⟩
  · exact ⟨canonicalPose7_447, canonicalSolid7_447⟩

#print axioms keys7Chunk13_canonical

end SparseMonotiles.Canonical
