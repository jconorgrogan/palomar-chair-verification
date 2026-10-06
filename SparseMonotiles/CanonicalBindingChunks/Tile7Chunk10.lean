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

def canonicalPose7_320 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, true, true, false, false, false], ![0, 2, 1, 2, 0, 0, 0]⟩
def canonicalBox7_320 : BoxKey 7 :=
  ⟨![0, 255360, 60480, 241920, 100800, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 254940, 60080, 241535, 101360, 108010, 114688], false⟩

theorem canonicalMatch7_320 :
    canonicalPose7_320.boxKey 188160 (referenceBox7 (!canonicalBox7_320.bump)) = canonicalBox7_320 := by decide +kernel

theorem canonicalDecode7_320 : canonicalBox7_320.toKeyData 188160 = keys7Chunk10.get ⟨0, by decide⟩ := by
  change canonicalBox7_320.toKeyData 188160 = ⟨![0, (19 / 14), (9 / 28), (9 / 7), (15 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_320 : keySolid (keys7Chunk10.get ⟨0, by decide⟩) = canonicalPose7_320.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_320 (box := canonicalBox7_320) (k := keys7Chunk10.get ⟨0, by decide⟩) (canonicalMatch7_320) (canonicalDecode7_320)

def canonicalPose7_321 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, false, true, false, true, true], ![0, 2, 0, 2, 0, 1, 1]⟩
def canonicalBox7_321 : BoxKey 7 :=
  ⟨![120960, 376320, 114240, 268800, 100800, 53760, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 375760, 114688, 268310, 101360, 53375, 60080], false⟩

theorem canonicalMatch7_321 :
    canonicalPose7_321.boxKey 188160 (referenceBox7 (!canonicalBox7_321.bump)) = canonicalBox7_321 := by decide +kernel

theorem canonicalDecode7_321 : canonicalBox7_321.toKeyData 188160 = keys7Chunk10.get ⟨1, by decide⟩ := by
  change canonicalBox7_321.toKeyData 188160 = ⟨![(9 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (2 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_321 : keySolid (keys7Chunk10.get ⟨1, by decide⟩) = canonicalPose7_321.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_321 (box := canonicalBox7_321) (k := keys7Chunk10.get ⟨1, by decide⟩) (canonicalMatch7_321) (canonicalDecode7_321)

def canonicalPose7_322 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, false, false, false, false], ![0, 1, 0, 1, 0, 0, 0]⟩
def canonicalBox7_322 : BoxKey 7 :=
  ⟨![107520, 302400, 0, 309120, 127680, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 302848, -560, 309540, 128080, 134785, 101360], true⟩

theorem canonicalMatch7_322 :
    canonicalPose7_322.boxKey 188160 (referenceBox7 (!canonicalBox7_322.bump)) = canonicalBox7_322 := by decide +kernel

theorem canonicalDecode7_322 : canonicalBox7_322.toKeyData 188160 = keys7Chunk10.get ⟨2, by decide⟩ := by
  change canonicalBox7_322.toKeyData 188160 = ⟨![(4 / 7), (45 / 28), 0, (23 / 14), (19 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (169 / 105), (-1 / 336), (737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_322 : keySolid (keys7Chunk10.get ⟨2, by decide⟩) = canonicalPose7_322.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_322 (box := canonicalBox7_322) (k := keys7Chunk10.get ⟨2, by decide⟩) (canonicalMatch7_322) (canonicalDecode7_322)

def canonicalPose7_323 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, false, false, false, false], ![0, 1, 0, 1, 0, 0, 0]⟩
def canonicalBox7_323 : BoxKey 7 :=
  ⟨![127680, 309120, 0, 302400, 107520, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 309540, 560, 302848, 108010, 101360, 134785], false⟩

theorem canonicalMatch7_323 :
    canonicalPose7_323.boxKey 188160 (referenceBox7 (!canonicalBox7_323.bump)) = canonicalBox7_323 := by decide +kernel

theorem canonicalDecode7_323 : canonicalBox7_323.toKeyData 188160 = keys7Chunk10.get ⟨3, by decide⟩ := by
  change canonicalBox7_323.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), 0, (45 / 28), (4 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (1 / 336), (169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_323 : keySolid (keys7Chunk10.get ⟨3, by decide⟩) = canonicalPose7_323.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_323 (box := canonicalBox7_323) (k := keys7Chunk10.get ⟨3, by decide⟩) (canonicalMatch7_323) (canonicalDecode7_323)

def canonicalPose7_324 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, false, false, true, true], ![0, 2, 0, 2, 0, 1, 1]⟩
def canonicalBox7_324 : BoxKey 7 :=
  ⟨![100800, 268800, 114240, 376320, 120960, 60480, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 114688, 376880, 121380, 60080, 53375], true⟩

theorem canonicalMatch7_324 :
    canonicalPose7_324.boxKey 188160 (referenceBox7 (!canonicalBox7_324.bump)) = canonicalBox7_324 := by decide +kernel

theorem canonicalDecode7_324 : canonicalBox7_324.toKeyData 188160 = keys7Chunk10.get ⟨4, by decide⟩ := by
  change canonicalBox7_324.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (17 / 28), 2, (9 / 14), (9 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (289 / 448), (751 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_324 : keySolid (keys7Chunk10.get ⟨4, by decide⟩) = canonicalPose7_324.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_324 (box := canonicalBox7_324) (k := keys7Chunk10.get ⟨4, by decide⟩) (canonicalMatch7_324) (canonicalDecode7_324)

def canonicalPose7_325 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, true, true, true, false, false], ![0, 2, 1, 2, 0, 0, 0]⟩
def canonicalBox7_325 : BoxKey 7 :=
  ⟨![100800, 241920, 60480, 255360, 0, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 241535, 60080, 254940, -560, 114688, 108010], true⟩

theorem canonicalMatch7_325 :
    canonicalPose7_325.boxKey 188160 (referenceBox7 (!canonicalBox7_325.bump)) = canonicalBox7_325 := by decide +kernel

theorem canonicalDecode7_325 : canonicalBox7_325.toKeyData 188160 = keys7Chunk10.get ⟨5, by decide⟩ := by
  change canonicalBox7_325.toKeyData 188160 = ⟨![(15 / 28), (9 / 7), (9 / 28), (19 / 14), 0, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (64 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_325 : keySolid (keys7Chunk10.get ⟨5, by decide⟩) = canonicalPose7_325.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_325 (box := canonicalBox7_325) (k := keys7Chunk10.get ⟨5, by decide⟩) (canonicalMatch7_325) (canonicalDecode7_325)

def canonicalPose7_326 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, false, false, false, false, false, false], ![0, 1, 0, 1, 0, 0, 0]⟩
def canonicalBox7_326 : BoxKey 7 :=
  ⟨![100800, 322560, 127680, 309120, 114240, 0, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 322945, 128080, 309540, 114688, 560, 108010], false⟩

theorem canonicalMatch7_326 :
    canonicalPose7_326.boxKey 188160 (referenceBox7 (!canonicalBox7_326.bump)) = canonicalBox7_326 := by decide +kernel

theorem canonicalDecode7_326 : canonicalBox7_326.toKeyData 188160 = keys7Chunk10.get ⟨6, by decide⟩ := by
  change canonicalBox7_326.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (19 / 28), (23 / 14), (17 / 28), 0, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105), (1 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_326 : keySolid (keys7Chunk10.get ⟨6, by decide⟩) = canonicalPose7_326.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_326 (box := canonicalBox7_326) (k := keys7Chunk10.get ⟨6, by decide⟩) (canonicalMatch7_326) (canonicalDecode7_326)

def canonicalPose7_327 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, false, false, false, false, false, true], ![0, 1, 0, 1, 0, 0, 0]⟩
def canonicalBox7_327 : BoxKey 7 :=
  ⟨![114240, 309120, 127680, 322560, 100800, 107520, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 309540, 128080, 322945, 101360, 108010, -560], true⟩

theorem canonicalMatch7_327 :
    canonicalPose7_327.boxKey 188160 (referenceBox7 (!canonicalBox7_327.bump)) = canonicalBox7_327 := by decide +kernel

theorem canonicalDecode7_327 : canonicalBox7_327.toKeyData 188160 = keys7Chunk10.get ⟨7, by decide⟩ := by
  change canonicalBox7_327.toKeyData 188160 = ⟨![(17 / 28), (23 / 14), (19 / 28), (12 / 7), (15 / 28), (4 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_327 : keySolid (keys7Chunk10.get ⟨7, by decide⟩) = canonicalPose7_327.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_327 (box := canonicalBox7_327) (k := keys7Chunk10.get ⟨7, by decide⟩) (canonicalMatch7_327) (canonicalDecode7_327)

def canonicalPose7_328 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, true, true, true, true], ![0, 2, 0, 2, 1, 1, 2]⟩
def canonicalBox7_328 : BoxKey 7 :=
  ⟨![0, 262080, 107520, 275520, 53760, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 261632, 108010, 274960, 53375, 60080, 254940], true⟩

theorem canonicalMatch7_328 :
    canonicalPose7_328.boxKey 188160 (referenceBox7 (!canonicalBox7_328.bump)) = canonicalBox7_328 := by decide +kernel

theorem canonicalDecode7_328 : canonicalBox7_328.toKeyData 188160 = keys7Chunk10.get ⟨8, by decide⟩ := by
  change canonicalBox7_328.toKeyData 188160 = ⟨![0, (39 / 28), (4 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_328 : keySolid (keys7Chunk10.get ⟨8, by decide⟩) = canonicalPose7_328.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_328 (box := canonicalBox7_328) (k := keys7Chunk10.get ⟨8, by decide⟩) (canonicalMatch7_328) (canonicalDecode7_328)

def canonicalPose7_329 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, true, false, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_329 : BoxKey 7 :=
  ⟨![73920, 376320, 67200, 248640, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, 375760, 66780, 248240, 134785, 101360, 268310], false⟩

theorem canonicalMatch7_329 :
    canonicalPose7_329.boxKey 188160 (referenceBox7 (!canonicalBox7_329.bump)) = canonicalBox7_329 := by decide +kernel

theorem canonicalDecode7_329 : canonicalBox7_329.toKeyData 188160 = keys7Chunk10.get ⟨9, by decide⟩ := by
  change canonicalBox7_329.toKeyData 188160 = ⟨![(11 / 28), 2, (5 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (671 / 336), (159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_329 : keySolid (keys7Chunk10.get ⟨9, by decide⟩) = canonicalPose7_329.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_329 (box := canonicalBox7_329) (k := keys7Chunk10.get ⟨9, by decide⟩) (canonicalMatch7_329) (canonicalDecode7_329)

def canonicalPose7_330 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, true, false, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_330 : BoxKey 7 :=
  ⟨![67200, 376320, 73920, 268800, 100800, 134400, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 376880, 73472, 268310, 101360, 134785, 248240], true⟩

theorem canonicalMatch7_330 :
    canonicalPose7_330.boxKey 188160 (referenceBox7 (!canonicalBox7_330.bump)) = canonicalBox7_330 := by decide +kernel

theorem canonicalDecode7_330 : canonicalBox7_330.toKeyData 188160 = keys7Chunk10.get ⟨10, by decide⟩ := by
  change canonicalBox7_330.toKeyData 188160 = ⟨![(5 / 14), 2, (11 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (673 / 336), (41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_330 : keySolid (keys7Chunk10.get ⟨10, by decide⟩) = canonicalPose7_330.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_330 (box := canonicalBox7_330) (k := keys7Chunk10.get ⟨10, by decide⟩) (canonicalMatch7_330) (canonicalDecode7_330)

def canonicalPose7_331 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, true, true, true, true], ![0, 2, 0, 2, 1, 1, 2]⟩
def canonicalBox7_331 : BoxKey 7 :=
  ⟨![107520, 262080, 0, 255360, 60480, 53760, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 261632, 560, 254940, 60080, 53375, 274960], false⟩

theorem canonicalMatch7_331 :
    canonicalPose7_331.boxKey 188160 (referenceBox7 (!canonicalBox7_331.bump)) = canonicalBox7_331 := by decide +kernel

theorem canonicalDecode7_331 : canonicalBox7_331.toKeyData 188160 = keys7Chunk10.get ⟨11, by decide⟩ := by
  change canonicalBox7_331.toKeyData 188160 = ⟨![(4 / 7), (39 / 28), 0, (19 / 14), (9 / 28), (2 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (146 / 105), (1 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_331 : keySolid (keys7Chunk10.get ⟨11, by decide⟩) = canonicalPose7_331.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_331 (box := canonicalBox7_331) (k := keys7Chunk10.get ⟨11, by decide⟩) (canonicalMatch7_331) (canonicalDecode7_331)

def canonicalPose7_332 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, true, false, false, true], ![0, 1, 0, 2, 0, 0, 2]⟩
def canonicalBox7_332 : BoxKey 7 :=
  ⟨![134400, 315840, 120960, 376320, 114240, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 316240, 121380, 375760, 114688, 108010, 274960], false⟩

theorem canonicalMatch7_332 :
    canonicalPose7_332.boxKey 188160 (referenceBox7 (!canonicalBox7_332.bump)) = canonicalBox7_332 := by decide +kernel

theorem canonicalDecode7_332 : canonicalBox7_332.toKeyData 188160 = keys7Chunk10.get ⟨12, by decide⟩ := by
  change canonicalBox7_332.toKeyData 188160 = ⟨![(5 / 7), (47 / 28), (9 / 14), 2, (17 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (64 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_332 : keySolid (keys7Chunk10.get ⟨12, by decide⟩) = canonicalPose7_332.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_332 (box := canonicalBox7_332) (k := keys7Chunk10.get ⟨12, by decide⟩) (canonicalMatch7_332) (canonicalDecode7_332)

def canonicalPose7_333 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, true, true, true, true, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_333 : BoxKey 7 :=
  ⟨![53760, 248640, 67200, 262080, 0, 107520, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 248240, 66780, 261632, -560, 108010, 274960], true⟩

theorem canonicalMatch7_333 :
    canonicalPose7_333.boxKey 188160 (referenceBox7 (!canonicalBox7_333.bump)) = canonicalBox7_333 := by decide +kernel

theorem canonicalDecode7_333 : canonicalBox7_333.toKeyData 188160 = keys7Chunk10.get ⟨13, by decide⟩ := by
  change canonicalBox7_333.toKeyData 188160 = ⟨![(2 / 7), (37 / 28), (5 / 14), (39 / 28), 0, (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105), (-1 / 336), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_333 : keySolid (keys7Chunk10.get ⟨13, by decide⟩) = canonicalPose7_333.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_333 (box := canonicalBox7_333) (k := keys7Chunk10.get ⟨13, by decide⟩) (canonicalMatch7_333) (canonicalDecode7_333)

def canonicalPose7_334 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, true, true, true, false, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_334 : BoxKey 7 :=
  ⟨![67200, 248640, 53760, 275520, 107520, 0, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 248240, 53375, 274960, 108010, 560, 261632], false⟩

theorem canonicalMatch7_334 :
    canonicalPose7_334.boxKey 188160 (referenceBox7 (!canonicalBox7_334.bump)) = canonicalBox7_334 := by decide +kernel

theorem canonicalDecode7_334 : canonicalBox7_334.toKeyData 188160 = keys7Chunk10.get ⟨14, by decide⟩ := by
  change canonicalBox7_334.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (2 / 7), (41 / 28), (4 / 7), 0, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (1 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_334 : keySolid (keys7Chunk10.get ⟨14, by decide⟩) = canonicalPose7_334.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_334 (box := canonicalBox7_334) (k := keys7Chunk10.get ⟨14, by decide⟩) (canonicalMatch7_334) (canonicalDecode7_334)

def canonicalPose7_335 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, true, false, false, false], ![0, 1, 0, 2, 0, 0, 2]⟩
def canonicalBox7_335 : BoxKey 7 :=
  ⟨![120960, 315840, 134400, 275520, 107520, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 134785, 274960, 108010, 114688, 376880], true⟩

theorem canonicalMatch7_335 :
    canonicalPose7_335.boxKey 188160 (referenceBox7 (!canonicalBox7_335.bump)) = canonicalBox7_335 := by decide +kernel

theorem canonicalDecode7_335 : canonicalBox7_335.toKeyData 188160 = keys7Chunk10.get ⟨15, by decide⟩ := by
  change canonicalBox7_335.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (5 / 7), (41 / 28), (4 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_335 : keySolid (keys7Chunk10.get ⟨15, by decide⟩) = canonicalPose7_335.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_335 (box := canonicalBox7_335) (k := keys7Chunk10.get ⟨15, by decide⟩) (canonicalMatch7_335) (canonicalDecode7_335)

def canonicalPose7_336 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, true, true, true, true, true, false], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_336 : BoxKey 7 :=
  ⟨![0, 262080, 67200, 248640, 53760, 275520, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![560, 261632, 66780, 248240, 53375, 274960, 108010], false⟩

theorem canonicalMatch7_336 :
    canonicalPose7_336.boxKey 188160 (referenceBox7 (!canonicalBox7_336.bump)) = canonicalBox7_336 := by decide +kernel

theorem canonicalDecode7_336 : canonicalBox7_336.toKeyData 188160 = keys7Chunk10.get ⟨16, by decide⟩ := by
  change canonicalBox7_336.toKeyData 188160 = ⟨![0, (39 / 28), (5 / 14), (37 / 28), (2 / 7), (41 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(1 / 336), (146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_336 : keySolid (keys7Chunk10.get ⟨16, by decide⟩) = canonicalPose7_336.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_336 (box := canonicalBox7_336) (k := keys7Chunk10.get ⟨16, by decide⟩) (canonicalMatch7_336) (canonicalDecode7_336)

def canonicalPose7_337 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, false, false, false, true, false], ![0, 2, 0, 1, 0, 2, 0]⟩
def canonicalBox7_337 : BoxKey 7 :=
  ⟨![114240, 376320, 120960, 315840, 134400, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 376880, 121380, 316240, 134785, 274960, 108010], true⟩

theorem canonicalMatch7_337 :
    canonicalPose7_337.boxKey 188160 (referenceBox7 (!canonicalBox7_337.bump)) = canonicalBox7_337 := by decide +kernel

theorem canonicalDecode7_337 : canonicalBox7_337.toKeyData 188160 = keys7Chunk10.get ⟨17, by decide⟩ := by
  change canonicalBox7_337.toKeyData 188160 = ⟨![(17 / 28), 2, (9 / 14), (47 / 28), (5 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_337 : keySolid (keys7Chunk10.get ⟨17, by decide⟩) = canonicalPose7_337.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_337 (box := canonicalBox7_337) (k := keys7Chunk10.get ⟨17, by decide⟩) (canonicalMatch7_337) (canonicalDecode7_337)

def canonicalPose7_338 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, true, true, false, true, true], ![1, 2, 0, 2, 0, 2, 1]⟩
def canonicalBox7_338 : BoxKey 7 :=
  ⟨![60480, 255360, 0, 262080, 107520, 275520, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, -560, 261632, 108010, 274960, 53375], true⟩

theorem canonicalMatch7_338 :
    canonicalPose7_338.boxKey 188160 (referenceBox7 (!canonicalBox7_338.bump)) = canonicalBox7_338 := by decide +kernel

theorem canonicalDecode7_338 : canonicalBox7_338.toKeyData 188160 = keys7Chunk10.get ⟨18, by decide⟩ := by
  change canonicalBox7_338.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_338 : keySolid (keys7Chunk10.get ⟨18, by decide⟩) = canonicalPose7_338.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_338 (box := canonicalBox7_338) (k := keys7Chunk10.get ⟨18, by decide⟩) (canonicalMatch7_338) (canonicalDecode7_338)

def canonicalPose7_339 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, true, true, true, false], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_339 : BoxKey 7 :=
  ⟨![100800, 268800, 73920, 376320, 67200, 248640, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 73472, 375760, 66780, 248240, 134785], false⟩

theorem canonicalMatch7_339 :
    canonicalPose7_339.boxKey 188160 (referenceBox7 (!canonicalBox7_339.bump)) = canonicalBox7_339 := by decide +kernel

theorem canonicalDecode7_339 : canonicalBox7_339.toKeyData 188160 = keys7Chunk10.get ⟨19, by decide⟩ := by
  change canonicalBox7_339.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (11 / 28), 2, (5 / 14), (37 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (41 / 105), (671 / 336), (159 / 448), (3103 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_339 : keySolid (keys7Chunk10.get ⟨19, by decide⟩) = canonicalPose7_339.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_339 (box := canonicalBox7_339) (k := keys7Chunk10.get ⟨19, by decide⟩) (canonicalMatch7_339) (canonicalDecode7_339)

def canonicalPose7_340 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, true, false, true, true, false], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_340 : BoxKey 7 :=
  ⟨![134400, 248640, 67200, 376320, 73920, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 248240, 66780, 376880, 73472, 268310, 101360], true⟩

theorem canonicalMatch7_340 :
    canonicalPose7_340.boxKey 188160 (referenceBox7 (!canonicalBox7_340.bump)) = canonicalBox7_340 := by decide +kernel

theorem canonicalDecode7_340 : canonicalBox7_340.toKeyData 188160 = keys7Chunk10.get ⟨20, by decide⟩ := by
  change canonicalBox7_340.toKeyData 188160 = ⟨![(5 / 7), (37 / 28), (5 / 14), 2, (11 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3103 / 2352), (159 / 448), (673 / 336), (41 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_340 : keySolid (keys7Chunk10.get ⟨20, by decide⟩) = canonicalPose7_340.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_340 (box := canonicalBox7_340) (k := keys7Chunk10.get ⟨20, by decide⟩) (canonicalMatch7_340) (canonicalDecode7_340)

def canonicalPose7_341 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, true, false, true, true], ![1, 2, 0, 2, 0, 2, 1]⟩
def canonicalBox7_341 : BoxKey 7 :=
  ⟨![53760, 275520, 107520, 262080, 0, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 274960, 108010, 261632, 560, 254940, 60080], false⟩

theorem canonicalMatch7_341 :
    canonicalPose7_341.boxKey 188160 (referenceBox7 (!canonicalBox7_341.bump)) = canonicalBox7_341 := by decide +kernel

theorem canonicalDecode7_341 : canonicalBox7_341.toKeyData 188160 = keys7Chunk10.get ⟨21, by decide⟩ := by
  change canonicalBox7_341.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (607 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_341 : keySolid (keys7Chunk10.get ⟨21, by decide⟩) = canonicalPose7_341.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_341 (box := canonicalBox7_341) (k := keys7Chunk10.get ⟨21, by decide⟩) (canonicalMatch7_341) (canonicalDecode7_341)

def canonicalPose7_342 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, false, false, false, true, false], ![0, 2, 0, 1, 0, 2, 0]⟩
def canonicalBox7_342 : BoxKey 7 :=
  ⟨![107520, 275520, 134400, 315840, 120960, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 134785, 316240, 121380, 375760, 114688], false⟩

theorem canonicalMatch7_342 :
    canonicalPose7_342.boxKey 188160 (referenceBox7 (!canonicalBox7_342.bump)) = canonicalBox7_342 := by decide +kernel

theorem canonicalDecode7_342 : canonicalBox7_342.toKeyData 188160 = keys7Chunk10.get ⟨22, by decide⟩ := by
  change canonicalBox7_342.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (5 / 7), (47 / 28), (9 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_342 : keySolid (keys7Chunk10.get ⟨22, by decide⟩) = canonicalPose7_342.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_342 (box := canonicalBox7_342) (k := keys7Chunk10.get ⟨22, by decide⟩) (canonicalMatch7_342) (canonicalDecode7_342)

def canonicalPose7_343 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, true, true, true, true, true, true], ![0, 2, 1, 2, 1, 2, 0]⟩
def canonicalBox7_343 : BoxKey 7 :=
  ⟨![107520, 275520, 53760, 248640, 67200, 262080, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 274960, 53375, 248240, 66780, 261632, -560], true⟩

theorem canonicalMatch7_343 :
    canonicalPose7_343.boxKey 188160 (referenceBox7 (!canonicalBox7_343.bump)) = canonicalBox7_343 := by decide +kernel

theorem canonicalDecode7_343 : canonicalBox7_343.toKeyData 188160 = keys7Chunk10.get ⟨23, by decide⟩ := by
  change canonicalBox7_343.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (2 / 7), (37 / 28), (5 / 14), (39 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_343 : keySolid (keys7Chunk10.get ⟨23, by decide⟩) = canonicalPose7_343.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_343 (box := canonicalBox7_343) (k := keys7Chunk10.get ⟨23, by decide⟩) (canonicalMatch7_343) (canonicalDecode7_343)

def canonicalPose7_344 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, true, true, false, true, true], ![0, 2, 1, 2, 0, 2, 2]⟩
def canonicalBox7_344 : BoxKey 7 :=
  ⟨![0, 255360, 60480, 241920, 100800, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 254940, 60080, 241535, 101360, 268310, 261632], false⟩

theorem canonicalMatch7_344 :
    canonicalPose7_344.boxKey 188160 (referenceBox7 (!canonicalBox7_344.bump)) = canonicalBox7_344 := by decide +kernel

theorem canonicalDecode7_344 : canonicalBox7_344.toKeyData 188160 = keys7Chunk10.get ⟨24, by decide⟩ := by
  change canonicalBox7_344.toKeyData 188160 = ⟨![0, (19 / 14), (9 / 28), (9 / 7), (15 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_344 : keySolid (keys7Chunk10.get ⟨24, by decide⟩) = canonicalPose7_344.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_344 (box := canonicalBox7_344) (k := keys7Chunk10.get ⟨24, by decide⟩) (canonicalMatch7_344) (canonicalDecode7_344)

def canonicalPose7_345 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, false, true, false, false, false], ![0, 2, 0, 2, 0, 1, 1]⟩
def canonicalBox7_345 : BoxKey 7 :=
  ⟨![120960, 376320, 114240, 268800, 100800, 322560, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 375760, 114688, 268310, 101360, 322945, 316240], false⟩

theorem canonicalMatch7_345 :
    canonicalPose7_345.boxKey 188160 (referenceBox7 (!canonicalBox7_345.bump)) = canonicalBox7_345 := by decide +kernel

theorem canonicalDecode7_345 : canonicalBox7_345.toKeyData 188160 = keys7Chunk10.get ⟨25, by decide⟩ := by
  change canonicalBox7_345.toKeyData 188160 = ⟨![(9 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (12 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_345 : keySolid (keys7Chunk10.get ⟨25, by decide⟩) = canonicalPose7_345.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_345 (box := canonicalBox7_345) (k := keys7Chunk10.get ⟨25, by decide⟩) (canonicalMatch7_345) (canonicalDecode7_345)

def canonicalPose7_346 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, false, false, true, true], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_346 : BoxKey 7 :=
  ⟨![107520, 302400, 0, 309120, 127680, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 302848, -560, 309540, 128080, 241535, 274960], true⟩

theorem canonicalMatch7_346 :
    canonicalPose7_346.boxKey 188160 (referenceBox7 (!canonicalBox7_346.bump)) = canonicalBox7_346 := by decide +kernel

theorem canonicalDecode7_346 : canonicalBox7_346.toKeyData 188160 = keys7Chunk10.get ⟨26, by decide⟩ := by
  change canonicalBox7_346.toKeyData 188160 = ⟨![(4 / 7), (45 / 28), 0, (23 / 14), (19 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (169 / 105), (-1 / 336), (737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_346 : keySolid (keys7Chunk10.get ⟨26, by decide⟩) = canonicalPose7_346.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_346 (box := canonicalBox7_346) (k := keys7Chunk10.get ⟨26, by decide⟩) (canonicalMatch7_346) (canonicalDecode7_346)

def canonicalPose7_347 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, false, false, true, true], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_347 : BoxKey 7 :=
  ⟨![127680, 309120, 0, 302400, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 309540, 560, 302848, 108010, 274960, 241535], false⟩

theorem canonicalMatch7_347 :
    canonicalPose7_347.boxKey 188160 (referenceBox7 (!canonicalBox7_347.bump)) = canonicalBox7_347 := by decide +kernel

theorem canonicalDecode7_347 : canonicalBox7_347.toKeyData 188160 = keys7Chunk10.get ⟨27, by decide⟩ := by
  change canonicalBox7_347.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), 0, (45 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (1 / 336), (169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_347 : keySolid (keys7Chunk10.get ⟨27, by decide⟩) = canonicalPose7_347.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_347 (box := canonicalBox7_347) (k := keys7Chunk10.get ⟨27, by decide⟩) (canonicalMatch7_347) (canonicalDecode7_347)

def canonicalPose7_348 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, false, false, false, false], ![0, 2, 0, 2, 0, 1, 1]⟩
def canonicalBox7_348 : BoxKey 7 :=
  ⟨![100800, 268800, 114240, 376320, 120960, 315840, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 114688, 376880, 121380, 316240, 322945], true⟩

theorem canonicalMatch7_348 :
    canonicalPose7_348.boxKey 188160 (referenceBox7 (!canonicalBox7_348.bump)) = canonicalBox7_348 := by decide +kernel

theorem canonicalDecode7_348 : canonicalBox7_348.toKeyData 188160 = keys7Chunk10.get ⟨28, by decide⟩ := by
  change canonicalBox7_348.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (17 / 28), 2, (9 / 14), (47 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (289 / 448), (3953 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_348 : keySolid (keys7Chunk10.get ⟨28, by decide⟩) = canonicalPose7_348.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_348 (box := canonicalBox7_348) (k := keys7Chunk10.get ⟨28, by decide⟩) (canonicalMatch7_348) (canonicalDecode7_348)

def canonicalPose7_349 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, true, true, true, true, true], ![0, 2, 1, 2, 0, 2, 2]⟩
def canonicalBox7_349 : BoxKey 7 :=
  ⟨![100800, 241920, 60480, 255360, 0, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 241535, 60080, 254940, -560, 261632, 268310], true⟩

theorem canonicalMatch7_349 :
    canonicalPose7_349.boxKey 188160 (referenceBox7 (!canonicalBox7_349.bump)) = canonicalBox7_349 := by decide +kernel

theorem canonicalDecode7_349 : canonicalBox7_349.toKeyData 188160 = keys7Chunk10.get ⟨29, by decide⟩ := by
  change canonicalBox7_349.toKeyData 188160 = ⟨![(15 / 28), (9 / 7), (9 / 28), (19 / 14), 0, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (146 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_349 : keySolid (keys7Chunk10.get ⟨29, by decide⟩) = canonicalPose7_349.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_349 (box := canonicalBox7_349) (k := keys7Chunk10.get ⟨29, by decide⟩) (canonicalMatch7_349) (canonicalDecode7_349)

def canonicalPose7_350 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, false, false, false, false, true, true], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_350 : BoxKey 7 :=
  ⟨![100800, 322560, 127680, 309120, 114240, 376320, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 322945, 128080, 309540, 114688, 375760, 268310], false⟩

theorem canonicalMatch7_350 :
    canonicalPose7_350.boxKey 188160 (referenceBox7 (!canonicalBox7_350.bump)) = canonicalBox7_350 := by decide +kernel

theorem canonicalDecode7_350 : canonicalBox7_350.toKeyData 188160 = keys7Chunk10.get ⟨30, by decide⟩ := by
  change canonicalBox7_350.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (19 / 28), (23 / 14), (17 / 28), 2, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105), (671 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_350 : keySolid (keys7Chunk10.get ⟨30, by decide⟩) = canonicalPose7_350.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_350 (box := canonicalBox7_350) (k := keys7Chunk10.get ⟨30, by decide⟩) (canonicalMatch7_350) (canonicalDecode7_350)

def canonicalPose7_351 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, false, false, false, false, true, false], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_351 : BoxKey 7 :=
  ⟨![114240, 309120, 127680, 322560, 100800, 268800, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 309540, 128080, 322945, 101360, 268310, 376880], true⟩

theorem canonicalMatch7_351 :
    canonicalPose7_351.boxKey 188160 (referenceBox7 (!canonicalBox7_351.bump)) = canonicalBox7_351 := by decide +kernel

theorem canonicalDecode7_351 : canonicalBox7_351.toKeyData 188160 = keys7Chunk10.get ⟨31, by decide⟩ := by
  change canonicalBox7_351.toKeyData 188160 = ⟨![(17 / 28), (23 / 14), (19 / 28), (12 / 7), (15 / 28), (10 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_351 : keySolid (keys7Chunk10.get ⟨31, by decide⟩) = canonicalPose7_351.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_351 (box := canonicalBox7_351) (k := keys7Chunk10.get ⟨31, by decide⟩) (canonicalMatch7_351) (canonicalDecode7_351)

theorem keys7Chunk10_canonical : ∀ k ∈ keys7Chunk10,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk10, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_320, canonicalSolid7_320⟩
  · exact ⟨canonicalPose7_321, canonicalSolid7_321⟩
  · exact ⟨canonicalPose7_322, canonicalSolid7_322⟩
  · exact ⟨canonicalPose7_323, canonicalSolid7_323⟩
  · exact ⟨canonicalPose7_324, canonicalSolid7_324⟩
  · exact ⟨canonicalPose7_325, canonicalSolid7_325⟩
  · exact ⟨canonicalPose7_326, canonicalSolid7_326⟩
  · exact ⟨canonicalPose7_327, canonicalSolid7_327⟩
  · exact ⟨canonicalPose7_328, canonicalSolid7_328⟩
  · exact ⟨canonicalPose7_329, canonicalSolid7_329⟩
  · exact ⟨canonicalPose7_330, canonicalSolid7_330⟩
  · exact ⟨canonicalPose7_331, canonicalSolid7_331⟩
  · exact ⟨canonicalPose7_332, canonicalSolid7_332⟩
  · exact ⟨canonicalPose7_333, canonicalSolid7_333⟩
  · exact ⟨canonicalPose7_334, canonicalSolid7_334⟩
  · exact ⟨canonicalPose7_335, canonicalSolid7_335⟩
  · exact ⟨canonicalPose7_336, canonicalSolid7_336⟩
  · exact ⟨canonicalPose7_337, canonicalSolid7_337⟩
  · exact ⟨canonicalPose7_338, canonicalSolid7_338⟩
  · exact ⟨canonicalPose7_339, canonicalSolid7_339⟩
  · exact ⟨canonicalPose7_340, canonicalSolid7_340⟩
  · exact ⟨canonicalPose7_341, canonicalSolid7_341⟩
  · exact ⟨canonicalPose7_342, canonicalSolid7_342⟩
  · exact ⟨canonicalPose7_343, canonicalSolid7_343⟩
  · exact ⟨canonicalPose7_344, canonicalSolid7_344⟩
  · exact ⟨canonicalPose7_345, canonicalSolid7_345⟩
  · exact ⟨canonicalPose7_346, canonicalSolid7_346⟩
  · exact ⟨canonicalPose7_347, canonicalSolid7_347⟩
  · exact ⟨canonicalPose7_348, canonicalSolid7_348⟩
  · exact ⟨canonicalPose7_349, canonicalSolid7_349⟩
  · exact ⟨canonicalPose7_350, canonicalSolid7_350⟩
  · exact ⟨canonicalPose7_351, canonicalSolid7_351⟩

#print axioms keys7Chunk10_canonical

end SparseMonotiles.Canonical
