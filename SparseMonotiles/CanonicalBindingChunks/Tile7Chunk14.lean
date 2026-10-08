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

def canonicalPose7_448 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, true, false, false, false], ![0, 2, 1, 2, 0, 0, 0]⟩
def canonicalBox7_448 : BoxKey 7 :=
  ⟨![0, 255360, 315840, 241920, 100800, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 254940, 316240, 241535, 101360, 108010, 114688], true⟩

theorem canonicalMatch7_448 :
    canonicalPose7_448.boxKey 188160 (referenceBox7 (!canonicalBox7_448.bump)) = canonicalBox7_448 := by decide +kernel

theorem canonicalDecode7_448 : canonicalBox7_448.toKeyData 188160 = keys7Chunk14.get ⟨0, by decide⟩ := by
  change canonicalBox7_448.toKeyData 188160 = ⟨![0, (19 / 14), (47 / 28), (9 / 7), (15 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_448 : keySolid (keys7Chunk14.get ⟨0, by decide⟩) = canonicalPose7_448.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_448 (box := canonicalBox7_448) (k := keys7Chunk14.get ⟨0, by decide⟩) (canonicalMatch7_448) (canonicalDecode7_448)

def canonicalPose7_449 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, true, true, false, true, true], ![0, 2, 2, 2, 0, 1, 1]⟩
def canonicalBox7_449 : BoxKey 7 :=
  ⟨![120960, 376320, 262080, 268800, 100800, 53760, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 376880, 261632, 268310, 101360, 53375, 60080], true⟩

theorem canonicalMatch7_449 :
    canonicalPose7_449.boxKey 188160 (referenceBox7 (!canonicalBox7_449.bump)) = canonicalBox7_449 := by decide +kernel

theorem canonicalDecode7_449 : canonicalBox7_449.toKeyData 188160 = keys7Chunk14.get ⟨1, by decide⟩ := by
  change canonicalBox7_449.toKeyData 188160 = ⟨![(9 / 14), 2, (39 / 28), (10 / 7), (15 / 28), (2 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_449 : keySolid (keys7Chunk14.get ⟨1, by decide⟩) = canonicalPose7_449.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_449 (box := canonicalBox7_449) (k := keys7Chunk14.get ⟨1, by decide⟩) (canonicalMatch7_449) (canonicalDecode7_449)

def canonicalPose7_450 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, false, false, false, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_450 : BoxKey 7 :=
  ⟨![107520, 302400, 376320, 309120, 127680, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 302848, 375760, 309540, 128080, 134785, 101360], false⟩

theorem canonicalMatch7_450 :
    canonicalPose7_450.boxKey 188160 (referenceBox7 (!canonicalBox7_450.bump)) = canonicalBox7_450 := by decide +kernel

theorem canonicalDecode7_450 : canonicalBox7_450.toKeyData 188160 = keys7Chunk14.get ⟨2, by decide⟩ := by
  change canonicalBox7_450.toKeyData 188160 = ⟨![(4 / 7), (45 / 28), 2, (23 / 14), (19 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (169 / 105), (671 / 336), (737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_450 : keySolid (keys7Chunk14.get ⟨2, by decide⟩) = canonicalPose7_450.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_450 (box := canonicalBox7_450) (k := keys7Chunk14.get ⟨2, by decide⟩) (canonicalMatch7_450) (canonicalDecode7_450)

def canonicalPose7_451 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, false, false, false, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_451 : BoxKey 7 :=
  ⟨![127680, 309120, 376320, 302400, 107520, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 309540, 376880, 302848, 108010, 101360, 134785], true⟩

theorem canonicalMatch7_451 :
    canonicalPose7_451.boxKey 188160 (referenceBox7 (!canonicalBox7_451.bump)) = canonicalBox7_451 := by decide +kernel

theorem canonicalDecode7_451 : canonicalBox7_451.toKeyData 188160 = keys7Chunk14.get ⟨3, by decide⟩ := by
  change canonicalBox7_451.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), 2, (45 / 28), (4 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (673 / 336), (169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_451 : keySolid (keys7Chunk14.get ⟨3, by decide⟩) = canonicalPose7_451.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_451 (box := canonicalBox7_451) (k := keys7Chunk14.get ⟨3, by decide⟩) (canonicalMatch7_451) (canonicalDecode7_451)

def canonicalPose7_452 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, true, false, true, true], ![0, 2, 2, 2, 0, 1, 1]⟩
def canonicalBox7_452 : BoxKey 7 :=
  ⟨![100800, 268800, 262080, 376320, 120960, 60480, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 261632, 375760, 121380, 60080, 53375], false⟩

theorem canonicalMatch7_452 :
    canonicalPose7_452.boxKey 188160 (referenceBox7 (!canonicalBox7_452.bump)) = canonicalBox7_452 := by decide +kernel

theorem canonicalDecode7_452 : canonicalBox7_452.toKeyData 188160 = keys7Chunk14.get ⟨4, by decide⟩ := by
  change canonicalBox7_452.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (9 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (751 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_452 : keySolid (keys7Chunk14.get ⟨4, by decide⟩) = canonicalPose7_452.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_452 (box := canonicalBox7_452) (k := keys7Chunk14.get ⟨4, by decide⟩) (canonicalMatch7_452) (canonicalDecode7_452)

def canonicalPose7_453 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, false, true, false, false, false], ![0, 2, 1, 2, 0, 0, 0]⟩
def canonicalBox7_453 : BoxKey 7 :=
  ⟨![100800, 241920, 315840, 255360, 0, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 241535, 316240, 254940, 560, 114688, 108010], false⟩

theorem canonicalMatch7_453 :
    canonicalPose7_453.boxKey 188160 (referenceBox7 (!canonicalBox7_453.bump)) = canonicalBox7_453 := by decide +kernel

theorem canonicalDecode7_453 : canonicalBox7_453.toKeyData 188160 = keys7Chunk14.get ⟨5, by decide⟩ := by
  change canonicalBox7_453.toKeyData 188160 = ⟨![(15 / 28), (9 / 7), (47 / 28), (19 / 14), 0, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_453 : keySolid (keys7Chunk14.get ⟨5, by decide⟩) = canonicalPose7_453.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_453 (box := canonicalBox7_453) (k := keys7Chunk14.get ⟨5, by decide⟩) (canonicalMatch7_453) (canonicalDecode7_453)

def canonicalPose7_454 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, false, true, false, false, true, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_454 : BoxKey 7 :=
  ⟨![100800, 322560, 248640, 309120, 114240, 0, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 322945, 248240, 309540, 114688, -560, 108010], true⟩

theorem canonicalMatch7_454 :
    canonicalPose7_454.boxKey 188160 (referenceBox7 (!canonicalBox7_454.bump)) = canonicalBox7_454 := by decide +kernel

theorem canonicalDecode7_454 : canonicalBox7_454.toKeyData 188160 = keys7Chunk14.get ⟨6, by decide⟩ := by
  change canonicalBox7_454.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (37 / 28), (23 / 14), (17 / 28), 0, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105), (-1 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_454 : keySolid (keys7Chunk14.get ⟨6, by decide⟩) = canonicalPose7_454.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_454 (box := canonicalBox7_454) (k := keys7Chunk14.get ⟨6, by decide⟩) (canonicalMatch7_454) (canonicalDecode7_454)

def canonicalPose7_455 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, false, true, false, false, false, false], ![0, 1, 2, 1, 0, 0, 0]⟩
def canonicalBox7_455 : BoxKey 7 :=
  ⟨![114240, 309120, 248640, 322560, 100800, 107520, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 309540, 248240, 322945, 101360, 108010, 560], false⟩

theorem canonicalMatch7_455 :
    canonicalPose7_455.boxKey 188160 (referenceBox7 (!canonicalBox7_455.bump)) = canonicalBox7_455 := by decide +kernel

theorem canonicalDecode7_455 : canonicalBox7_455.toKeyData 188160 = keys7Chunk14.get ⟨7, by decide⟩ := by
  change canonicalBox7_455.toKeyData 188160 = ⟨![(17 / 28), (23 / 14), (37 / 28), (12 / 7), (15 / 28), (4 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_455 : keySolid (keys7Chunk14.get ⟨7, by decide⟩) = canonicalPose7_455.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_455 (box := canonicalBox7_455) (k := keys7Chunk14.get ⟨7, by decide⟩) (canonicalMatch7_455) (canonicalDecode7_455)

def canonicalPose7_456 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, true, false, true, true, false, true], ![0, 2, 1, 2, 1, 0, 2]⟩
def canonicalBox7_456 : BoxKey 7 :=
  ⟨![0, 262080, 309120, 248640, 53760, 100800, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![-560, 261632, 309540, 248240, 53375, 101360, 268310], true⟩

theorem canonicalMatch7_456 :
    canonicalPose7_456.boxKey 188160 (referenceBox7 (!canonicalBox7_456.bump)) = canonicalBox7_456 := by decide +kernel

theorem canonicalDecode7_456 : canonicalBox7_456.toKeyData 188160 = keys7Chunk14.get ⟨8, by decide⟩ := by
  change canonicalBox7_456.toKeyData 188160 = ⟨![0, (39 / 28), (23 / 14), (37 / 28), (2 / 7), (15 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(-1 / 336), (146 / 105), (737 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_456 : keySolid (keys7Chunk14.get ⟨8, by decide⟩) = canonicalPose7_456.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_456 (box := canonicalBox7_456) (k := keys7Chunk14.get ⟨8, by decide⟩) (canonicalMatch7_456) (canonicalDecode7_456)

def canonicalPose7_457 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, true, false, false, false, true], ![0, 2, 2, 1, 0, 0, 2]⟩
def canonicalBox7_457 : BoxKey 7 :=
  ⟨![114240, 376320, 255360, 315840, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 375760, 254940, 316240, 134785, 101360, 268310], false⟩

theorem canonicalMatch7_457 :
    canonicalPose7_457.boxKey 188160 (referenceBox7 (!canonicalBox7_457.bump)) = canonicalBox7_457 := by decide +kernel

theorem canonicalDecode7_457 : canonicalBox7_457.toKeyData 188160 = keys7Chunk14.get ⟨9, by decide⟩ := by
  change canonicalBox7_457.toKeyData 188160 = ⟨![(17 / 28), 2, (19 / 14), (47 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (671 / 336), (607 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_457 : keySolid (keys7Chunk14.get ⟨9, by decide⟩) = canonicalPose7_457.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_457 (box := canonicalBox7_457) (k := keys7Chunk14.get ⟨9, by decide⟩) (canonicalMatch7_457) (canonicalDecode7_457)

def canonicalPose7_458 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, true, true, false, false, false], ![1, 2, 2, 2, 0, 0, 1]⟩
def canonicalBox7_458 : BoxKey 7 :=
  ⟨![60480, 255360, 376320, 262080, 107520, 100800, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 375760, 261632, 108010, 101360, 322945], false⟩

theorem canonicalMatch7_458 :
    canonicalPose7_458.boxKey 188160 (referenceBox7 (!canonicalBox7_458.bump)) = canonicalBox7_458 := by decide +kernel

theorem canonicalDecode7_458 : canonicalBox7_458.toKeyData 188160 = keys7Chunk14.get ⟨10, by decide⟩ := by
  change canonicalBox7_458.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 2, (39 / 28), (4 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (671 / 336), (146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_458 : keySolid (keys7Chunk14.get ⟨10, by decide⟩) = canonicalPose7_458.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_458 (box := canonicalBox7_458) (k := keys7Chunk14.get ⟨10, by decide⟩) (canonicalMatch7_458) (canonicalDecode7_458)

def canonicalPose7_459 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, false, false, true, false, true], ![0, 2, 1, 2, 1, 0, 2]⟩
def canonicalBox7_459 : BoxKey 7 :=
  ⟨![100800, 268800, 302400, 376320, 67200, 127680, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 302848, 376880, 66780, 128080, 241535], true⟩

theorem canonicalMatch7_459 :
    canonicalPose7_459.boxKey 188160 (referenceBox7 (!canonicalBox7_459.bump)) = canonicalBox7_459 := by decide +kernel

theorem canonicalDecode7_459 : canonicalBox7_459.toKeyData 188160 = keys7Chunk14.get ⟨11, by decide⟩ := by
  change canonicalBox7_459.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (45 / 28), 2, (5 / 14), (19 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (169 / 105), (673 / 336), (159 / 448), (1601 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_459 : keySolid (keys7Chunk14.get ⟨11, by decide⟩) = canonicalPose7_459.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_459 (box := canonicalBox7_459) (k := keys7Chunk14.get ⟨11, by decide⟩) (canonicalMatch7_459) (canonicalDecode7_459)

def canonicalPose7_460 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, false, true, true, false, true], ![0, 2, 1, 2, 1, 0, 2]⟩
def canonicalBox7_460 : BoxKey 7 :=
  ⟨![134400, 248640, 309120, 376320, 73920, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 248240, 309540, 375760, 73472, 108010, 274960], false⟩

theorem canonicalMatch7_460 :
    canonicalPose7_460.boxKey 188160 (referenceBox7 (!canonicalBox7_460.bump)) = canonicalBox7_460 := by decide +kernel

theorem canonicalDecode7_460 : canonicalBox7_460.toKeyData 188160 = keys7Chunk14.get ⟨12, by decide⟩ := by
  change canonicalBox7_460.toKeyData 188160 = ⟨![(5 / 7), (37 / 28), (23 / 14), 2, (11 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3103 / 2352), (737 / 448), (671 / 336), (41 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_460 : keySolid (keys7Chunk14.get ⟨12, by decide⟩) = canonicalPose7_460.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_460 (box := canonicalBox7_460) (k := keys7Chunk14.get ⟨12, by decide⟩) (canonicalMatch7_460) (canonicalDecode7_460)

def canonicalPose7_461 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, true, true, false, false], ![1, 2, 2, 2, 0, 0, 1]⟩
def canonicalBox7_461 : BoxKey 7 :=
  ⟨![53760, 275520, 268800, 262080, 0, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 274960, 268310, 261632, -560, 121380, 316240], true⟩

theorem canonicalMatch7_461 :
    canonicalPose7_461.boxKey 188160 (referenceBox7 (!canonicalBox7_461.bump)) = canonicalBox7_461 := by decide +kernel

theorem canonicalDecode7_461 : canonicalBox7_461.toKeyData 188160 = keys7Chunk14.get ⟨13, by decide⟩ := by
  change canonicalBox7_461.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (10 / 7), (39 / 28), 0, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (289 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_461 : keySolid (keys7Chunk14.get ⟨13, by decide⟩) = canonicalPose7_461.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_461 (box := canonicalBox7_461) (k := keys7Chunk14.get ⟨13, by decide⟩) (canonicalMatch7_461) (canonicalDecode7_461)

def canonicalPose7_462 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, false, false, true, true], ![0, 2, 2, 1, 0, 0, 2]⟩
def canonicalBox7_462 : BoxKey 7 :=
  ⟨![107520, 275520, 241920, 315840, 120960, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 241535, 316240, 121380, -560, 261632], true⟩

theorem canonicalMatch7_462 :
    canonicalPose7_462.boxKey 188160 (referenceBox7 (!canonicalBox7_462.bump)) = canonicalBox7_462 := by decide +kernel

theorem canonicalDecode7_462 : canonicalBox7_462.toKeyData 188160 = keys7Chunk14.get ⟨14, by decide⟩ := by
  change canonicalBox7_462.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (9 / 7), (47 / 28), (9 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_462 : keySolid (keys7Chunk14.get ⟨14, by decide⟩) = canonicalPose7_462.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_462 (box := canonicalBox7_462) (k := keys7Chunk14.get ⟨14, by decide⟩) (canonicalMatch7_462) (canonicalDecode7_462)

def canonicalPose7_463 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, true, false, true, true, false, true], ![0, 2, 1, 2, 1, 0, 2]⟩
def canonicalBox7_463 : BoxKey 7 :=
  ⟨![107520, 275520, 322560, 248640, 67200, 114240, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 274960, 322945, 248240, 66780, 114688, 375760], false⟩

theorem canonicalMatch7_463 :
    canonicalPose7_463.boxKey 188160 (referenceBox7 (!canonicalBox7_463.bump)) = canonicalBox7_463 := by decide +kernel

theorem canonicalDecode7_463 : canonicalBox7_463.toKeyData 188160 = keys7Chunk14.get ⟨15, by decide⟩ := by
  change canonicalBox7_463.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (12 / 7), (37 / 28), (5 / 14), (17 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_463 : keySolid (keys7Chunk14.get ⟨15, by decide⟩) = canonicalPose7_463.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_463 (box := canonicalBox7_463) (k := keys7Chunk14.get ⟨15, by decide⟩) (canonicalMatch7_463) (canonicalDecode7_463)

def canonicalPose7_464 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, true, true, false, false], ![0, 2, 2, 2, 1, 1, 0]⟩
def canonicalBox7_464 : BoxKey 7 :=
  ⟨![0, 262080, 268800, 275520, 53760, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 261632, 268310, 274960, 53375, 316240, 121380], false⟩

theorem canonicalMatch7_464 :
    canonicalPose7_464.boxKey 188160 (referenceBox7 (!canonicalBox7_464.bump)) = canonicalBox7_464 := by decide +kernel

theorem canonicalDecode7_464 : canonicalBox7_464.toKeyData 188160 = keys7Chunk14.get ⟨16, by decide⟩ := by
  change canonicalBox7_464.toKeyData 188160 = ⟨![0, (39 / 28), (10 / 7), (41 / 28), (2 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_464 : keySolid (keys7Chunk14.get ⟨16, by decide⟩) = canonicalPose7_464.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_464 (box := canonicalBox7_464) (k := keys7Chunk14.get ⟨16, by decide⟩) (canonicalMatch7_464) (canonicalDecode7_464)

def canonicalPose7_465 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, false, true, false, true, false], ![1, 2, 1, 2, 0, 2, 0]⟩
def canonicalBox7_465 : BoxKey 7 :=
  ⟨![73920, 376320, 309120, 248640, 134400, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, 376880, 309540, 248240, 134785, 274960, 108010], true⟩

theorem canonicalMatch7_465 :
    canonicalPose7_465.boxKey 188160 (referenceBox7 (!canonicalBox7_465.bump)) = canonicalBox7_465 := by decide +kernel

theorem canonicalDecode7_465 : canonicalBox7_465.toKeyData 188160 = keys7Chunk14.get ⟨17, by decide⟩ := by
  change canonicalBox7_465.toKeyData 188160 = ⟨![(11 / 28), 2, (23 / 14), (37 / 28), (5 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (673 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_465 : keySolid (keys7Chunk14.get ⟨17, by decide⟩) = canonicalPose7_465.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_465 (box := canonicalBox7_465) (k := keys7Chunk14.get ⟨17, by decide⟩) (canonicalMatch7_465) (canonicalDecode7_465)

def canonicalPose7_466 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, false, true, false, true, false], ![1, 2, 1, 2, 0, 2, 0]⟩
def canonicalBox7_466 : BoxKey 7 :=
  ⟨![67200, 376320, 302400, 268800, 100800, 241920, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 375760, 302848, 268310, 101360, 241535, 128080], false⟩

theorem canonicalMatch7_466 :
    canonicalPose7_466.boxKey 188160 (referenceBox7 (!canonicalBox7_466.bump)) = canonicalBox7_466 := by decide +kernel

theorem canonicalDecode7_466 : canonicalBox7_466.toKeyData 188160 = keys7Chunk14.get ⟨18, by decide⟩ := by
  change canonicalBox7_466.toKeyData 188160 = ⟨![(5 / 14), 2, (45 / 28), (10 / 7), (15 / 28), (9 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (671 / 336), (169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_466 : keySolid (keys7Chunk14.get ⟨18, by decide⟩) = canonicalPose7_466.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_466 (box := canonicalBox7_466) (k := keys7Chunk14.get ⟨18, by decide⟩) (canonicalMatch7_466) (canonicalDecode7_466)

def canonicalPose7_467 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, true, true, false, false], ![0, 2, 2, 2, 1, 1, 0]⟩
def canonicalBox7_467 : BoxKey 7 :=
  ⟨![107520, 262080, 376320, 255360, 60480, 322560, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 261632, 376880, 254940, 60080, 322945, 101360], true⟩

theorem canonicalMatch7_467 :
    canonicalPose7_467.boxKey 188160 (referenceBox7 (!canonicalBox7_467.bump)) = canonicalBox7_467 := by decide +kernel

theorem canonicalDecode7_467 : canonicalBox7_467.toKeyData 188160 = keys7Chunk14.get ⟨19, by decide⟩ := by
  change canonicalBox7_467.toKeyData 188160 = ⟨![(4 / 7), (39 / 28), 2, (19 / 14), (9 / 28), (12 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (146 / 105), (673 / 336), (607 / 448), (751 / 2352), (9227 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_467 : keySolid (keys7Chunk14.get ⟨19, by decide⟩) = canonicalPose7_467.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_467 (box := canonicalBox7_467) (k := keys7Chunk14.get ⟨19, by decide⟩) (canonicalMatch7_467) (canonicalDecode7_467)

def canonicalPose7_468 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, true, false, false, true, false], ![0, 1, 2, 2, 0, 2, 0]⟩
def canonicalBox7_468 : BoxKey 7 :=
  ⟨![134400, 315840, 255360, 376320, 114240, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 316240, 254940, 376880, 114688, 268310, 101360], true⟩

theorem canonicalMatch7_468 :
    canonicalPose7_468.boxKey 188160 (referenceBox7 (!canonicalBox7_468.bump)) = canonicalBox7_468 := by decide +kernel

theorem canonicalDecode7_468 : canonicalBox7_468.toKeyData 188160 = keys7Chunk14.get ⟨20, by decide⟩ := by
  change canonicalBox7_468.toKeyData 188160 = ⟨![(5 / 7), (47 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3953 / 2352), (607 / 448), (673 / 336), (64 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_468 : keySolid (keys7Chunk14.get ⟨20, by decide⟩) = canonicalPose7_468.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_468 (box := canonicalBox7_468) (k := keys7Chunk14.get ⟨20, by decide⟩) (canonicalMatch7_468) (canonicalDecode7_468)

def canonicalPose7_469 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, true, false, true, false, true, false], ![1, 2, 1, 2, 0, 2, 0]⟩
def canonicalBox7_469 : BoxKey 7 :=
  ⟨![53760, 248640, 309120, 262080, 0, 268800, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 248240, 309540, 261632, 560, 268310, 101360], false⟩

theorem canonicalMatch7_469 :
    canonicalPose7_469.boxKey 188160 (referenceBox7 (!canonicalBox7_469.bump)) = canonicalBox7_469 := by decide +kernel

theorem canonicalDecode7_469 : canonicalBox7_469.toKeyData 188160 = keys7Chunk14.get ⟨21, by decide⟩ := by
  change canonicalBox7_469.toKeyData 188160 = ⟨![(2 / 7), (37 / 28), (23 / 14), (39 / 28), 0, (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (3103 / 2352), (737 / 448), (146 / 105), (1 / 336), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_469 : keySolid (keys7Chunk14.get ⟨21, by decide⟩) = canonicalPose7_469.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_469 (box := canonicalBox7_469) (k := keys7Chunk14.get ⟨21, by decide⟩) (canonicalMatch7_469) (canonicalDecode7_469)

def canonicalPose7_470 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, true, false, true, false, false, false], ![1, 2, 1, 2, 0, 2, 0]⟩
def canonicalBox7_470 : BoxKey 7 :=
  ⟨![67200, 248640, 322560, 275520, 107520, 376320, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 248240, 322945, 274960, 108010, 376880, 114688], true⟩

theorem canonicalMatch7_470 :
    canonicalPose7_470.boxKey 188160 (referenceBox7 (!canonicalBox7_470.bump)) = canonicalBox7_470 := by decide +kernel

theorem canonicalDecode7_470 : canonicalBox7_470.toKeyData 188160 = keys7Chunk14.get ⟨22, by decide⟩ := by
  change canonicalBox7_470.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (12 / 7), (41 / 28), (4 / 7), 2, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (673 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_470 : keySolid (keys7Chunk14.get ⟨22, by decide⟩) = canonicalPose7_470.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_470 (box := canonicalBox7_470) (k := keys7Chunk14.get ⟨22, by decide⟩) (canonicalMatch7_470) (canonicalDecode7_470)

def canonicalPose7_471 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, true, true, false, true, false], ![0, 1, 2, 2, 0, 2, 0]⟩
def canonicalBox7_471 : BoxKey 7 :=
  ⟨![120960, 315840, 241920, 275520, 107520, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 241535, 274960, 108010, 261632, 560], false⟩

theorem canonicalMatch7_471 :
    canonicalPose7_471.boxKey 188160 (referenceBox7 (!canonicalBox7_471.bump)) = canonicalBox7_471 := by decide +kernel

theorem canonicalDecode7_471 : canonicalBox7_471.toKeyData 188160 = keys7Chunk14.get ⟨23, by decide⟩ := by
  change canonicalBox7_471.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (9 / 7), (41 / 28), (4 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_471 : keySolid (keys7Chunk14.get ⟨23, by decide⟩) = canonicalPose7_471.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_471 (box := canonicalBox7_471) (k := keys7Chunk14.get ⟨23, by decide⟩) (canonicalMatch7_471) (canonicalDecode7_471)

def canonicalPose7_472 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, true, false, true, true], ![0, 2, 1, 2, 0, 2, 2]⟩
def canonicalBox7_472 : BoxKey 7 :=
  ⟨![0, 255360, 315840, 241920, 100800, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 254940, 316240, 241535, 101360, 268310, 261632], true⟩

theorem canonicalMatch7_472 :
    canonicalPose7_472.boxKey 188160 (referenceBox7 (!canonicalBox7_472.bump)) = canonicalBox7_472 := by decide +kernel

theorem canonicalDecode7_472 : canonicalBox7_472.toKeyData 188160 = keys7Chunk14.get ⟨24, by decide⟩ := by
  change canonicalBox7_472.toKeyData 188160 = ⟨![0, (19 / 14), (47 / 28), (9 / 7), (15 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_472 : keySolid (keys7Chunk14.get ⟨24, by decide⟩) = canonicalPose7_472.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_472 (box := canonicalBox7_472) (k := keys7Chunk14.get ⟨24, by decide⟩) (canonicalMatch7_472) (canonicalDecode7_472)

def canonicalPose7_473 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, true, true, false, false, false], ![0, 2, 2, 2, 0, 1, 1]⟩
def canonicalBox7_473 : BoxKey 7 :=
  ⟨![120960, 376320, 262080, 268800, 100800, 322560, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 376880, 261632, 268310, 101360, 322945, 316240], true⟩

theorem canonicalMatch7_473 :
    canonicalPose7_473.boxKey 188160 (referenceBox7 (!canonicalBox7_473.bump)) = canonicalBox7_473 := by decide +kernel

theorem canonicalDecode7_473 : canonicalBox7_473.toKeyData 188160 = keys7Chunk14.get ⟨25, by decide⟩ := by
  change canonicalBox7_473.toKeyData 188160 = ⟨![(9 / 14), 2, (39 / 28), (10 / 7), (15 / 28), (12 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_473 : keySolid (keys7Chunk14.get ⟨25, by decide⟩) = canonicalPose7_473.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_473 (box := canonicalBox7_473) (k := keys7Chunk14.get ⟨25, by decide⟩) (canonicalMatch7_473) (canonicalDecode7_473)

def canonicalPose7_474 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, false, false, true, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_474 : BoxKey 7 :=
  ⟨![107520, 302400, 376320, 309120, 127680, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 302848, 375760, 309540, 128080, 241535, 274960], false⟩

theorem canonicalMatch7_474 :
    canonicalPose7_474.boxKey 188160 (referenceBox7 (!canonicalBox7_474.bump)) = canonicalBox7_474 := by decide +kernel

theorem canonicalDecode7_474 : canonicalBox7_474.toKeyData 188160 = keys7Chunk14.get ⟨26, by decide⟩ := by
  change canonicalBox7_474.toKeyData 188160 = ⟨![(4 / 7), (45 / 28), 2, (23 / 14), (19 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (169 / 105), (671 / 336), (737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_474 : keySolid (keys7Chunk14.get ⟨26, by decide⟩) = canonicalPose7_474.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_474 (box := canonicalBox7_474) (k := keys7Chunk14.get ⟨26, by decide⟩) (canonicalMatch7_474) (canonicalDecode7_474)

def canonicalPose7_475 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, false, false, true, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_475 : BoxKey 7 :=
  ⟨![127680, 309120, 376320, 302400, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 309540, 376880, 302848, 108010, 274960, 241535], true⟩

theorem canonicalMatch7_475 :
    canonicalPose7_475.boxKey 188160 (referenceBox7 (!canonicalBox7_475.bump)) = canonicalBox7_475 := by decide +kernel

theorem canonicalDecode7_475 : canonicalBox7_475.toKeyData 188160 = keys7Chunk14.get ⟨27, by decide⟩ := by
  change canonicalBox7_475.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), 2, (45 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (673 / 336), (169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_475 : keySolid (keys7Chunk14.get ⟨27, by decide⟩) = canonicalPose7_475.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_475 (box := canonicalBox7_475) (k := keys7Chunk14.get ⟨27, by decide⟩) (canonicalMatch7_475) (canonicalDecode7_475)

def canonicalPose7_476 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, true, false, false, false], ![0, 2, 2, 2, 0, 1, 1]⟩
def canonicalBox7_476 : BoxKey 7 :=
  ⟨![100800, 268800, 262080, 376320, 120960, 315840, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 261632, 375760, 121380, 316240, 322945], false⟩

theorem canonicalMatch7_476 :
    canonicalPose7_476.boxKey 188160 (referenceBox7 (!canonicalBox7_476.bump)) = canonicalBox7_476 := by decide +kernel

theorem canonicalDecode7_476 : canonicalBox7_476.toKeyData 188160 = keys7Chunk14.get ⟨28, by decide⟩ := by
  change canonicalBox7_476.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (47 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (3953 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_476 : keySolid (keys7Chunk14.get ⟨28, by decide⟩) = canonicalPose7_476.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_476 (box := canonicalBox7_476) (k := keys7Chunk14.get ⟨28, by decide⟩) (canonicalMatch7_476) (canonicalDecode7_476)

def canonicalPose7_477 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, false, true, false, true, true], ![0, 2, 1, 2, 0, 2, 2]⟩
def canonicalBox7_477 : BoxKey 7 :=
  ⟨![100800, 241920, 315840, 255360, 0, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 241535, 316240, 254940, 560, 261632, 268310], false⟩

theorem canonicalMatch7_477 :
    canonicalPose7_477.boxKey 188160 (referenceBox7 (!canonicalBox7_477.bump)) = canonicalBox7_477 := by decide +kernel

theorem canonicalDecode7_477 : canonicalBox7_477.toKeyData 188160 = keys7Chunk14.get ⟨29, by decide⟩ := by
  change canonicalBox7_477.toKeyData 188160 = ⟨![(15 / 28), (9 / 7), (47 / 28), (19 / 14), 0, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (146 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_477 : keySolid (keys7Chunk14.get ⟨29, by decide⟩) = canonicalPose7_477.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_477 (box := canonicalBox7_477) (k := keys7Chunk14.get ⟨29, by decide⟩) (canonicalMatch7_477) (canonicalDecode7_477)

def canonicalPose7_478 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, false, true, false, false, false, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_478 : BoxKey 7 :=
  ⟨![100800, 322560, 248640, 309120, 114240, 376320, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 322945, 248240, 309540, 114688, 376880, 268310], true⟩

theorem canonicalMatch7_478 :
    canonicalPose7_478.boxKey 188160 (referenceBox7 (!canonicalBox7_478.bump)) = canonicalBox7_478 := by decide +kernel

theorem canonicalDecode7_478 : canonicalBox7_478.toKeyData 188160 = keys7Chunk14.get ⟨30, by decide⟩ := by
  change canonicalBox7_478.toKeyData 188160 = ⟨![(15 / 28), (12 / 7), (37 / 28), (23 / 14), (17 / 28), 2, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105), (673 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_478 : keySolid (keys7Chunk14.get ⟨30, by decide⟩) = canonicalPose7_478.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_478 (box := canonicalBox7_478) (k := keys7Chunk14.get ⟨30, by decide⟩) (canonicalMatch7_478) (canonicalDecode7_478)

def canonicalPose7_479 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, false, true, false, false, true, true], ![0, 1, 2, 1, 0, 2, 2]⟩
def canonicalBox7_479 : BoxKey 7 :=
  ⟨![114240, 309120, 248640, 322560, 100800, 268800, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 309540, 248240, 322945, 101360, 268310, 375760], false⟩

theorem canonicalMatch7_479 :
    canonicalPose7_479.boxKey 188160 (referenceBox7 (!canonicalBox7_479.bump)) = canonicalBox7_479 := by decide +kernel

theorem canonicalDecode7_479 : canonicalBox7_479.toKeyData 188160 = keys7Chunk14.get ⟨31, by decide⟩ := by
  change canonicalBox7_479.toKeyData 188160 = ⟨![(17 / 28), (23 / 14), (37 / 28), (12 / 7), (15 / 28), (10 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_479 : keySolid (keys7Chunk14.get ⟨31, by decide⟩) = canonicalPose7_479.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_479 (box := canonicalBox7_479) (k := keys7Chunk14.get ⟨31, by decide⟩) (canonicalMatch7_479) (canonicalDecode7_479)

theorem keys7Chunk14_canonical : ∀ k ∈ keys7Chunk14,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk14, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_448, canonicalSolid7_448⟩
  · exact ⟨canonicalPose7_449, canonicalSolid7_449⟩
  · exact ⟨canonicalPose7_450, canonicalSolid7_450⟩
  · exact ⟨canonicalPose7_451, canonicalSolid7_451⟩
  · exact ⟨canonicalPose7_452, canonicalSolid7_452⟩
  · exact ⟨canonicalPose7_453, canonicalSolid7_453⟩
  · exact ⟨canonicalPose7_454, canonicalSolid7_454⟩
  · exact ⟨canonicalPose7_455, canonicalSolid7_455⟩
  · exact ⟨canonicalPose7_456, canonicalSolid7_456⟩
  · exact ⟨canonicalPose7_457, canonicalSolid7_457⟩
  · exact ⟨canonicalPose7_458, canonicalSolid7_458⟩
  · exact ⟨canonicalPose7_459, canonicalSolid7_459⟩
  · exact ⟨canonicalPose7_460, canonicalSolid7_460⟩
  · exact ⟨canonicalPose7_461, canonicalSolid7_461⟩
  · exact ⟨canonicalPose7_462, canonicalSolid7_462⟩
  · exact ⟨canonicalPose7_463, canonicalSolid7_463⟩
  · exact ⟨canonicalPose7_464, canonicalSolid7_464⟩
  · exact ⟨canonicalPose7_465, canonicalSolid7_465⟩
  · exact ⟨canonicalPose7_466, canonicalSolid7_466⟩
  · exact ⟨canonicalPose7_467, canonicalSolid7_467⟩
  · exact ⟨canonicalPose7_468, canonicalSolid7_468⟩
  · exact ⟨canonicalPose7_469, canonicalSolid7_469⟩
  · exact ⟨canonicalPose7_470, canonicalSolid7_470⟩
  · exact ⟨canonicalPose7_471, canonicalSolid7_471⟩
  · exact ⟨canonicalPose7_472, canonicalSolid7_472⟩
  · exact ⟨canonicalPose7_473, canonicalSolid7_473⟩
  · exact ⟨canonicalPose7_474, canonicalSolid7_474⟩
  · exact ⟨canonicalPose7_475, canonicalSolid7_475⟩
  · exact ⟨canonicalPose7_476, canonicalSolid7_476⟩
  · exact ⟨canonicalPose7_477, canonicalSolid7_477⟩
  · exact ⟨canonicalPose7_478, canonicalSolid7_478⟩
  · exact ⟨canonicalPose7_479, canonicalSolid7_479⟩

#print axioms keys7Chunk14_canonical

end SparseMonotiles.Canonical
