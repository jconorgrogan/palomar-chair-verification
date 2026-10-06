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

def canonicalPose7_32 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, false, false, true, true, true, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_32 : BoxKey 7 :=
  ⟨![0, 107520, 100800, 53760, 248640, 67200, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![-560, 108010, 101360, 53375, 248240, 66780, 114688], true⟩

theorem canonicalMatch7_32 :
    canonicalPose7_32.boxKey 188160 (referenceBox7 (!canonicalBox7_32.bump)) = canonicalBox7_32 := by decide +kernel

theorem canonicalDecode7_32 : canonicalBox7_32.toKeyData 188160 = keys7Chunk1.get ⟨0, by decide⟩ := by
  change canonicalBox7_32.toKeyData 188160 = ⟨![0, (4 / 7), (15 / 28), (2 / 7), (37 / 28), (5 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(-1 / 336), (1543 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_32 : keySolid (keys7Chunk1.get ⟨0, by decide⟩) = canonicalPose7_32.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_32 (box := canonicalBox7_32) (k := keys7Chunk1.get ⟨0, by decide⟩) (canonicalMatch7_32) (canonicalDecode7_32)

def canonicalPose7_33 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, false, false, true, true, true, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_33 : BoxKey 7 :=
  ⟨![107520, 0, 114240, 67200, 248640, 53760, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, 560, 114688, 66780, 248240, 53375, 101360], false⟩

theorem canonicalMatch7_33 :
    canonicalPose7_33.boxKey 188160 (referenceBox7 (!canonicalBox7_33.bump)) = canonicalBox7_33 := by decide +kernel

theorem canonicalDecode7_33 : canonicalBox7_33.toKeyData 188160 = keys7Chunk1.get ⟨1, by decide⟩ := by
  change canonicalBox7_33.toKeyData 188160 = ⟨![(4 / 7), 0, (17 / 28), (5 / 14), (37 / 28), (2 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (1 / 336), (64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_33 : keySolid (keys7Chunk1.get ⟨1, by decide⟩) = canonicalPose7_33.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_33 (box := canonicalBox7_33) (k := keys7Chunk1.get ⟨1, by decide⟩) (canonicalMatch7_33) (canonicalDecode7_33)

def canonicalPose7_34 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, false, false, false, false], ![0, 0, 0, 0, 1, 0, 0]⟩
def canonicalBox7_34 : BoxKey 7 :=
  ⟨![107520, 114240, 0, 120960, 315840, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, -560, 121380, 316240, 134785, 101360], true⟩

theorem canonicalMatch7_34 :
    canonicalPose7_34.boxKey 188160 (referenceBox7 (!canonicalBox7_34.bump)) = canonicalBox7_34 := by decide +kernel

theorem canonicalDecode7_34 : canonicalBox7_34.toKeyData 188160 = keys7Chunk1.get ⟨2, by decide⟩ := by
  change canonicalBox7_34.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 0, (9 / 14), (47 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_34 : keySolid (keys7Chunk1.get ⟨2, by decide⟩) = canonicalPose7_34.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_34 (box := canonicalBox7_34) (k := keys7Chunk1.get ⟨2, by decide⟩) (canonicalMatch7_34) (canonicalDecode7_34)

def canonicalPose7_35 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, false, true, true, false, false], ![1, 1, 0, 0, 2, 0, 0]⟩
def canonicalBox7_35 : BoxKey 7 :=
  ⟨![53760, 60480, 120960, 0, 262080, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 60080, 121380, -560, 261632, 108010, 101360], true⟩

theorem canonicalMatch7_35 :
    canonicalPose7_35.boxKey 188160 (referenceBox7 (!canonicalBox7_35.bump)) = canonicalBox7_35 := by decide +kernel

theorem canonicalDecode7_35 : canonicalBox7_35.toKeyData 188160 = keys7Chunk1.get ⟨3, by decide⟩ := by
  change canonicalBox7_35.toKeyData 188160 = ⟨![(2 / 7), (9 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (751 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_35 : keySolid (keys7Chunk1.get ⟨3, by decide⟩) = canonicalPose7_35.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_35 (box := canonicalBox7_35) (k := keys7Chunk1.get ⟨3, by decide⟩) (canonicalMatch7_35) (canonicalDecode7_35)

def canonicalPose7_36 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, true, false, true, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_36 : BoxKey 7 :=
  ⟨![100800, 134400, 127680, 67200, 376320, 73920, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 128080, 66780, 376880, 73472, 108010], true⟩

theorem canonicalMatch7_36 :
    canonicalPose7_36.boxKey 188160 (referenceBox7 (!canonicalBox7_36.bump)) = canonicalBox7_36 := by decide +kernel

theorem canonicalDecode7_36 : canonicalBox7_36.toKeyData 188160 = keys7Chunk1.get ⟨4, by decide⟩ := by
  change canonicalBox7_36.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (19 / 28), (5 / 14), 2, (11 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (1601 / 2352), (159 / 448), (673 / 336), (41 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_36 : keySolid (keys7Chunk1.get ⟨4, by decide⟩) = canonicalPose7_36.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_36 (box := canonicalBox7_36) (k := keys7Chunk1.get ⟨4, by decide⟩) (canonicalMatch7_36) (canonicalDecode7_36)

def canonicalPose7_37 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, true, true, true, false], ![0, 0, 0, 1, 2, 1, 0]⟩
def canonicalBox7_37 : BoxKey 7 :=
  ⟨![134400, 100800, 107520, 73920, 376320, 67200, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 108010, 73472, 375760, 66780, 128080], false⟩

theorem canonicalMatch7_37 :
    canonicalPose7_37.boxKey 188160 (referenceBox7 (!canonicalBox7_37.bump)) = canonicalBox7_37 := by decide +kernel

theorem canonicalDecode7_37 : canonicalBox7_37.toKeyData 188160 = keys7Chunk1.get ⟨5, by decide⟩ := by
  change canonicalBox7_37.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (4 / 7), (11 / 28), 2, (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (1543 / 2688), (41 / 105), (671 / 336), (159 / 448), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_37 : keySolid (keys7Chunk1.get ⟨5, by decide⟩) = canonicalPose7_37.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_37 (box := canonicalBox7_37) (k := keys7Chunk1.get ⟨5, by decide⟩) (canonicalMatch7_37) (canonicalDecode7_37)

def canonicalPose7_38 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, false, false, true, false, false], ![1, 1, 0, 0, 2, 0, 0]⟩
def canonicalBox7_38 : BoxKey 7 :=
  ⟨![60480, 53760, 100800, 107520, 262080, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 53375, 101360, 108010, 261632, 560, 121380], false⟩

theorem canonicalMatch7_38 :
    canonicalPose7_38.boxKey 188160 (referenceBox7 (!canonicalBox7_38.bump)) = canonicalBox7_38 := by decide +kernel

theorem canonicalDecode7_38 : canonicalBox7_38.toKeyData 188160 = keys7Chunk1.get ⟨6, by decide⟩ := by
  change canonicalBox7_38.toKeyData 188160 = ⟨![(9 / 28), (2 / 7), (15 / 28), (4 / 7), (39 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_38 : keySolid (keys7Chunk1.get ⟨6, by decide⟩) = canonicalPose7_38.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_38 (box := canonicalBox7_38) (k := keys7Chunk1.get ⟨6, by decide⟩) (canonicalMatch7_38) (canonicalDecode7_38)

def canonicalPose7_39 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 1, 0, 0]⟩
def canonicalBox7_39 : BoxKey 7 :=
  ⟨![114240, 107520, 100800, 134400, 315840, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 101360, 134785, 316240, 121380, 560], false⟩

theorem canonicalMatch7_39 :
    canonicalPose7_39.boxKey 188160 (referenceBox7 (!canonicalBox7_39.bump)) = canonicalBox7_39 := by decide +kernel

theorem canonicalDecode7_39 : canonicalBox7_39.toKeyData 188160 = keys7Chunk1.get ⟨7, by decide⟩ := by
  change canonicalBox7_39.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (15 / 28), (5 / 7), (47 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_39 : keySolid (keys7Chunk1.get ⟨7, by decide⟩) = canonicalPose7_39.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_39 (box := canonicalBox7_39) (k := keys7Chunk1.get ⟨7, by decide⟩) (canonicalMatch7_39) (canonicalDecode7_39)

def canonicalPose7_40 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, false, false, true, true, true], ![0, 0, 0, 0, 2, 1, 2]⟩
def canonicalBox7_40 : BoxKey 7 :=
  ⟨![0, 114240, 107520, 100800, 241920, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 114688, 108010, 101360, 241535, 60080, 254940], true⟩

theorem canonicalMatch7_40 :
    canonicalPose7_40.boxKey 188160 (referenceBox7 (!canonicalBox7_40.bump)) = canonicalBox7_40 := by decide +kernel

theorem canonicalDecode7_40 : canonicalBox7_40.toKeyData 188160 = keys7Chunk1.get ⟨8, by decide⟩ := by
  change canonicalBox7_40.toKeyData 188160 = ⟨![0, (17 / 28), (4 / 7), (15 / 28), (9 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376), (751 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_40 : keySolid (keys7Chunk1.get ⟨8, by decide⟩) = canonicalPose7_40.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_40 (box := canonicalBox7_40) (k := keys7Chunk1.get ⟨8, by decide⟩) (canonicalMatch7_40) (canonicalDecode7_40)

def canonicalPose7_41 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 1, 0, 1]⟩
def canonicalBox7_41 : BoxKey 7 :=
  ⟨![114240, 0, 107520, 100800, 322560, 127680, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, 560, 108010, 101360, 322945, 128080, 309540], false⟩

theorem canonicalMatch7_41 :
    canonicalPose7_41.boxKey 188160 (referenceBox7 (!canonicalBox7_41.bump)) = canonicalBox7_41 := by decide +kernel

theorem canonicalDecode7_41 : canonicalBox7_41.toKeyData 188160 = keys7Chunk1.get ⟨9, by decide⟩ := by
  change canonicalBox7_41.toKeyData 188160 = ⟨![(17 / 28), 0, (4 / 7), (15 / 28), (12 / 7), (19 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_41 : keySolid (keys7Chunk1.get ⟨9, by decide⟩) = canonicalPose7_41.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_41 (box := canonicalBox7_41) (k := keys7Chunk1.get ⟨9, by decide⟩) (canonicalMatch7_41) (canonicalDecode7_41)

def canonicalPose7_42 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, false, true, false, false, false, false], ![0, 0, 0, 0, 1, 0, 1]⟩
def canonicalBox7_42 : BoxKey 7 :=
  ⟨![100800, 107520, 0, 114240, 309120, 127680, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 108010, -560, 114688, 309540, 128080, 322945], true⟩

theorem canonicalMatch7_42 :
    canonicalPose7_42.boxKey 188160 (referenceBox7 (!canonicalBox7_42.bump)) = canonicalBox7_42 := by decide +kernel

theorem canonicalDecode7_42 : canonicalBox7_42.toKeyData 188160 = keys7Chunk1.get ⟨10, by decide⟩ := by
  change canonicalBox7_42.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), 0, (17 / 28), (23 / 14), (19 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (-1 / 336), (64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_42 : keySolid (keys7Chunk1.get ⟨10, by decide⟩) = canonicalPose7_42.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_42 (box := canonicalBox7_42) (k := keys7Chunk1.get ⟨10, by decide⟩) (canonicalMatch7_42) (canonicalDecode7_42)

def canonicalPose7_43 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, false, false, true, true, true], ![0, 0, 0, 0, 2, 1, 2]⟩
def canonicalBox7_43 : BoxKey 7 :=
  ⟨![100800, 107520, 114240, 0, 255360, 60480, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 114688, 560, 254940, 60080, 241535], false⟩

theorem canonicalMatch7_43 :
    canonicalPose7_43.boxKey 188160 (referenceBox7 (!canonicalBox7_43.bump)) = canonicalBox7_43 := by decide +kernel

theorem canonicalDecode7_43 : canonicalBox7_43.toKeyData 188160 = keys7Chunk1.get ⟨11, by decide⟩ := by
  change canonicalBox7_43.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (9 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (64 / 105), (1 / 336), (607 / 448), (751 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_43 : keySolid (keys7Chunk1.get ⟨11, by decide⟩) = canonicalPose7_43.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_43 (box := canonicalBox7_43) (k := keys7Chunk1.get ⟨11, by decide⟩) (canonicalMatch7_43) (canonicalDecode7_43)

def canonicalPose7_44 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, true, false, true, false, true], ![0, 1, 1, 0, 2, 0, 2]⟩
def canonicalBox7_44 : BoxKey 7 :=
  ⟨![100800, 53760, 60480, 120960, 376320, 114240, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 53375, 60080, 121380, 375760, 114688, 268310], false⟩

theorem canonicalMatch7_44 :
    canonicalPose7_44.boxKey 188160 (referenceBox7 (!canonicalBox7_44.bump)) = canonicalBox7_44 := by decide +kernel

theorem canonicalDecode7_44 : canonicalBox7_44.toKeyData 188160 = keys7Chunk1.get ⟨12, by decide⟩ := by
  change canonicalBox7_44.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (9 / 28), (9 / 14), 2, (17 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (671 / 336), (64 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_44 : keySolid (keys7Chunk1.get ⟨12, by decide⟩) = canonicalPose7_44.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_44 (box := canonicalBox7_44) (k := keys7Chunk1.get ⟨12, by decide⟩) (canonicalMatch7_44) (canonicalDecode7_44)

def canonicalPose7_45 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 1, 0, 1]⟩
def canonicalBox7_45 : BoxKey 7 :=
  ⟨![107520, 100800, 134400, 127680, 309120, 0, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 134785, 128080, 309540, 560, 302848], false⟩

theorem canonicalMatch7_45 :
    canonicalPose7_45.boxKey 188160 (referenceBox7 (!canonicalBox7_45.bump)) = canonicalBox7_45 := by decide +kernel

theorem canonicalDecode7_45 : canonicalBox7_45.toKeyData 188160 = keys7Chunk1.get ⟨13, by decide⟩ := by
  change canonicalBox7_45.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (5 / 7), (19 / 28), (23 / 14), 0, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448), (1 / 336), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_45 : keySolid (keys7Chunk1.get ⟨13, by decide⟩) = canonicalPose7_45.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_45 (box := canonicalBox7_45) (k := keys7Chunk1.get ⟨13, by decide⟩) (canonicalMatch7_45) (canonicalDecode7_45)

def canonicalPose7_46 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, false, false, true, false], ![0, 0, 0, 0, 1, 0, 1]⟩
def canonicalBox7_46 : BoxKey 7 :=
  ⟨![127680, 134400, 100800, 107520, 302400, 0, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 134785, 101360, 108010, 302848, -560, 309540], true⟩

theorem canonicalMatch7_46 :
    canonicalPose7_46.boxKey 188160 (referenceBox7 (!canonicalBox7_46.bump)) = canonicalBox7_46 := by decide +kernel

theorem canonicalDecode7_46 : canonicalBox7_46.toKeyData 188160 = keys7Chunk1.get ⟨14, by decide⟩ := by
  change canonicalBox7_46.toKeyData 188160 = ⟨![(19 / 28), (5 / 7), (15 / 28), (4 / 7), (45 / 28), 0, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105), (-1 / 336), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_46 : keySolid (keys7Chunk1.get ⟨14, by decide⟩) = canonicalPose7_46.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_46 (box := canonicalBox7_46) (k := keys7Chunk1.get ⟨14, by decide⟩) (canonicalMatch7_46) (canonicalDecode7_46)

def canonicalPose7_47 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, true, false, true, false, false], ![0, 1, 1, 0, 2, 0, 2]⟩
def canonicalBox7_47 : BoxKey 7 :=
  ⟨![120960, 60480, 53760, 100800, 268800, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 60080, 53375, 101360, 268310, 114688, 376880], true⟩

theorem canonicalMatch7_47 :
    canonicalPose7_47.boxKey 188160 (referenceBox7 (!canonicalBox7_47.bump)) = canonicalBox7_47 := by decide +kernel

theorem canonicalDecode7_47 : canonicalBox7_47.toKeyData 188160 = keys7Chunk1.get ⟨15, by decide⟩ := by
  change canonicalBox7_47.toKeyData 188160 = ⟨![(9 / 14), (9 / 28), (2 / 7), (15 / 28), (10 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_47 : keySolid (keys7Chunk1.get ⟨15, by decide⟩) = canonicalPose7_47.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_47 (box := canonicalBox7_47) (k := keys7Chunk1.get ⟨15, by decide⟩) (canonicalMatch7_47) (canonicalDecode7_47)

def canonicalPose7_48 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 1, 1, 0]⟩
def canonicalBox7_48 : BoxKey 7 :=
  ⟨![0, 114240, 107520, 100800, 322560, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 114688, 108010, 101360, 322945, 316240, 121380], false⟩

theorem canonicalMatch7_48 :
    canonicalPose7_48.boxKey 188160 (referenceBox7 (!canonicalBox7_48.bump)) = canonicalBox7_48 := by decide +kernel

theorem canonicalDecode7_48 : canonicalBox7_48.toKeyData 188160 = keys7Chunk1.get ⟨16, by decide⟩ := by
  change canonicalBox7_48.toKeyData 188160 = ⟨![0, (17 / 28), (4 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_48 : keySolid (keys7Chunk1.get ⟨16, by decide⟩) = canonicalPose7_48.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_48 (box := canonicalBox7_48) (k := keys7Chunk1.get ⟨16, by decide⟩) (canonicalMatch7_48) (canonicalDecode7_48)

def canonicalPose7_49 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, false, true, true, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_49 : BoxKey 7 :=
  ⟨![73920, 0, 67200, 127680, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, -560, 66780, 128080, 241535, 274960, 108010], true⟩

theorem canonicalMatch7_49 :
    canonicalPose7_49.boxKey 188160 (referenceBox7 (!canonicalBox7_49.bump)) = canonicalBox7_49 := by decide +kernel

theorem canonicalDecode7_49 : canonicalBox7_49.toKeyData 188160 = keys7Chunk1.get ⟨17, by decide⟩ := by
  change canonicalBox7_49.toKeyData 188160 = ⟨![(11 / 28), 0, (5 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (-1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_49 : keySolid (keys7Chunk1.get ⟨17, by decide⟩) = canonicalPose7_49.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_49 (box := canonicalBox7_49) (k := keys7Chunk1.get ⟨17, by decide⟩) (canonicalMatch7_49) (canonicalDecode7_49)

def canonicalPose7_50 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, false, true, true, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_50 : BoxKey 7 :=
  ⟨![67200, 0, 73920, 107520, 275520, 241920, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 560, 73472, 108010, 274960, 241535, 128080], false⟩

theorem canonicalMatch7_50 :
    canonicalPose7_50.boxKey 188160 (referenceBox7 (!canonicalBox7_50.bump)) = canonicalBox7_50 := by decide +kernel

theorem canonicalDecode7_50 : canonicalBox7_50.toKeyData 188160 = keys7Chunk1.get ⟨18, by decide⟩ := by
  change canonicalBox7_50.toKeyData 188160 = ⟨![(5 / 14), 0, (11 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (1 / 336), (41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_50 : keySolid (keys7Chunk1.get ⟨18, by decide⟩) = canonicalPose7_50.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_50 (box := canonicalBox7_50) (k := keys7Chunk1.get ⟨18, by decide⟩) (canonicalMatch7_50) (canonicalDecode7_50)

def canonicalPose7_51 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, false, false, false, false], ![0, 0, 0, 0, 1, 1, 0]⟩
def canonicalBox7_51 : BoxKey 7 :=
  ⟨![107520, 114240, 0, 120960, 315840, 322560, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, -560, 121380, 316240, 322945, 101360], true⟩

theorem canonicalMatch7_51 :
    canonicalPose7_51.boxKey 188160 (referenceBox7 (!canonicalBox7_51.bump)) = canonicalBox7_51 := by decide +kernel

theorem canonicalDecode7_51 : canonicalBox7_51.toKeyData 188160 = keys7Chunk1.get ⟨19, by decide⟩ := by
  change canonicalBox7_51.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 0, (9 / 14), (47 / 28), (12 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_51 : keySolid (keys7Chunk1.get ⟨19, by decide⟩) = canonicalPose7_51.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_51 (box := canonicalBox7_51) (k := keys7Chunk1.get ⟨19, by decide⟩) (canonicalMatch7_51) (canonicalDecode7_51)

def canonicalPose7_52 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, false, true, true, true, false], ![0, 1, 0, 0, 2, 2, 0]⟩
def canonicalBox7_52 : BoxKey 7 :=
  ⟨![134400, 60480, 120960, 0, 262080, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 60080, 121380, -560, 261632, 268310, 101360], true⟩

theorem canonicalMatch7_52 :
    canonicalPose7_52.boxKey 188160 (referenceBox7 (!canonicalBox7_52.bump)) = canonicalBox7_52 := by decide +kernel

theorem canonicalDecode7_52 : canonicalBox7_52.toKeyData 188160 = keys7Chunk1.get ⟨20, by decide⟩ := by
  change canonicalBox7_52.toKeyData 188160 = ⟨![(5 / 7), (9 / 28), (9 / 14), 0, (39 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (751 / 2352), (289 / 448), (-1 / 336), (146 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_52 : keySolid (keys7Chunk1.get ⟨20, by decide⟩) = canonicalPose7_52.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_52 (box := canonicalBox7_52) (k := keys7Chunk1.get ⟨20, by decide⟩) (canonicalMatch7_52) (canonicalDecode7_52)

def canonicalPose7_53 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, false, true, false, true, true, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_53 : BoxKey 7 :=
  ⟨![53760, 127680, 67200, 114240, 376320, 268800, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 128080, 66780, 114688, 375760, 268310, 101360], false⟩

theorem canonicalMatch7_53 :
    canonicalPose7_53.boxKey 188160 (referenceBox7 (!canonicalBox7_53.bump)) = canonicalBox7_53 := by decide +kernel

theorem canonicalDecode7_53 : canonicalBox7_53.toKeyData 188160 = keys7Chunk1.get ⟨21, by decide⟩ := by
  change canonicalBox7_53.toKeyData 188160 = ⟨![(2 / 7), (19 / 28), (5 / 14), (17 / 28), 2, (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (1601 / 2352), (159 / 448), (64 / 105), (671 / 336), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_53 : keySolid (keys7Chunk1.get ⟨21, by decide⟩) = canonicalPose7_53.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_53 (box := canonicalBox7_53) (k := keys7Chunk1.get ⟨21, by decide⟩) (canonicalMatch7_53) (canonicalDecode7_53)

def canonicalPose7_54 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, false, true, false, true, false, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_54 : BoxKey 7 :=
  ⟨![67200, 127680, 53760, 100800, 268800, 376320, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 128080, 53375, 101360, 268310, 376880, 114688], true⟩

theorem canonicalMatch7_54 :
    canonicalPose7_54.boxKey 188160 (referenceBox7 (!canonicalBox7_54.bump)) = canonicalBox7_54 := by decide +kernel

theorem canonicalDecode7_54 : canonicalBox7_54.toKeyData 188160 = keys7Chunk1.get ⟨22, by decide⟩ := by
  change canonicalBox7_54.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (2 / 7), (15 / 28), (10 / 7), 2, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (673 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_54 : keySolid (keys7Chunk1.get ⟨22, by decide⟩) = canonicalPose7_54.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_54 (box := canonicalBox7_54) (k := keys7Chunk1.get ⟨22, by decide⟩) (canonicalMatch7_54) (canonicalDecode7_54)

def canonicalPose7_55 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 2, 0]⟩
def canonicalBox7_55 : BoxKey 7 :=
  ⟨![120960, 60480, 134400, 100800, 268800, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 60080, 134785, 101360, 268310, 261632, 560], false⟩

theorem canonicalMatch7_55 :
    canonicalPose7_55.boxKey 188160 (referenceBox7 (!canonicalBox7_55.bump)) = canonicalBox7_55 := by decide +kernel

theorem canonicalDecode7_55 : canonicalBox7_55.toKeyData 188160 = keys7Chunk1.get ⟨23, by decide⟩ := by
  change canonicalBox7_55.toKeyData 188160 = ⟨![(9 / 14), (9 / 28), (5 / 7), (15 / 28), (10 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_55 : keySolid (keys7Chunk1.get ⟨23, by decide⟩) = canonicalPose7_55.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_55 (box := canonicalBox7_55) (k := keys7Chunk1.get ⟨23, by decide⟩) (canonicalMatch7_55) (canonicalDecode7_55)

def canonicalPose7_56 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, false, true, false, true], ![0, 0, 0, 0, 2, 1, 2]⟩
def canonicalBox7_56 : BoxKey 7 :=
  ⟨![0, 114240, 107520, 100800, 241920, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 114688, 108010, 101360, 241535, 316240, 254940], false⟩

theorem canonicalMatch7_56 :
    canonicalPose7_56.boxKey 188160 (referenceBox7 (!canonicalBox7_56.bump)) = canonicalBox7_56 := by decide +kernel

theorem canonicalDecode7_56 : canonicalBox7_56.toKeyData 188160 = keys7Chunk1.get ⟨24, by decide⟩ := by
  change canonicalBox7_56.toKeyData 188160 = ⟨![0, (17 / 28), (4 / 7), (15 / 28), (9 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_56 : keySolid (keys7Chunk1.get ⟨24, by decide⟩) = canonicalPose7_56.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_56 (box := canonicalBox7_56) (k := keys7Chunk1.get ⟨24, by decide⟩) (canonicalMatch7_56) (canonicalDecode7_56)

def canonicalPose7_57 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, true, false, false, false, true, false], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_57 : BoxKey 7 :=
  ⟨![114240, 0, 107520, 100800, 322560, 248640, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, -560, 108010, 101360, 322945, 248240, 309540], true⟩

theorem canonicalMatch7_57 :
    canonicalPose7_57.boxKey 188160 (referenceBox7 (!canonicalBox7_57.bump)) = canonicalBox7_57 := by decide +kernel

theorem canonicalDecode7_57 : canonicalBox7_57.toKeyData 188160 = keys7Chunk1.get ⟨25, by decide⟩ := by
  change canonicalBox7_57.toKeyData 188160 = ⟨![(17 / 28), 0, (4 / 7), (15 / 28), (12 / 7), (37 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (-1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_57 : keySolid (keys7Chunk1.get ⟨25, by decide⟩) = canonicalPose7_57.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_57 (box := canonicalBox7_57) (k := keys7Chunk1.get ⟨25, by decide⟩) (canonicalMatch7_57) (canonicalDecode7_57)

def canonicalPose7_58 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, false, false, false, false, true, false], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_58 : BoxKey 7 :=
  ⟨![100800, 107520, 0, 114240, 309120, 248640, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 108010, 560, 114688, 309540, 248240, 322945], false⟩

theorem canonicalMatch7_58 :
    canonicalPose7_58.boxKey 188160 (referenceBox7 (!canonicalBox7_58.bump)) = canonicalBox7_58 := by decide +kernel

theorem canonicalDecode7_58 : canonicalBox7_58.toKeyData 188160 = keys7Chunk1.get ⟨26, by decide⟩ := by
  change canonicalBox7_58.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), 0, (17 / 28), (23 / 14), (37 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (1 / 336), (64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_58 : keySolid (keys7Chunk1.get ⟨26, by decide⟩) = canonicalPose7_58.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_58 (box := canonicalBox7_58) (k := keys7Chunk1.get ⟨26, by decide⟩) (canonicalMatch7_58) (canonicalDecode7_58)

def canonicalPose7_59 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, false, true, true, false, true], ![0, 0, 0, 0, 2, 1, 2]⟩
def canonicalBox7_59 : BoxKey 7 :=
  ⟨![100800, 107520, 114240, 0, 255360, 315840, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 114688, -560, 254940, 316240, 241535], true⟩

theorem canonicalMatch7_59 :
    canonicalPose7_59.boxKey 188160 (referenceBox7 (!canonicalBox7_59.bump)) = canonicalBox7_59 := by decide +kernel

theorem canonicalDecode7_59 : canonicalBox7_59.toKeyData 188160 = keys7Chunk1.get ⟨27, by decide⟩ := by
  change canonicalBox7_59.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (47 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_59 : keySolid (keys7Chunk1.get ⟨27, by decide⟩) = canonicalPose7_59.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_59 (box := canonicalBox7_59) (k := keys7Chunk1.get ⟨27, by decide⟩) (canonicalMatch7_59) (canonicalDecode7_59)

def canonicalPose7_60 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, true, false, false, true, true], ![0, 1, 1, 0, 2, 2, 2]⟩
def canonicalBox7_60 : BoxKey 7 :=
  ⟨![100800, 53760, 60480, 120960, 376320, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 53375, 60080, 121380, 376880, 261632, 268310], true⟩

theorem canonicalMatch7_60 :
    canonicalPose7_60.boxKey 188160 (referenceBox7 (!canonicalBox7_60.bump)) = canonicalBox7_60 := by decide +kernel

theorem canonicalDecode7_60 : canonicalBox7_60.toKeyData 188160 = keys7Chunk1.get ⟨28, by decide⟩ := by
  change canonicalBox7_60.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (9 / 28), (9 / 14), 2, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_60 : keySolid (keys7Chunk1.get ⟨28, by decide⟩) = canonicalPose7_60.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_60 (box := canonicalBox7_60) (k := keys7Chunk1.get ⟨28, by decide⟩) (canonicalMatch7_60) (canonicalDecode7_60)

def canonicalPose7_61 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_61 : BoxKey 7 :=
  ⟨![107520, 100800, 134400, 127680, 309120, 376320, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 134785, 128080, 309540, 376880, 302848], true⟩

theorem canonicalMatch7_61 :
    canonicalPose7_61.boxKey 188160 (referenceBox7 (!canonicalBox7_61.bump)) = canonicalBox7_61 := by decide +kernel

theorem canonicalDecode7_61 : canonicalBox7_61.toKeyData 188160 = keys7Chunk1.get ⟨29, by decide⟩ := by
  change canonicalBox7_61.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (5 / 7), (19 / 28), (23 / 14), 2, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448), (673 / 336), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_61 : keySolid (keys7Chunk1.get ⟨29, by decide⟩) = canonicalPose7_61.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_61 (box := canonicalBox7_61) (k := keys7Chunk1.get ⟨29, by decide⟩) (canonicalMatch7_61) (canonicalDecode7_61)

def canonicalPose7_62 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, false, false, true, false], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_62 : BoxKey 7 :=
  ⟨![127680, 134400, 100800, 107520, 302400, 376320, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 134785, 101360, 108010, 302848, 375760, 309540], false⟩

theorem canonicalMatch7_62 :
    canonicalPose7_62.boxKey 188160 (referenceBox7 (!canonicalBox7_62.bump)) = canonicalBox7_62 := by decide +kernel

theorem canonicalDecode7_62 : canonicalBox7_62.toKeyData 188160 = keys7Chunk1.get ⟨30, by decide⟩ := by
  change canonicalBox7_62.toKeyData 188160 = ⟨![(19 / 28), (5 / 7), (15 / 28), (4 / 7), (45 / 28), 2, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105), (671 / 336), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_62 : keySolid (keys7Chunk1.get ⟨30, by decide⟩) = canonicalPose7_62.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_62 (box := canonicalBox7_62) (k := keys7Chunk1.get ⟨30, by decide⟩) (canonicalMatch7_62) (canonicalDecode7_62)

def canonicalPose7_63 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, true, false, true, true, true], ![0, 1, 1, 0, 2, 2, 2]⟩
def canonicalBox7_63 : BoxKey 7 :=
  ⟨![120960, 60480, 53760, 100800, 268800, 262080, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 60080, 53375, 101360, 268310, 261632, 375760], false⟩

theorem canonicalMatch7_63 :
    canonicalPose7_63.boxKey 188160 (referenceBox7 (!canonicalBox7_63.bump)) = canonicalBox7_63 := by decide +kernel

theorem canonicalDecode7_63 : canonicalBox7_63.toKeyData 188160 = keys7Chunk1.get ⟨31, by decide⟩ := by
  change canonicalBox7_63.toKeyData 188160 = ⟨![(9 / 14), (9 / 28), (2 / 7), (15 / 28), (10 / 7), (39 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_63 : keySolid (keys7Chunk1.get ⟨31, by decide⟩) = canonicalPose7_63.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_63 (box := canonicalBox7_63) (k := keys7Chunk1.get ⟨31, by decide⟩) (canonicalMatch7_63) (canonicalDecode7_63)

theorem keys7Chunk1_canonical : ∀ k ∈ keys7Chunk1,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_32, canonicalSolid7_32⟩
  · exact ⟨canonicalPose7_33, canonicalSolid7_33⟩
  · exact ⟨canonicalPose7_34, canonicalSolid7_34⟩
  · exact ⟨canonicalPose7_35, canonicalSolid7_35⟩
  · exact ⟨canonicalPose7_36, canonicalSolid7_36⟩
  · exact ⟨canonicalPose7_37, canonicalSolid7_37⟩
  · exact ⟨canonicalPose7_38, canonicalSolid7_38⟩
  · exact ⟨canonicalPose7_39, canonicalSolid7_39⟩
  · exact ⟨canonicalPose7_40, canonicalSolid7_40⟩
  · exact ⟨canonicalPose7_41, canonicalSolid7_41⟩
  · exact ⟨canonicalPose7_42, canonicalSolid7_42⟩
  · exact ⟨canonicalPose7_43, canonicalSolid7_43⟩
  · exact ⟨canonicalPose7_44, canonicalSolid7_44⟩
  · exact ⟨canonicalPose7_45, canonicalSolid7_45⟩
  · exact ⟨canonicalPose7_46, canonicalSolid7_46⟩
  · exact ⟨canonicalPose7_47, canonicalSolid7_47⟩
  · exact ⟨canonicalPose7_48, canonicalSolid7_48⟩
  · exact ⟨canonicalPose7_49, canonicalSolid7_49⟩
  · exact ⟨canonicalPose7_50, canonicalSolid7_50⟩
  · exact ⟨canonicalPose7_51, canonicalSolid7_51⟩
  · exact ⟨canonicalPose7_52, canonicalSolid7_52⟩
  · exact ⟨canonicalPose7_53, canonicalSolid7_53⟩
  · exact ⟨canonicalPose7_54, canonicalSolid7_54⟩
  · exact ⟨canonicalPose7_55, canonicalSolid7_55⟩
  · exact ⟨canonicalPose7_56, canonicalSolid7_56⟩
  · exact ⟨canonicalPose7_57, canonicalSolid7_57⟩
  · exact ⟨canonicalPose7_58, canonicalSolid7_58⟩
  · exact ⟨canonicalPose7_59, canonicalSolid7_59⟩
  · exact ⟨canonicalPose7_60, canonicalSolid7_60⟩
  · exact ⟨canonicalPose7_61, canonicalSolid7_61⟩
  · exact ⟨canonicalPose7_62, canonicalSolid7_62⟩
  · exact ⟨canonicalPose7_63, canonicalSolid7_63⟩

#print axioms keys7Chunk1_canonical

end SparseMonotiles.Canonical
