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

def canonicalPose7_64 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, false, true, true, true, false, false], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_64 : BoxKey 7 :=
  ⟨![0, 114240, 67200, 248640, 53760, 100800, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![560, 114688, 66780, 248240, 53375, 101360, 108010], false⟩

theorem canonicalMatch7_64 :
    canonicalPose7_64.boxKey 188160 (referenceBox7 (!canonicalBox7_64.bump)) = canonicalBox7_64 := by decide +kernel

theorem canonicalDecode7_64 : canonicalBox7_64.toKeyData 188160 = keys7Chunk2.get ⟨0, by decide⟩ := by
  change canonicalBox7_64.toKeyData 188160 = ⟨![0, (17 / 28), (5 / 14), (37 / 28), (2 / 7), (15 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(1 / 336), (64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_64 : keySolid (keys7Chunk2.get ⟨0, by decide⟩) = canonicalPose7_64.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_64 (box := canonicalBox7_64) (k := keys7Chunk2.get ⟨0, by decide⟩) (canonicalMatch7_64) (canonicalDecode7_64)

def canonicalPose7_65 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, false, false, false, false], ![0, 0, 0, 1, 0, 0, 0]⟩
def canonicalBox7_65 : BoxKey 7 :=
  ⟨![114240, 0, 120960, 315840, 134400, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, -560, 121380, 316240, 134785, 101360, 108010], true⟩

theorem canonicalMatch7_65 :
    canonicalPose7_65.boxKey 188160 (referenceBox7 (!canonicalBox7_65.bump)) = canonicalBox7_65 := by decide +kernel

theorem canonicalDecode7_65 : canonicalBox7_65.toKeyData 188160 = keys7Chunk2.get ⟨1, by decide⟩ := by
  change canonicalBox7_65.toKeyData 188160 = ⟨![(17 / 28), 0, (9 / 14), (47 / 28), (5 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_65 : keySolid (keys7Chunk2.get ⟨1, by decide⟩) = canonicalPose7_65.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_65 (box := canonicalBox7_65) (k := keys7Chunk2.get ⟨1, by decide⟩) (canonicalMatch7_65) (canonicalDecode7_65)

def canonicalPose7_66 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, true, true, false, false, true], ![1, 0, 0, 2, 0, 0, 1]⟩
def canonicalBox7_66 : BoxKey 7 :=
  ⟨![60480, 120960, 0, 262080, 107520, 100800, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, -560, 261632, 108010, 101360, 53375], true⟩

theorem canonicalMatch7_66 :
    canonicalPose7_66.boxKey 188160 (referenceBox7 (!canonicalBox7_66.bump)) = canonicalBox7_66 := by decide +kernel

theorem canonicalDecode7_66 : canonicalBox7_66.toKeyData 188160 = keys7Chunk2.get ⟨2, by decide⟩ := by
  change canonicalBox7_66.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (181 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_66 : keySolid (keys7Chunk2.get ⟨2, by decide⟩) = canonicalPose7_66.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_66 (box := canonicalBox7_66) (k := keys7Chunk2.get ⟨2, by decide⟩) (canonicalMatch7_66) (canonicalDecode7_66)

def canonicalPose7_67 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, true, true, true, false, false], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_67 : BoxKey 7 :=
  ⟨![100800, 107520, 73920, 376320, 67200, 127680, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 73472, 375760, 66780, 128080, 134785], false⟩

theorem canonicalMatch7_67 :
    canonicalPose7_67.boxKey 188160 (referenceBox7 (!canonicalBox7_67.bump)) = canonicalBox7_67 := by decide +kernel

theorem canonicalDecode7_67 : canonicalBox7_67.toKeyData 188160 = keys7Chunk2.get ⟨3, by decide⟩ := by
  change canonicalBox7_67.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (11 / 28), 2, (5 / 14), (19 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (41 / 105), (671 / 336), (159 / 448), (1601 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_67 : keySolid (keys7Chunk2.get ⟨3, by decide⟩) = canonicalPose7_67.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_67 (box := canonicalBox7_67) (k := keys7Chunk2.get ⟨3, by decide⟩) (canonicalMatch7_67) (canonicalDecode7_67)

def canonicalPose7_68 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, true, false, true, false, false], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_68 : BoxKey 7 :=
  ⟨![134400, 127680, 67200, 376320, 73920, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 128080, 66780, 376880, 73472, 108010, 101360], true⟩

theorem canonicalMatch7_68 :
    canonicalPose7_68.boxKey 188160 (referenceBox7 (!canonicalBox7_68.bump)) = canonicalBox7_68 := by decide +kernel

theorem canonicalDecode7_68 : canonicalBox7_68.toKeyData 188160 = keys7Chunk2.get ⟨4, by decide⟩ := by
  change canonicalBox7_68.toKeyData 188160 = ⟨![(5 / 7), (19 / 28), (5 / 14), 2, (11 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (1601 / 2352), (159 / 448), (673 / 336), (41 / 105), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_68 : keySolid (keys7Chunk2.get ⟨4, by decide⟩) = canonicalPose7_68.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_68 (box := canonicalBox7_68) (k := keys7Chunk2.get ⟨4, by decide⟩) (canonicalMatch7_68) (canonicalDecode7_68)

def canonicalPose7_69 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, false, true, false, false, true], ![1, 0, 0, 2, 0, 0, 1]⟩
def canonicalBox7_69 : BoxKey 7 :=
  ⟨![53760, 100800, 107520, 262080, 0, 120960, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 101360, 108010, 261632, 560, 121380, 60080], false⟩

theorem canonicalMatch7_69 :
    canonicalPose7_69.boxKey 188160 (referenceBox7 (!canonicalBox7_69.bump)) = canonicalBox7_69 := by decide +kernel

theorem canonicalDecode7_69 : canonicalBox7_69.toKeyData 188160 = keys7Chunk2.get ⟨5, by decide⟩ := by
  change canonicalBox7_69.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_69 : keySolid (keys7Chunk2.get ⟨5, by decide⟩) = canonicalPose7_69.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_69 (box := canonicalBox7_69) (k := keys7Chunk2.get ⟨5, by decide⟩) (canonicalMatch7_69) (canonicalDecode7_69)

def canonicalPose7_70 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, false, false, false, false], ![0, 0, 0, 1, 0, 0, 0]⟩
def canonicalBox7_70 : BoxKey 7 :=
  ⟨![107520, 100800, 134400, 315840, 120960, 0, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 134785, 316240, 121380, 560, 114688], false⟩

theorem canonicalMatch7_70 :
    canonicalPose7_70.boxKey 188160 (referenceBox7 (!canonicalBox7_70.bump)) = canonicalBox7_70 := by decide +kernel

theorem canonicalDecode7_70 : canonicalBox7_70.toKeyData 188160 = keys7Chunk2.get ⟨6, by decide⟩ := by
  change canonicalBox7_70.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (5 / 7), (47 / 28), (9 / 14), 0, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_70 : keySolid (keys7Chunk2.get ⟨6, by decide⟩) = canonicalPose7_70.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_70 (box := canonicalBox7_70) (k := keys7Chunk2.get ⟨6, by decide⟩) (canonicalMatch7_70) (canonicalDecode7_70)

def canonicalPose7_71 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, false, true, true, true, false, true], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_71 : BoxKey 7 :=
  ⟨![107520, 100800, 53760, 248640, 67200, 114240, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 101360, 53375, 248240, 66780, 114688, -560], true⟩

theorem canonicalMatch7_71 :
    canonicalPose7_71.boxKey 188160 (referenceBox7 (!canonicalBox7_71.bump)) = canonicalBox7_71 := by decide +kernel

theorem canonicalDecode7_71 : canonicalBox7_71.toKeyData 188160 = keys7Chunk2.get ⟨7, by decide⟩ := by
  change canonicalBox7_71.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (2 / 7), (37 / 28), (5 / 14), (17 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_71 : keySolid (keys7Chunk2.get ⟨7, by decide⟩) = canonicalPose7_71.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_71 (box := canonicalBox7_71) (k := keys7Chunk2.get ⟨7, by decide⟩) (canonicalMatch7_71) (canonicalDecode7_71)

def canonicalPose7_72 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, true, true, true, true], ![0, 0, 0, 2, 1, 1, 2]⟩
def canonicalBox7_72 : BoxKey 7 :=
  ⟨![0, 114240, 107520, 275520, 53760, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 114688, 108010, 274960, 53375, 60080, 254940], false⟩

theorem canonicalMatch7_72 :
    canonicalPose7_72.boxKey 188160 (referenceBox7 (!canonicalBox7_72.bump)) = canonicalBox7_72 := by decide +kernel

theorem canonicalDecode7_72 : canonicalBox7_72.toKeyData 188160 = keys7Chunk2.get ⟨8, by decide⟩ := by
  change canonicalBox7_72.toKeyData 188160 = ⟨![0, (17 / 28), (4 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (64 / 105), (1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_72 : keySolid (keys7Chunk2.get ⟨8, by decide⟩) = canonicalPose7_72.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_72 (box := canonicalBox7_72) (k := keys7Chunk2.get ⟨8, by decide⟩) (canonicalMatch7_72) (canonicalDecode7_72)

def canonicalPose7_73 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, true, false, false, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_73 : BoxKey 7 :=
  ⟨![73920, 0, 67200, 248640, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, -560, 66780, 248240, 134785, 101360, 268310], true⟩

theorem canonicalMatch7_73 :
    canonicalPose7_73.boxKey 188160 (referenceBox7 (!canonicalBox7_73.bump)) = canonicalBox7_73 := by decide +kernel

theorem canonicalDecode7_73 : canonicalBox7_73.toKeyData 188160 = keys7Chunk2.get ⟨9, by decide⟩ := by
  change canonicalBox7_73.toKeyData 188160 = ⟨![(11 / 28), 0, (5 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (-1 / 336), (159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_73 : keySolid (keys7Chunk2.get ⟨9, by decide⟩) = canonicalPose7_73.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_73 (box := canonicalBox7_73) (k := keys7Chunk2.get ⟨9, by decide⟩) (canonicalMatch7_73) (canonicalDecode7_73)

def canonicalPose7_74 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, true, false, false, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_74 : BoxKey 7 :=
  ⟨![67200, 0, 73920, 268800, 100800, 134400, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 560, 73472, 268310, 101360, 134785, 248240], false⟩

theorem canonicalMatch7_74 :
    canonicalPose7_74.boxKey 188160 (referenceBox7 (!canonicalBox7_74.bump)) = canonicalBox7_74 := by decide +kernel

theorem canonicalDecode7_74 : canonicalBox7_74.toKeyData 188160 = keys7Chunk2.get ⟨10, by decide⟩ := by
  change canonicalBox7_74.toKeyData 188160 = ⟨![(5 / 14), 0, (11 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (1 / 336), (41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_74 : keySolid (keys7Chunk2.get ⟨10, by decide⟩) = canonicalPose7_74.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_74 (box := canonicalBox7_74) (k := keys7Chunk2.get ⟨10, by decide⟩) (canonicalMatch7_74) (canonicalDecode7_74)

def canonicalPose7_75 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, true, true, true, true, true], ![0, 0, 0, 2, 1, 1, 2]⟩
def canonicalBox7_75 : BoxKey 7 :=
  ⟨![107520, 114240, 0, 255360, 60480, 53760, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, -560, 254940, 60080, 53375, 274960], true⟩

theorem canonicalMatch7_75 :
    canonicalPose7_75.boxKey 188160 (referenceBox7 (!canonicalBox7_75.bump)) = canonicalBox7_75 := by decide +kernel

theorem canonicalDecode7_75 : canonicalBox7_75.toKeyData 188160 = keys7Chunk2.get ⟨11, by decide⟩ := by
  change canonicalBox7_75.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 0, (19 / 14), (9 / 28), (2 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_75 : keySolid (keys7Chunk2.get ⟨11, by decide⟩) = canonicalPose7_75.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_75 (box := canonicalBox7_75) (k := keys7Chunk2.get ⟨11, by decide⟩) (canonicalMatch7_75) (canonicalDecode7_75)

def canonicalPose7_76 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, false, false, false, false, true], ![0, 1, 0, 2, 0, 0, 2]⟩
def canonicalBox7_76 : BoxKey 7 :=
  ⟨![134400, 60480, 120960, 376320, 114240, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 60080, 121380, 376880, 114688, 108010, 274960], true⟩

theorem canonicalMatch7_76 :
    canonicalPose7_76.boxKey 188160 (referenceBox7 (!canonicalBox7_76.bump)) = canonicalBox7_76 := by decide +kernel

theorem canonicalDecode7_76 : canonicalBox7_76.toKeyData 188160 = keys7Chunk2.get ⟨12, by decide⟩ := by
  change canonicalBox7_76.toKeyData 188160 = ⟨![(5 / 7), (9 / 28), (9 / 14), 2, (17 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (751 / 2352), (289 / 448), (673 / 336), (64 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_76 : keySolid (keys7Chunk2.get ⟨12, by decide⟩) = canonicalPose7_76.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_76 (box := canonicalBox7_76) (k := keys7Chunk2.get ⟨12, by decide⟩) (canonicalMatch7_76) (canonicalDecode7_76)

def canonicalPose7_77 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, false, true, true, false, false, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_77 : BoxKey 7 :=
  ⟨![53760, 127680, 67200, 262080, 0, 107520, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 128080, 66780, 261632, 560, 108010, 274960], false⟩

theorem canonicalMatch7_77 :
    canonicalPose7_77.boxKey 188160 (referenceBox7 (!canonicalBox7_77.bump)) = canonicalBox7_77 := by decide +kernel

theorem canonicalDecode7_77 : canonicalBox7_77.toKeyData 188160 = keys7Chunk2.get ⟨13, by decide⟩ := by
  change canonicalBox7_77.toKeyData 188160 = ⟨![(2 / 7), (19 / 28), (5 / 14), (39 / 28), 0, (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105), (1 / 336), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_77 : keySolid (keys7Chunk2.get ⟨13, by decide⟩) = canonicalPose7_77.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_77 (box := canonicalBox7_77) (k := keys7Chunk2.get ⟨13, by decide⟩) (canonicalMatch7_77) (canonicalDecode7_77)

def canonicalPose7_78 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, false, true, true, false, true, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_78 : BoxKey 7 :=
  ⟨![67200, 127680, 53760, 275520, 107520, 0, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 128080, 53375, 274960, 108010, -560, 261632], true⟩

theorem canonicalMatch7_78 :
    canonicalPose7_78.boxKey 188160 (referenceBox7 (!canonicalBox7_78.bump)) = canonicalBox7_78 := by decide +kernel

theorem canonicalDecode7_78 : canonicalBox7_78.toKeyData 188160 = keys7Chunk2.get ⟨14, by decide⟩ := by
  change canonicalBox7_78.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (2 / 7), (41 / 28), (4 / 7), 0, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_78 : keySolid (keys7Chunk2.get ⟨14, by decide⟩) = canonicalPose7_78.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_78 (box := canonicalBox7_78) (k := keys7Chunk2.get ⟨14, by decide⟩) (canonicalMatch7_78) (canonicalDecode7_78)

def canonicalPose7_79 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, false, true, false, false, true], ![0, 1, 0, 2, 0, 0, 2]⟩
def canonicalBox7_79 : BoxKey 7 :=
  ⟨![120960, 60480, 134400, 275520, 107520, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 60080, 134785, 274960, 108010, 114688, 375760], false⟩

theorem canonicalMatch7_79 :
    canonicalPose7_79.boxKey 188160 (referenceBox7 (!canonicalBox7_79.bump)) = canonicalBox7_79 := by decide +kernel

theorem canonicalDecode7_79 : canonicalBox7_79.toKeyData 188160 = keys7Chunk2.get ⟨15, by decide⟩ := by
  change canonicalBox7_79.toKeyData 188160 = ⟨![(9 / 14), (9 / 28), (5 / 7), (41 / 28), (4 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (751 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_79 : keySolid (keys7Chunk2.get ⟨15, by decide⟩) = canonicalPose7_79.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_79 (box := canonicalBox7_79) (k := keys7Chunk2.get ⟨15, by decide⟩) (canonicalMatch7_79) (canonicalDecode7_79)

def canonicalPose7_80 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, false, false, false, false, false, false], ![0, 0, 0, 1, 0, 1, 0]⟩
def canonicalBox7_80 : BoxKey 7 :=
  ⟨![0, 107520, 100800, 322560, 127680, 309120, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![560, 108010, 101360, 322945, 128080, 309540, 114688], false⟩

theorem canonicalMatch7_80 :
    canonicalPose7_80.boxKey 188160 (referenceBox7 (!canonicalBox7_80.bump)) = canonicalBox7_80 := by decide +kernel

theorem canonicalDecode7_80 : canonicalBox7_80.toKeyData 188160 = keys7Chunk2.get ⟨16, by decide⟩ := by
  change canonicalBox7_80.toKeyData 188160 = ⟨![0, (4 / 7), (15 / 28), (12 / 7), (19 / 28), (23 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_80 : keySolid (keys7Chunk2.get ⟨16, by decide⟩) = canonicalPose7_80.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_80 (box := canonicalBox7_80) (k := keys7Chunk2.get ⟨16, by decide⟩) (canonicalMatch7_80) (canonicalDecode7_80)

def canonicalPose7_81 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, true, false, false, false, false, false], ![0, 0, 0, 1, 0, 1, 0]⟩
def canonicalBox7_81 : BoxKey 7 :=
  ⟨![107520, 0, 114240, 309120, 127680, 322560, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, -560, 114688, 309540, 128080, 322945, 101360], true⟩

theorem canonicalMatch7_81 :
    canonicalPose7_81.boxKey 188160 (referenceBox7 (!canonicalBox7_81.bump)) = canonicalBox7_81 := by decide +kernel

theorem canonicalDecode7_81 : canonicalBox7_81.toKeyData 188160 = keys7Chunk2.get ⟨17, by decide⟩ := by
  change canonicalBox7_81.toKeyData 188160 = ⟨![(4 / 7), 0, (17 / 28), (23 / 14), (19 / 28), (12 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (-1 / 336), (64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_81 : keySolid (keys7Chunk2.get ⟨17, by decide⟩) = canonicalPose7_81.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_81 (box := canonicalBox7_81) (k := keys7Chunk2.get ⟨17, by decide⟩) (canonicalMatch7_81) (canonicalDecode7_81)

def canonicalPose7_82 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, false, true, true, true, false], ![0, 0, 0, 2, 1, 2, 0]⟩
def canonicalBox7_82 : BoxKey 7 :=
  ⟨![107520, 114240, 0, 255360, 60480, 241920, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, 560, 254940, 60080, 241535, 101360], false⟩

theorem canonicalMatch7_82 :
    canonicalPose7_82.boxKey 188160 (referenceBox7 (!canonicalBox7_82.bump)) = canonicalBox7_82 := by decide +kernel

theorem canonicalDecode7_82 : canonicalBox7_82.toKeyData 188160 = keys7Chunk2.get ⟨18, by decide⟩ := by
  change canonicalBox7_82.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 0, (19 / 14), (9 / 28), (9 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (1 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_82 : keySolid (keys7Chunk2.get ⟨18, by decide⟩) = canonicalPose7_82.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_82 (box := canonicalBox7_82) (k := keys7Chunk2.get ⟨18, by decide⟩) (canonicalMatch7_82) (canonicalDecode7_82)

def canonicalPose7_83 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, false, true, false, true, false], ![1, 1, 0, 2, 0, 2, 0]⟩
def canonicalBox7_83 : BoxKey 7 :=
  ⟨![53760, 60480, 120960, 376320, 114240, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 60080, 121380, 375760, 114688, 268310, 101360], false⟩

theorem canonicalMatch7_83 :
    canonicalPose7_83.boxKey 188160 (referenceBox7 (!canonicalBox7_83.bump)) = canonicalBox7_83 := by decide +kernel

theorem canonicalDecode7_83 : canonicalBox7_83.toKeyData 188160 = keys7Chunk2.get ⟨19, by decide⟩ := by
  change canonicalBox7_83.toKeyData 188160 = ⟨![(2 / 7), (9 / 28), (9 / 14), 2, (17 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (751 / 2352), (289 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_83 : keySolid (keys7Chunk2.get ⟨19, by decide⟩) = canonicalPose7_83.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_83 (box := canonicalBox7_83) (k := keys7Chunk2.get ⟨19, by decide⟩) (canonicalMatch7_83) (canonicalDecode7_83)

def canonicalPose7_84 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, false, false, false, false], ![0, 0, 0, 1, 0, 1, 0]⟩
def canonicalBox7_84 : BoxKey 7 :=
  ⟨![100800, 134400, 127680, 309120, 0, 302400, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 128080, 309540, 560, 302848, 108010], false⟩

theorem canonicalMatch7_84 :
    canonicalPose7_84.boxKey 188160 (referenceBox7 (!canonicalBox7_84.bump)) = canonicalBox7_84 := by decide +kernel

theorem canonicalDecode7_84 : canonicalBox7_84.toKeyData 188160 = keys7Chunk2.get ⟨20, by decide⟩ := by
  change canonicalBox7_84.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (19 / 28), (23 / 14), 0, (45 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448), (1 / 336), (169 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_84 : keySolid (keys7Chunk2.get ⟨20, by decide⟩) = canonicalPose7_84.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_84 (box := canonicalBox7_84) (k := keys7Chunk2.get ⟨20, by decide⟩) (canonicalMatch7_84) (canonicalDecode7_84)

def canonicalPose7_85 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, false, true, false, false], ![0, 0, 0, 1, 0, 1, 0]⟩
def canonicalBox7_85 : BoxKey 7 :=
  ⟨![134400, 100800, 107520, 302400, 0, 309120, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 108010, 302848, -560, 309540, 128080], true⟩

theorem canonicalMatch7_85 :
    canonicalPose7_85.boxKey 188160 (referenceBox7 (!canonicalBox7_85.bump)) = canonicalBox7_85 := by decide +kernel

theorem canonicalDecode7_85 : canonicalBox7_85.toKeyData 188160 = keys7Chunk2.get ⟨21, by decide⟩ := by
  change canonicalBox7_85.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (4 / 7), (45 / 28), 0, (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105), (-1 / 336), (737 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_85 : keySolid (keys7Chunk2.get ⟨21, by decide⟩) = canonicalPose7_85.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_85 (box := canonicalBox7_85) (k := keys7Chunk2.get ⟨21, by decide⟩) (canonicalMatch7_85) (canonicalDecode7_85)

def canonicalPose7_86 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, false, true, false, false, false], ![1, 1, 0, 2, 0, 2, 0]⟩
def canonicalBox7_86 : BoxKey 7 :=
  ⟨![60480, 53760, 100800, 268800, 114240, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 53375, 101360, 268310, 114688, 376880, 121380], true⟩

theorem canonicalMatch7_86 :
    canonicalPose7_86.boxKey 188160 (referenceBox7 (!canonicalBox7_86.bump)) = canonicalBox7_86 := by decide +kernel

theorem canonicalDecode7_86 : canonicalBox7_86.toKeyData 188160 = keys7Chunk2.get ⟨22, by decide⟩ := by
  change canonicalBox7_86.toKeyData 188160 = ⟨![(9 / 28), (2 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_86 : keySolid (keys7Chunk2.get ⟨22, by decide⟩) = canonicalPose7_86.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_86 (box := canonicalBox7_86) (k := keys7Chunk2.get ⟨22, by decide⟩) (canonicalMatch7_86) (canonicalDecode7_86)

def canonicalPose7_87 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, true, true, true, true], ![0, 0, 0, 2, 1, 2, 0]⟩
def canonicalBox7_87 : BoxKey 7 :=
  ⟨![114240, 107520, 100800, 241920, 60480, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 101360, 241535, 60080, 254940, -560], true⟩

theorem canonicalMatch7_87 :
    canonicalPose7_87.boxKey 188160 (referenceBox7 (!canonicalBox7_87.bump)) = canonicalBox7_87 := by decide +kernel

theorem canonicalDecode7_87 : canonicalBox7_87.toKeyData 188160 = keys7Chunk2.get ⟨23, by decide⟩ := by
  change canonicalBox7_87.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (15 / 28), (9 / 7), (9 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_87 : keySolid (keys7Chunk2.get ⟨23, by decide⟩) = canonicalPose7_87.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_87 (box := canonicalBox7_87) (k := keys7Chunk2.get ⟨23, by decide⟩) (canonicalMatch7_87) (canonicalDecode7_87)

def canonicalPose7_88 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, true, false, true, false], ![0, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_88 : BoxKey 7 :=
  ⟨![0, 73920, 107520, 275520, 134400, 248640, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 73472, 108010, 274960, 134785, 248240, 309540], true⟩

theorem canonicalMatch7_88 :
    canonicalPose7_88.boxKey 188160 (referenceBox7 (!canonicalBox7_88.bump)) = canonicalBox7_88 := by decide +kernel

theorem canonicalDecode7_88 : canonicalBox7_88.toKeyData 188160 = keys7Chunk2.get ⟨24, by decide⟩ := by
  change canonicalBox7_88.toKeyData 188160 = ⟨![0, (11 / 28), (4 / 7), (41 / 28), (5 / 7), (37 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_88 : keySolid (keys7Chunk2.get ⟨24, by decide⟩) = canonicalPose7_88.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_88 (box := canonicalBox7_88) (k := keys7Chunk2.get ⟨24, by decide⟩) (canonicalMatch7_88) (canonicalDecode7_88)

def canonicalPose7_89 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, false, true, false, true, false], ![0, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_89 : BoxKey 7 :=
  ⟨![0, 67200, 127680, 241920, 100800, 268800, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 66780, 128080, 241535, 101360, 268310, 302848], false⟩

theorem canonicalMatch7_89 :
    canonicalPose7_89.boxKey 188160 (referenceBox7 (!canonicalBox7_89.bump)) = canonicalBox7_89 := by decide +kernel

theorem canonicalDecode7_89 : canonicalBox7_89.toKeyData 188160 = keys7Chunk2.get ⟨25, by decide⟩ := by
  change canonicalBox7_89.toKeyData 188160 = ⟨![0, (5 / 14), (19 / 28), (9 / 7), (15 / 28), (10 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_89 : keySolid (keys7Chunk2.get ⟨25, by decide⟩) = canonicalPose7_89.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_89 (box := canonicalBox7_89) (k := keys7Chunk2.get ⟨25, by decide⟩) (canonicalMatch7_89) (canonicalDecode7_89)

def canonicalPose7_90 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, false, false, true, true, true], ![0, 0, 0, 1, 1, 2, 2]⟩
def canonicalBox7_90 : BoxKey 7 :=
  ⟨![114240, 0, 120960, 315840, 53760, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 560, 121380, 316240, 53375, 274960, 268310], false⟩

theorem canonicalMatch7_90 :
    canonicalPose7_90.boxKey 188160 (referenceBox7 (!canonicalBox7_90.bump)) = canonicalBox7_90 := by decide +kernel

theorem canonicalDecode7_90 : canonicalBox7_90.toKeyData 188160 = keys7Chunk2.get ⟨26, by decide⟩ := by
  change canonicalBox7_90.toKeyData 188160 = ⟨![(17 / 28), 0, (9 / 14), (47 / 28), (2 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_90 : keySolid (keys7Chunk2.get ⟨26, by decide⟩) = canonicalPose7_90.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_90 (box := canonicalBox7_90) (k := keys7Chunk2.get ⟨26, by decide⟩) (canonicalMatch7_90) (canonicalDecode7_90)

def canonicalPose7_91 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, false, true, false, true, true], ![1, 0, 0, 2, 0, 2, 2]⟩
def canonicalBox7_91 : BoxKey 7 :=
  ⟨![60480, 120960, 0, 262080, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, 560, 261632, 108010, 274960, 241535], false⟩

theorem canonicalMatch7_91 :
    canonicalPose7_91.boxKey 188160 (referenceBox7 (!canonicalBox7_91.bump)) = canonicalBox7_91 := by decide +kernel

theorem canonicalDecode7_91 : canonicalBox7_91.toKeyData 188160 = keys7Chunk2.get ⟨27, by decide⟩ := by
  change canonicalBox7_91.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_91 : keySolid (keys7Chunk2.get ⟨27, by decide⟩) = canonicalPose7_91.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_91 (box := canonicalBox7_91) (k := keys7Chunk2.get ⟨27, by decide⟩) (canonicalMatch7_91) (canonicalDecode7_91)

def canonicalPose7_92 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, true, false, false, false, true, false], ![0, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_92 : BoxKey 7 :=
  ⟨![127680, 67200, 114240, 376320, 107520, 275520, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 66780, 114688, 376880, 108010, 274960, 322945], true⟩

theorem canonicalMatch7_92 :
    canonicalPose7_92.boxKey 188160 (referenceBox7 (!canonicalBox7_92.bump)) = canonicalBox7_92 := by decide +kernel

theorem canonicalDecode7_92 : canonicalBox7_92.toKeyData 188160 = keys7Chunk2.get ⟨28, by decide⟩ := by
  change canonicalBox7_92.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), (17 / 28), 2, (4 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (64 / 105), (673 / 336), (1543 / 2688), (491 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_92 : keySolid (keys7Chunk2.get ⟨28, by decide⟩) = canonicalPose7_92.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_92 (box := canonicalBox7_92) (k := keys7Chunk2.get ⟨28, by decide⟩) (canonicalMatch7_92) (canonicalDecode7_92)

def canonicalPose7_93 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, true, false, true, false, true, false], ![0, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_93 : BoxKey 7 :=
  ⟨![127680, 53760, 100800, 268800, 0, 262080, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 53375, 101360, 268310, 560, 261632, 309540], false⟩

theorem canonicalMatch7_93 :
    canonicalPose7_93.boxKey 188160 (referenceBox7 (!canonicalBox7_93.bump)) = canonicalBox7_93 := by decide +kernel

theorem canonicalDecode7_93 : canonicalBox7_93.toKeyData 188160 = keys7Chunk2.get ⟨29, by decide⟩ := by
  change canonicalBox7_93.toKeyData 188160 = ⟨![(19 / 28), (2 / 7), (15 / 28), (10 / 7), 0, (39 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (1 / 336), (146 / 105), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_93 : keySolid (keys7Chunk2.get ⟨29, by decide⟩) = canonicalPose7_93.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_93 (box := canonicalBox7_93) (k := keys7Chunk2.get ⟨29, by decide⟩) (canonicalMatch7_93) (canonicalDecode7_93)

def canonicalPose7_94 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, true, false, false, true], ![1, 0, 0, 2, 0, 2, 2]⟩
def canonicalBox7_94 : BoxKey 7 :=
  ⟨![60480, 134400, 100800, 268800, 114240, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 134785, 101360, 268310, 114688, 376880, 254940], true⟩

theorem canonicalMatch7_94 :
    canonicalPose7_94.boxKey 188160 (referenceBox7 (!canonicalBox7_94.bump)) = canonicalBox7_94 := by decide +kernel

theorem canonicalDecode7_94 : canonicalBox7_94.toKeyData 188160 = keys7Chunk2.get ⟨30, by decide⟩ := by
  change canonicalBox7_94.toKeyData 188160 = ⟨![(9 / 28), (5 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_94 : keySolid (keys7Chunk2.get ⟨30, by decide⟩) = canonicalPose7_94.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_94 (box := canonicalBox7_94) (k := keys7Chunk2.get ⟨30, by decide⟩) (canonicalMatch7_94) (canonicalDecode7_94)

def canonicalPose7_95 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, false, true, true, false], ![0, 0, 0, 1, 1, 2, 2]⟩
def canonicalBox7_95 : BoxKey 7 :=
  ⟨![114240, 107520, 100800, 322560, 60480, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 101360, 322945, 60080, 254940, 376880], true⟩

theorem canonicalMatch7_95 :
    canonicalPose7_95.boxKey 188160 (referenceBox7 (!canonicalBox7_95.bump)) = canonicalBox7_95 := by decide +kernel

theorem canonicalDecode7_95 : canonicalBox7_95.toKeyData 188160 = keys7Chunk2.get ⟨31, by decide⟩ := by
  change canonicalBox7_95.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (15 / 28), (12 / 7), (9 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352), (607 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_95 : keySolid (keys7Chunk2.get ⟨31, by decide⟩) = canonicalPose7_95.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_95 (box := canonicalBox7_95) (k := keys7Chunk2.get ⟨31, by decide⟩) (canonicalMatch7_95) (canonicalDecode7_95)

theorem keys7Chunk2_canonical : ∀ k ∈ keys7Chunk2,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk2, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_64, canonicalSolid7_64⟩
  · exact ⟨canonicalPose7_65, canonicalSolid7_65⟩
  · exact ⟨canonicalPose7_66, canonicalSolid7_66⟩
  · exact ⟨canonicalPose7_67, canonicalSolid7_67⟩
  · exact ⟨canonicalPose7_68, canonicalSolid7_68⟩
  · exact ⟨canonicalPose7_69, canonicalSolid7_69⟩
  · exact ⟨canonicalPose7_70, canonicalSolid7_70⟩
  · exact ⟨canonicalPose7_71, canonicalSolid7_71⟩
  · exact ⟨canonicalPose7_72, canonicalSolid7_72⟩
  · exact ⟨canonicalPose7_73, canonicalSolid7_73⟩
  · exact ⟨canonicalPose7_74, canonicalSolid7_74⟩
  · exact ⟨canonicalPose7_75, canonicalSolid7_75⟩
  · exact ⟨canonicalPose7_76, canonicalSolid7_76⟩
  · exact ⟨canonicalPose7_77, canonicalSolid7_77⟩
  · exact ⟨canonicalPose7_78, canonicalSolid7_78⟩
  · exact ⟨canonicalPose7_79, canonicalSolid7_79⟩
  · exact ⟨canonicalPose7_80, canonicalSolid7_80⟩
  · exact ⟨canonicalPose7_81, canonicalSolid7_81⟩
  · exact ⟨canonicalPose7_82, canonicalSolid7_82⟩
  · exact ⟨canonicalPose7_83, canonicalSolid7_83⟩
  · exact ⟨canonicalPose7_84, canonicalSolid7_84⟩
  · exact ⟨canonicalPose7_85, canonicalSolid7_85⟩
  · exact ⟨canonicalPose7_86, canonicalSolid7_86⟩
  · exact ⟨canonicalPose7_87, canonicalSolid7_87⟩
  · exact ⟨canonicalPose7_88, canonicalSolid7_88⟩
  · exact ⟨canonicalPose7_89, canonicalSolid7_89⟩
  · exact ⟨canonicalPose7_90, canonicalSolid7_90⟩
  · exact ⟨canonicalPose7_91, canonicalSolid7_91⟩
  · exact ⟨canonicalPose7_92, canonicalSolid7_92⟩
  · exact ⟨canonicalPose7_93, canonicalSolid7_93⟩
  · exact ⟨canonicalPose7_94, canonicalSolid7_94⟩
  · exact ⟨canonicalPose7_95, canonicalSolid7_95⟩

#print axioms keys7Chunk2_canonical

end SparseMonotiles.Canonical
