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

def canonicalPose7_0 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, false, false, false, false, true], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_0 : BoxKey 7 :=
  ⟨![0, 73920, 107520, 100800, 134400, 127680, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 73472, 108010, 101360, 134785, 128080, 66780], false⟩

theorem canonicalMatch7_0 :
    canonicalPose7_0.boxKey 188160 (referenceBox7 (!canonicalBox7_0.bump)) = canonicalBox7_0 := by decide

theorem canonicalDecode7_0 : canonicalBox7_0.toKeyData 188160 = keys7Chunk0.get ⟨0, by decide⟩ := by
  change canonicalBox7_0.toKeyData 188160 = ⟨![0, (11 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (41 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_0, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_0, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_0, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_0 : keySolid (keys7Chunk0.get ⟨0, by decide⟩) = canonicalPose7_0.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_0 (box := canonicalBox7_0) (k := keys7Chunk0.get ⟨0, by decide⟩) (canonicalMatch7_0) (canonicalDecode7_0)

def canonicalPose7_1 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_1 : BoxKey 7 :=
  ⟨![0, 67200, 127680, 134400, 100800, 107520, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 66780, 128080, 134785, 101360, 108010, 73472], true⟩

theorem canonicalMatch7_1 :
    canonicalPose7_1.boxKey 188160 (referenceBox7 (!canonicalBox7_1.bump)) = canonicalBox7_1 := by decide

theorem canonicalDecode7_1 : canonicalBox7_1.toKeyData 188160 = keys7Chunk0.get ⟨1, by decide⟩ := by
  change canonicalBox7_1.toKeyData 188160 = ⟨![0, (5 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (159 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_1, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_1, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_1, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_1 : keySolid (keys7Chunk0.get ⟨1, by decide⟩) = canonicalPose7_1.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1 (box := canonicalBox7_1) (k := keys7Chunk0.get ⟨1, by decide⟩) (canonicalMatch7_1) (canonicalDecode7_1)

def canonicalPose7_2 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, true, true, false, false], ![0, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_2 : BoxKey 7 :=
  ⟨![114240, 0, 120960, 60480, 53760, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, -560, 121380, 60080, 53375, 101360, 108010], true⟩

theorem canonicalMatch7_2 :
    canonicalPose7_2.boxKey 188160 (referenceBox7 (!canonicalBox7_2.bump)) = canonicalBox7_2 := by decide

theorem canonicalDecode7_2 : canonicalBox7_2.toKeyData 188160 = keys7Chunk0.get ⟨2, by decide⟩ := by
  change canonicalBox7_2.toKeyData 188160 = ⟨![(17 / 28), 0, (9 / 14), (9 / 28), (2 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (-1 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_2, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_2, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_2, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_2 : keySolid (keys7Chunk0.get ⟨2, by decide⟩) = canonicalPose7_2.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_2 (box := canonicalBox7_2) (k := keys7Chunk0.get ⟨2, by decide⟩) (canonicalMatch7_2) (canonicalDecode7_2)

def canonicalPose7_3 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, true, false, false, false, false], ![1, 0, 0, 0, 0, 0, 0]⟩
def canonicalBox7_3 : BoxKey 7 :=
  ⟨![60480, 120960, 0, 114240, 107520, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, -560, 114688, 108010, 101360, 134785], true⟩

theorem canonicalMatch7_3 :
    canonicalPose7_3.boxKey 188160 (referenceBox7 (!canonicalBox7_3.bump)) = canonicalBox7_3 := by decide

theorem canonicalDecode7_3 : canonicalBox7_3.toKeyData 188160 = keys7Chunk0.get ⟨3, by decide⟩ := by
  change canonicalBox7_3.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (-1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_3, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_3, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_3, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_3 : keySolid (keys7Chunk0.get ⟨3, by decide⟩) = canonicalPose7_3.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_3 (box := canonicalBox7_3) (k := keys7Chunk0.get ⟨3, by decide⟩) (canonicalMatch7_3) (canonicalDecode7_3)

def canonicalPose7_4 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, true, false, false, false, false, true], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_4 : BoxKey 7 :=
  ⟨![127680, 67200, 114240, 0, 107520, 100800, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 66780, 114688, 560, 108010, 101360, 53375], false⟩

theorem canonicalMatch7_4 :
    canonicalPose7_4.boxKey 188160 (referenceBox7 (!canonicalBox7_4.bump)) = canonicalBox7_4 := by decide

theorem canonicalDecode7_4 : canonicalBox7_4.toKeyData 188160 = keys7Chunk0.get ⟨4, by decide⟩ := by
  change canonicalBox7_4.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), (17 / 28), 0, (4 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (64 / 105), (1 / 336), (1543 / 2688), (181 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_4, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_4, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_4, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_4 : keySolid (keys7Chunk0.get ⟨4, by decide⟩) = canonicalPose7_4.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_4 (box := canonicalBox7_4) (k := keys7Chunk0.get ⟨4, by decide⟩) (canonicalMatch7_4) (canonicalDecode7_4)

def canonicalPose7_5 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, true, false, false, true, false, true], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_5 : BoxKey 7 :=
  ⟨![127680, 53760, 100800, 107520, 0, 114240, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 53375, 101360, 108010, -560, 114688, 66780], true⟩

theorem canonicalMatch7_5 :
    canonicalPose7_5.boxKey 188160 (referenceBox7 (!canonicalBox7_5.bump)) = canonicalBox7_5 := by decide

theorem canonicalDecode7_5 : canonicalBox7_5.toKeyData 188160 = keys7Chunk0.get ⟨5, by decide⟩ := by
  change canonicalBox7_5.toKeyData 188160 = ⟨![(19 / 28), (2 / 7), (15 / 28), (4 / 7), 0, (17 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688), (-1 / 336), (64 / 105), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_5, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_5, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_5, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_5 : keySolid (keys7Chunk0.get ⟨5, by decide⟩) = canonicalPose7_5.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_5 (box := canonicalBox7_5) (k := keys7Chunk0.get ⟨5, by decide⟩) (canonicalMatch7_5) (canonicalDecode7_5)

def canonicalPose7_6 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, false, false, false, false], ![1, 0, 0, 0, 0, 0, 0]⟩
def canonicalBox7_6 : BoxKey 7 :=
  ⟨![60480, 134400, 100800, 107520, 114240, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 134785, 101360, 108010, 114688, 560, 121380], false⟩

theorem canonicalMatch7_6 :
    canonicalPose7_6.boxKey 188160 (referenceBox7 (!canonicalBox7_6.bump)) = canonicalBox7_6 := by decide

theorem canonicalDecode7_6 : canonicalBox7_6.toKeyData 188160 = keys7Chunk0.get ⟨6, by decide⟩ := by
  change canonicalBox7_6.toKeyData 188160 = ⟨![(9 / 28), (5 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (1 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_6, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_6, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_6, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_6 : keySolid (keys7Chunk0.get ⟨6, by decide⟩) = canonicalPose7_6.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_6 (box := canonicalBox7_6) (k := keys7Chunk0.get ⟨6, by decide⟩) (canonicalMatch7_6) (canonicalDecode7_6)

def canonicalPose7_7 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, true, true, false, false], ![0, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_7 : BoxKey 7 :=
  ⟨![114240, 107520, 100800, 53760, 60480, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 101360, 53375, 60080, 121380, 560], false⟩

theorem canonicalMatch7_7 :
    canonicalPose7_7.boxKey 188160 (referenceBox7 (!canonicalBox7_7.bump)) = canonicalBox7_7 := by decide

theorem canonicalDecode7_7 : canonicalBox7_7.toKeyData 188160 = keys7Chunk0.get ⟨7, by decide⟩ := by
  change canonicalBox7_7.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_7, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_7, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_7, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_7 : keySolid (keys7Chunk0.get ⟨7, by decide⟩) = canonicalPose7_7.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_7 (box := canonicalBox7_7) (k := keys7Chunk0.get ⟨7, by decide⟩) (canonicalMatch7_7) (canonicalDecode7_7)

def canonicalPose7_8 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, true, true, false, false, true], ![0, 0, 1, 1, 0, 0, 2]⟩
def canonicalBox7_8 : BoxKey 7 :=
  ⟨![0, 120960, 60480, 53760, 100800, 107520, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 121380, 60080, 53375, 101360, 108010, 261632], false⟩

theorem canonicalMatch7_8 :
    canonicalPose7_8.boxKey 188160 (referenceBox7 (!canonicalBox7_8.bump)) = canonicalBox7_8 := by decide

theorem canonicalDecode7_8 : canonicalBox7_8.toKeyData 188160 = keys7Chunk0.get ⟨8, by decide⟩ := by
  change canonicalBox7_8.toKeyData 188160 = ⟨![0, (9 / 14), (9 / 28), (2 / 7), (15 / 28), (4 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_8, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_8, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_8, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_8 : keySolid (keys7Chunk0.get ⟨8, by decide⟩) = canonicalPose7_8.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_8 (box := canonicalBox7_8) (k := keys7Chunk0.get ⟨8, by decide⟩) (canonicalMatch7_8) (canonicalDecode7_8)

def canonicalPose7_9 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 0, 0, 1]⟩
def canonicalBox7_9 : BoxKey 7 :=
  ⟨![120960, 0, 114240, 107520, 100800, 134400, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 560, 114688, 108010, 101360, 134785, 316240], false⟩

theorem canonicalMatch7_9 :
    canonicalPose7_9.boxKey 188160 (referenceBox7 (!canonicalBox7_9.bump)) = canonicalBox7_9 := by decide

theorem canonicalDecode7_9 : canonicalBox7_9.toKeyData 188160 = keys7Chunk0.get ⟨9, by decide⟩ := by
  change canonicalBox7_9.toKeyData 188160 = ⟨![(9 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (5 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_9, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_9, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_9, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_9 : keySolid (keys7Chunk0.get ⟨9, by decide⟩) = canonicalPose7_9.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_9 (box := canonicalBox7_9) (k := keys7Chunk0.get ⟨9, by decide⟩) (canonicalMatch7_9) (canonicalDecode7_9)

def canonicalPose7_10 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, false, true, false, false, true, true], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_10 : BoxKey 7 :=
  ⟨![67200, 114240, 0, 107520, 100800, 53760, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 114688, -560, 108010, 101360, 53375, 248240], true⟩

theorem canonicalMatch7_10 :
    canonicalPose7_10.boxKey 188160 (referenceBox7 (!canonicalBox7_10.bump)) = canonicalBox7_10 := by decide

theorem canonicalDecode7_10 : canonicalBox7_10.toKeyData 188160 = keys7Chunk0.get ⟨10, by decide⟩ := by
  change canonicalBox7_10.toKeyData 188160 = ⟨![(5 / 14), (17 / 28), 0, (4 / 7), (15 / 28), (2 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (64 / 105), (-1 / 336), (1543 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_10, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_10, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_10, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_10 : keySolid (keys7Chunk0.get ⟨10, by decide⟩) = canonicalPose7_10.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_10 (box := canonicalBox7_10) (k := keys7Chunk0.get ⟨10, by decide⟩) (canonicalMatch7_10) (canonicalDecode7_10)

def canonicalPose7_11 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, false, false, false, false, true, true], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_11 : BoxKey 7 :=
  ⟨![53760, 100800, 107520, 0, 114240, 67200, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 101360, 108010, 560, 114688, 66780, 248240], false⟩

theorem canonicalMatch7_11 :
    canonicalPose7_11.boxKey 188160 (referenceBox7 (!canonicalBox7_11.bump)) = canonicalBox7_11 := by decide

theorem canonicalDecode7_11 : canonicalBox7_11.toKeyData 188160 = keys7Chunk0.get ⟨11, by decide⟩ := by
  change canonicalBox7_11.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (4 / 7), 0, (17 / 28), (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (1543 / 2688), (1 / 336), (64 / 105), (159 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_11, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_11, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_11, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_11 : keySolid (keys7Chunk0.get ⟨11, by decide⟩) = canonicalPose7_11.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_11 (box := canonicalBox7_11) (k := keys7Chunk0.get ⟨11, by decide⟩) (canonicalMatch7_11) (canonicalDecode7_11)

def canonicalPose7_12 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, false, true, false, false], ![0, 0, 0, 0, 0, 0, 1]⟩
def canonicalBox7_12 : BoxKey 7 :=
  ⟨![134400, 100800, 107520, 114240, 0, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 108010, 114688, -560, 121380, 316240], true⟩

theorem canonicalMatch7_12 :
    canonicalPose7_12.boxKey 188160 (referenceBox7 (!canonicalBox7_12.bump)) = canonicalBox7_12 := by decide

theorem canonicalDecode7_12 : canonicalBox7_12.toKeyData 188160 = keys7Chunk0.get ⟨12, by decide⟩ := by
  change canonicalBox7_12.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (289 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_12, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_12, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_12, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_12 : keySolid (keys7Chunk0.get ⟨12, by decide⟩) = canonicalPose7_12.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_12 (box := canonicalBox7_12) (k := keys7Chunk0.get ⟨12, by decide⟩) (canonicalMatch7_12) (canonicalDecode7_12)

def canonicalPose7_13 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, true, true, false, true, true], ![0, 0, 1, 1, 0, 0, 2]⟩
def canonicalBox7_13 : BoxKey 7 :=
  ⟨![107520, 100800, 53760, 60480, 120960, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 53375, 60080, 121380, -560, 261632], true⟩

theorem canonicalMatch7_13 :
    canonicalPose7_13.boxKey 188160 (referenceBox7 (!canonicalBox7_13.bump)) = canonicalBox7_13 := by decide

theorem canonicalDecode7_13 : canonicalBox7_13.toKeyData 188160 = keys7Chunk0.get ⟨13, by decide⟩ := by
  change canonicalBox7_13.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_13, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_13, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_13, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_13 : keySolid (keys7Chunk0.get ⟨13, by decide⟩) = canonicalPose7_13.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_13 (box := canonicalBox7_13) (k := keys7Chunk0.get ⟨13, by decide⟩) (canonicalMatch7_13) (canonicalDecode7_13)

def canonicalPose7_14 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, false, false, false, true, false], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_14 : BoxKey 7 :=
  ⟨![73920, 107520, 100800, 134400, 127680, 67200, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 108010, 101360, 134785, 128080, 66780, 376880], true⟩

theorem canonicalMatch7_14 :
    canonicalPose7_14.boxKey 188160 (referenceBox7 (!canonicalBox7_14.bump)) = canonicalBox7_14 := by decide

theorem canonicalDecode7_14 : canonicalBox7_14.toKeyData 188160 = keys7Chunk0.get ⟨14, by decide⟩ := by
  change canonicalBox7_14.toKeyData 188160 = ⟨![(11 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28), (5 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (159 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_14, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_14, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_14, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_14 : keySolid (keys7Chunk0.get ⟨14, by decide⟩) = canonicalPose7_14.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_14 (box := canonicalBox7_14) (k := keys7Chunk0.get ⟨14, by decide⟩) (canonicalMatch7_14) (canonicalDecode7_14)

def canonicalPose7_15 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, false, false, false, true, true], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_15 : BoxKey 7 :=
  ⟨![67200, 127680, 134400, 100800, 107520, 73920, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 128080, 134785, 101360, 108010, 73472, 375760], false⟩

theorem canonicalMatch7_15 :
    canonicalPose7_15.boxKey 188160 (referenceBox7 (!canonicalBox7_15.bump)) = canonicalBox7_15 := by decide

theorem canonicalDecode7_15 : canonicalBox7_15.toKeyData 188160 = keys7Chunk0.get ⟨15, by decide⟩ := by
  change canonicalBox7_15.toKeyData 188160 = ⟨![(5 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7), (11 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (41 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_15, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_15, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_15, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_15 : keySolid (keys7Chunk0.get ⟨15, by decide⟩) = canonicalPose7_15.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_15 (box := canonicalBox7_15) (k := keys7Chunk0.get ⟨15, by decide⟩) (canonicalMatch7_15) (canonicalDecode7_15)

def canonicalPose7_16 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 0, 1, 0]⟩
def canonicalBox7_16 : BoxKey 7 :=
  ⟨![0, 114240, 107520, 100800, 134400, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 114688, 108010, 101360, 134785, 316240, 121380], false⟩

theorem canonicalMatch7_16 :
    canonicalPose7_16.boxKey 188160 (referenceBox7 (!canonicalBox7_16.bump)) = canonicalBox7_16 := by decide

theorem canonicalDecode7_16 : canonicalBox7_16.toKeyData 188160 = keys7Chunk0.get ⟨16, by decide⟩ := by
  change canonicalBox7_16.toKeyData 188160 = ⟨![0, (17 / 28), (4 / 7), (15 / 28), (5 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_16, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_16, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_16, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_16 : keySolid (keys7Chunk0.get ⟨16, by decide⟩) = canonicalPose7_16.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_16 (box := canonicalBox7_16) (k := keys7Chunk0.get ⟨16, by decide⟩) (canonicalMatch7_16) (canonicalDecode7_16)

def canonicalPose7_17 : Pose 7 :=
  ⟨canonicalPerm7_10, ![false, true, false, false, true, true, true], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_17 : BoxKey 7 :=
  ⟨![114240, 0, 107520, 100800, 53760, 248640, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![114688, -560, 108010, 101360, 53375, 248240, 66780], true⟩

theorem canonicalMatch7_17 :
    canonicalPose7_17.boxKey 188160 (referenceBox7 (!canonicalBox7_17.bump)) = canonicalBox7_17 := by decide

theorem canonicalDecode7_17 : canonicalBox7_17.toKeyData 188160 = keys7Chunk0.get ⟨17, by decide⟩ := by
  change canonicalBox7_17.toKeyData 188160 = ⟨![(17 / 28), 0, (4 / 7), (15 / 28), (2 / 7), (37 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(64 / 105), (-1 / 336), (1543 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_17, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_17, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_17, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_17 : keySolid (keys7Chunk0.get ⟨17, by decide⟩) = canonicalPose7_17.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_17 (box := canonicalBox7_17) (k := keys7Chunk0.get ⟨17, by decide⟩) (canonicalMatch7_17) (canonicalDecode7_17)

def canonicalPose7_18 : Pose 7 :=
  ⟨canonicalPerm7_1, ![false, false, false, false, true, true, true], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_18 : BoxKey 7 :=
  ⟨![100800, 107520, 0, 114240, 67200, 248640, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![101360, 108010, 560, 114688, 66780, 248240, 53375], false⟩

theorem canonicalMatch7_18 :
    canonicalPose7_18.boxKey 188160 (referenceBox7 (!canonicalBox7_18.bump)) = canonicalBox7_18 := by decide

theorem canonicalDecode7_18 : canonicalBox7_18.toKeyData 188160 = keys7Chunk0.get ⟨18, by decide⟩ := by
  change canonicalBox7_18.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), 0, (17 / 28), (5 / 14), (37 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (1 / 336), (64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_18, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_18, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_18, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_18 : keySolid (keys7Chunk0.get ⟨18, by decide⟩) = canonicalPose7_18.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_18 (box := canonicalBox7_18) (k := keys7Chunk0.get ⟨18, by decide⟩) (canonicalMatch7_18) (canonicalDecode7_18)

def canonicalPose7_19 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, false, true, false, false, false], ![0, 0, 0, 0, 0, 1, 0]⟩
def canonicalBox7_19 : BoxKey 7 :=
  ⟨![100800, 107520, 114240, 0, 120960, 315840, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 114688, -560, 121380, 316240, 134785], true⟩

theorem canonicalMatch7_19 :
    canonicalPose7_19.boxKey 188160 (referenceBox7 (!canonicalBox7_19.bump)) = canonicalBox7_19 := by decide

theorem canonicalDecode7_19 : canonicalBox7_19.toKeyData 188160 = keys7Chunk0.get ⟨19, by decide⟩ := by
  change canonicalBox7_19.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (17 / 28), 0, (9 / 14), (47 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_19, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_19, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_19, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_19 : keySolid (keys7Chunk0.get ⟨19, by decide⟩) = canonicalPose7_19.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_19 (box := canonicalBox7_19) (k := keys7Chunk0.get ⟨19, by decide⟩) (canonicalMatch7_19) (canonicalDecode7_19)

def canonicalPose7_20 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, true, false, true, true, false], ![0, 1, 1, 0, 0, 2, 0]⟩
def canonicalBox7_20 : BoxKey 7 :=
  ⟨![100800, 53760, 60480, 120960, 0, 262080, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 53375, 60080, 121380, -560, 261632, 108010], true⟩

theorem canonicalMatch7_20 :
    canonicalPose7_20.boxKey 188160 (referenceBox7 (!canonicalBox7_20.bump)) = canonicalBox7_20 := by decide

theorem canonicalDecode7_20 : canonicalBox7_20.toKeyData 188160 = keys7Chunk0.get ⟨20, by decide⟩ := by
  change canonicalBox7_20.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (9 / 28), (9 / 14), 0, (39 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_20, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_20, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_20, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_20 : keySolid (keys7Chunk0.get ⟨20, by decide⟩) = canonicalPose7_20.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_20 (box := canonicalBox7_20) (k := keys7Chunk0.get ⟨20, by decide⟩) (canonicalMatch7_20) (canonicalDecode7_20)

def canonicalPose7_21 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, false, false, true, false, true], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_21 : BoxKey 7 :=
  ⟨![107520, 100800, 134400, 127680, 67200, 376320, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 134785, 128080, 66780, 376880, 73472], true⟩

theorem canonicalMatch7_21 :
    canonicalPose7_21.boxKey 188160 (referenceBox7 (!canonicalBox7_21.bump)) = canonicalBox7_21 := by decide

theorem canonicalDecode7_21 : canonicalBox7_21.toKeyData 188160 = keys7Chunk0.get ⟨21, by decide⟩ := by
  change canonicalBox7_21.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (5 / 7), (19 / 28), (5 / 14), 2, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (159 / 448), (673 / 336), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_21, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_21, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_21, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_21 : keySolid (keys7Chunk0.get ⟨21, by decide⟩) = canonicalPose7_21.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_21 (box := canonicalBox7_21) (k := keys7Chunk0.get ⟨21, by decide⟩) (canonicalMatch7_21) (canonicalDecode7_21)

def canonicalPose7_22 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, false, true, true, true], ![0, 0, 0, 0, 1, 2, 1]⟩
def canonicalBox7_22 : BoxKey 7 :=
  ⟨![127680, 134400, 100800, 107520, 73920, 376320, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![128080, 134785, 101360, 108010, 73472, 375760, 66780], false⟩

theorem canonicalMatch7_22 :
    canonicalPose7_22.boxKey 188160 (referenceBox7 (!canonicalBox7_22.bump)) = canonicalBox7_22 := by decide

theorem canonicalDecode7_22 : canonicalBox7_22.toKeyData 188160 = keys7Chunk0.get ⟨22, by decide⟩ := by
  change canonicalBox7_22.toKeyData 188160 = ⟨![(19 / 28), (5 / 7), (15 / 28), (4 / 7), (11 / 28), 2, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (41 / 105), (671 / 336), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_22, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_22, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_22, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_22 : keySolid (keys7Chunk0.get ⟨22, by decide⟩) = canonicalPose7_22.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_22 (box := canonicalBox7_22) (k := keys7Chunk0.get ⟨22, by decide⟩) (canonicalMatch7_22) (canonicalDecode7_22)

def canonicalPose7_23 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, true, false, false, true, false], ![0, 1, 1, 0, 0, 2, 0]⟩
def canonicalBox7_23 : BoxKey 7 :=
  ⟨![120960, 60480, 53760, 100800, 107520, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 60080, 53375, 101360, 108010, 261632, 560], false⟩

theorem canonicalMatch7_23 :
    canonicalPose7_23.boxKey 188160 (referenceBox7 (!canonicalBox7_23.bump)) = canonicalBox7_23 := by decide

theorem canonicalDecode7_23 : canonicalBox7_23.toKeyData 188160 = keys7Chunk0.get ⟨23, by decide⟩ := by
  change canonicalBox7_23.toKeyData 188160 = ⟨![(9 / 14), (9 / 28), (2 / 7), (15 / 28), (4 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_23, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_23, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_23, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_23 : keySolid (keys7Chunk0.get ⟨23, by decide⟩) = canonicalPose7_23.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_23 (box := canonicalBox7_23) (k := keys7Chunk0.get ⟨23, by decide⟩) (canonicalMatch7_23) (canonicalDecode7_23)

def canonicalPose7_24 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, true, false, false, true, true], ![0, 0, 1, 0, 0, 2, 2]⟩
def canonicalBox7_24 : BoxKey 7 :=
  ⟨![0, 120960, 60480, 134400, 100800, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 121380, 60080, 134785, 101360, 268310, 261632], false⟩

theorem canonicalMatch7_24 :
    canonicalPose7_24.boxKey 188160 (referenceBox7 (!canonicalBox7_24.bump)) = canonicalBox7_24 := by decide

theorem canonicalDecode7_24 : canonicalBox7_24.toKeyData 188160 = keys7Chunk0.get ⟨24, by decide⟩ := by
  change canonicalBox7_24.toKeyData 188160 = ⟨![0, (9 / 14), (9 / 28), (5 / 7), (15 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_24, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_24, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_24, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_24 : keySolid (keys7Chunk0.get ⟨24, by decide⟩) = canonicalPose7_24.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_24 (box := canonicalBox7_24) (k := keys7Chunk0.get ⟨24, by decide⟩) (canonicalMatch7_24) (canonicalDecode7_24)

def canonicalPose7_25 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, false, false, false, false], ![0, 0, 0, 0, 0, 1, 1]⟩
def canonicalBox7_25 : BoxKey 7 :=
  ⟨![120960, 0, 114240, 107520, 100800, 322560, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 560, 114688, 108010, 101360, 322945, 316240], false⟩

theorem canonicalMatch7_25 :
    canonicalPose7_25.boxKey 188160 (referenceBox7 (!canonicalBox7_25.bump)) = canonicalBox7_25 := by decide

theorem canonicalDecode7_25 : canonicalBox7_25.toKeyData 188160 = keys7Chunk0.get ⟨25, by decide⟩ := by
  change canonicalBox7_25.toKeyData 188160 = ⟨![(9 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (12 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_25, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_25, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_25, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_25 : keySolid (keys7Chunk0.get ⟨25, by decide⟩) = canonicalPose7_25.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_25 (box := canonicalBox7_25) (k := keys7Chunk0.get ⟨25, by decide⟩) (canonicalMatch7_25) (canonicalDecode7_25)

def canonicalPose7_26 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, true, true, false, true, true], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_26 : BoxKey 7 :=
  ⟨![107520, 73920, 0, 67200, 127680, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 73472, -560, 66780, 128080, 241535, 274960], true⟩

theorem canonicalMatch7_26 :
    canonicalPose7_26.boxKey 188160 (referenceBox7 (!canonicalBox7_26.bump)) = canonicalBox7_26 := by decide

theorem canonicalDecode7_26 : canonicalBox7_26.toKeyData 188160 = keys7Chunk0.get ⟨26, by decide⟩ := by
  change canonicalBox7_26.toKeyData 188160 = ⟨![(4 / 7), (11 / 28), 0, (5 / 14), (19 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (41 / 105), (-1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_26, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_26, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_26, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_26 : keySolid (keys7Chunk0.get ⟨26, by decide⟩) = canonicalPose7_26.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_26 (box := canonicalBox7_26) (k := keys7Chunk0.get ⟨26, by decide⟩) (canonicalMatch7_26) (canonicalDecode7_26)

def canonicalPose7_27 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, false, true, false, true, true], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_27 : BoxKey 7 :=
  ⟨![127680, 67200, 0, 73920, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 66780, 560, 73472, 108010, 274960, 241535], false⟩

theorem canonicalMatch7_27 :
    canonicalPose7_27.boxKey 188160 (referenceBox7 (!canonicalBox7_27.bump)) = canonicalBox7_27 := by decide

theorem canonicalDecode7_27 : canonicalBox7_27.toKeyData 188160 = keys7Chunk0.get ⟨27, by decide⟩ := by
  change canonicalBox7_27.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), 0, (11 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (1 / 336), (41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_27, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_27, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_27, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_27 : keySolid (keys7Chunk0.get ⟨27, by decide⟩) = canonicalPose7_27.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_27 (box := canonicalBox7_27) (k := keys7Chunk0.get ⟨27, by decide⟩) (canonicalMatch7_27) (canonicalDecode7_27)

def canonicalPose7_28 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, false, true, false, false, false], ![0, 0, 0, 0, 0, 1, 1]⟩
def canonicalBox7_28 : BoxKey 7 :=
  ⟨![100800, 107520, 114240, 0, 120960, 315840, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 114688, -560, 121380, 316240, 322945], true⟩

theorem canonicalMatch7_28 :
    canonicalPose7_28.boxKey 188160 (referenceBox7 (!canonicalBox7_28.bump)) = canonicalBox7_28 := by decide

theorem canonicalDecode7_28 : canonicalBox7_28.toKeyData 188160 = keys7Chunk0.get ⟨28, by decide⟩ := by
  change canonicalBox7_28.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (17 / 28), 0, (9 / 14), (47 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_28, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_28, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_28, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_28 : keySolid (keys7Chunk0.get ⟨28, by decide⟩) = canonicalPose7_28.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_28 (box := canonicalBox7_28) (k := keys7Chunk0.get ⟨28, by decide⟩) (canonicalMatch7_28) (canonicalDecode7_28)

def canonicalPose7_29 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, false, true, true, true], ![0, 0, 1, 0, 0, 2, 2]⟩
def canonicalBox7_29 : BoxKey 7 :=
  ⟨![100800, 134400, 60480, 120960, 0, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 60080, 121380, -560, 261632, 268310], true⟩

theorem canonicalMatch7_29 :
    canonicalPose7_29.boxKey 188160 (referenceBox7 (!canonicalBox7_29.bump)) = canonicalBox7_29 := by decide

theorem canonicalDecode7_29 : canonicalBox7_29.toKeyData 188160 = keys7Chunk0.get ⟨29, by decide⟩ := by
  change canonicalBox7_29.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (9 / 28), (9 / 14), 0, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (-1 / 336), (146 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_29, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_29, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_29, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_29 : keySolid (keys7Chunk0.get ⟨29, by decide⟩) = canonicalPose7_29.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_29 (box := canonicalBox7_29) (k := keys7Chunk0.get ⟨29, by decide⟩) (canonicalMatch7_29) (canonicalDecode7_29)

def canonicalPose7_30 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, true, false, true, false, true, true], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_30 : BoxKey 7 :=
  ⟨![100800, 53760, 127680, 67200, 114240, 376320, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 53375, 128080, 66780, 114688, 375760, 268310], false⟩

theorem canonicalMatch7_30 :
    canonicalPose7_30.boxKey 188160 (referenceBox7 (!canonicalBox7_30.bump)) = canonicalBox7_30 := by decide

theorem canonicalDecode7_30 : canonicalBox7_30.toKeyData 188160 = keys7Chunk0.get ⟨30, by decide⟩ := by
  change canonicalBox7_30.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (19 / 28), (5 / 14), (17 / 28), 2, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (64 / 105), (671 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_30, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_30, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_30, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_30 : keySolid (keys7Chunk0.get ⟨30, by decide⟩) = canonicalPose7_30.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_30 (box := canonicalBox7_30) (k := keys7Chunk0.get ⟨30, by decide⟩) (canonicalMatch7_30) (canonicalDecode7_30)

def canonicalPose7_31 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, true, false, true, false, true, false], ![0, 1, 0, 1, 0, 2, 2]⟩
def canonicalBox7_31 : BoxKey 7 :=
  ⟨![114240, 67200, 127680, 53760, 100800, 268800, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 66780, 128080, 53375, 101360, 268310, 376880], true⟩

theorem canonicalMatch7_31 :
    canonicalPose7_31.boxKey 188160 (referenceBox7 (!canonicalBox7_31.bump)) = canonicalBox7_31 := by decide

theorem canonicalDecode7_31 : canonicalBox7_31.toKeyData 188160 = keys7Chunk0.get ⟨31, by decide⟩ := by
  change canonicalBox7_31.toKeyData 188160 = ⟨![(17 / 28), (5 / 14), (19 / 28), (2 / 7), (15 / 28), (10 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_31, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_31, BoxKey.toKeyData, rationalVertex]
  · intro i
    fin_cases i <;> norm_num [canonicalBox7_31, BoxKey.toKeyData, rationalVertex]
  · rfl

theorem canonicalSolid7_31 : keySolid (keys7Chunk0.get ⟨31, by decide⟩) = canonicalPose7_31.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_31 (box := canonicalBox7_31) (k := keys7Chunk0.get ⟨31, by decide⟩) (canonicalMatch7_31) (canonicalDecode7_31)

theorem keys7Chunk0_canonical : ∀ k ∈ keys7Chunk0,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_0, canonicalSolid7_0⟩
  · exact ⟨canonicalPose7_1, canonicalSolid7_1⟩
  · exact ⟨canonicalPose7_2, canonicalSolid7_2⟩
  · exact ⟨canonicalPose7_3, canonicalSolid7_3⟩
  · exact ⟨canonicalPose7_4, canonicalSolid7_4⟩
  · exact ⟨canonicalPose7_5, canonicalSolid7_5⟩
  · exact ⟨canonicalPose7_6, canonicalSolid7_6⟩
  · exact ⟨canonicalPose7_7, canonicalSolid7_7⟩
  · exact ⟨canonicalPose7_8, canonicalSolid7_8⟩
  · exact ⟨canonicalPose7_9, canonicalSolid7_9⟩
  · exact ⟨canonicalPose7_10, canonicalSolid7_10⟩
  · exact ⟨canonicalPose7_11, canonicalSolid7_11⟩
  · exact ⟨canonicalPose7_12, canonicalSolid7_12⟩
  · exact ⟨canonicalPose7_13, canonicalSolid7_13⟩
  · exact ⟨canonicalPose7_14, canonicalSolid7_14⟩
  · exact ⟨canonicalPose7_15, canonicalSolid7_15⟩
  · exact ⟨canonicalPose7_16, canonicalSolid7_16⟩
  · exact ⟨canonicalPose7_17, canonicalSolid7_17⟩
  · exact ⟨canonicalPose7_18, canonicalSolid7_18⟩
  · exact ⟨canonicalPose7_19, canonicalSolid7_19⟩
  · exact ⟨canonicalPose7_20, canonicalSolid7_20⟩
  · exact ⟨canonicalPose7_21, canonicalSolid7_21⟩
  · exact ⟨canonicalPose7_22, canonicalSolid7_22⟩
  · exact ⟨canonicalPose7_23, canonicalSolid7_23⟩
  · exact ⟨canonicalPose7_24, canonicalSolid7_24⟩
  · exact ⟨canonicalPose7_25, canonicalSolid7_25⟩
  · exact ⟨canonicalPose7_26, canonicalSolid7_26⟩
  · exact ⟨canonicalPose7_27, canonicalSolid7_27⟩
  · exact ⟨canonicalPose7_28, canonicalSolid7_28⟩
  · exact ⟨canonicalPose7_29, canonicalSolid7_29⟩
  · exact ⟨canonicalPose7_30, canonicalSolid7_30⟩
  · exact ⟨canonicalPose7_31, canonicalSolid7_31⟩

#print axioms keys7Chunk0_canonical

end SparseMonotiles.Canonical
