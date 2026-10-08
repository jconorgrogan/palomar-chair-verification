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

def canonicalPose7_800 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, false, false, true, true, false], ![1, 2, 0, 0, 0, 2, 1]⟩
def canonicalBox7_800 : BoxKey 7 :=
  ⟨![322560, 275520, 107520, 114240, 0, 255360, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 274960, 108010, 114688, -560, 254940, 316240], true⟩

theorem canonicalMatch7_800 :
    canonicalPose7_800.boxKey 188160 (referenceBox7 (!canonicalBox7_800.bump)) = canonicalBox7_800 := by decide +kernel

theorem canonicalDecode7_800 : canonicalBox7_800.toKeyData 188160 = keys7Chunk25.get ⟨0, by decide⟩ := by
  change canonicalBox7_800.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_800 : keySolid (keys7Chunk25.get ⟨0, by decide⟩) = canonicalPose7_800.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_800 (box := canonicalBox7_800) (k := keys7Chunk25.get ⟨0, by decide⟩) (canonicalMatch7_800) (canonicalDecode7_800)

def canonicalPose7_801 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, false, true, false, false, true], ![2, 2, 0, 1, 0, 2, 2]⟩
def canonicalBox7_801 : BoxKey 7 :=
  ⟨![268800, 275520, 134400, 60480, 120960, 376320, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 134785, 60080, 121380, 376880, 261632], true⟩

theorem canonicalMatch7_801 :
    canonicalPose7_801.boxKey 188160 (referenceBox7 (!canonicalBox7_801.bump)) = canonicalBox7_801 := by decide +kernel

theorem canonicalDecode7_801 : canonicalBox7_801.toKeyData 188160 = keys7Chunk25.get ⟨1, by decide⟩ := by
  change canonicalBox7_801.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (5 / 7), (9 / 28), (9 / 14), 2, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (673 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_801 : keySolid (keys7Chunk25.get ⟨1, by decide⟩) = canonicalPose7_801.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_801 (box := canonicalBox7_801) (k := keys7Chunk25.get ⟨1, by decide⟩) (canonicalMatch7_801) (canonicalDecode7_801)

def canonicalPose7_802 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, true, true, false, true, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_802 : BoxKey 7 :=
  ⟨![268800, 275520, 53760, 127680, 67200, 262080, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 274960, 53375, 128080, 66780, 261632, 375760], false⟩

theorem canonicalMatch7_802 :
    canonicalPose7_802.boxKey 188160 (referenceBox7 (!canonicalBox7_802.bump)) = canonicalBox7_802 := by decide +kernel

theorem canonicalDecode7_802 : canonicalBox7_802.toKeyData 188160 = keys7Chunk25.get ⟨2, by decide⟩ := by
  change canonicalBox7_802.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (2 / 7), (19 / 28), (5 / 14), (39 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_802 : keySolid (keys7Chunk25.get ⟨2, by decide⟩) = canonicalPose7_802.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_802 (box := canonicalBox7_802) (k := keys7Chunk25.get ⟨2, by decide⟩) (canonicalMatch7_802) (canonicalDecode7_802)

def canonicalPose7_803 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, true, false, true, true, true, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_803 : BoxKey 7 :=
  ⟨![376320, 268800, 100800, 53760, 248640, 67200, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![376880, 268310, 101360, 53375, 248240, 66780, 114688], true⟩

theorem canonicalMatch7_803 :
    canonicalPose7_803.boxKey 188160 (referenceBox7 (!canonicalBox7_803.bump)) = canonicalBox7_803 := by decide +kernel

theorem canonicalDecode7_803 : canonicalBox7_803.toKeyData 188160 = keys7Chunk25.get ⟨3, by decide⟩ := by
  change canonicalBox7_803.toKeyData 188160 = ⟨![2, (10 / 7), (15 / 28), (2 / 7), (37 / 28), (5 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(673 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_803 : keySolid (keys7Chunk25.get ⟨3, by decide⟩) = canonicalPose7_803.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_803 (box := canonicalBox7_803) (k := keys7Chunk25.get ⟨3, by decide⟩) (canonicalMatch7_803) (canonicalDecode7_803)

def canonicalPose7_804 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, true, false, true, true, true, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_804 : BoxKey 7 :=
  ⟨![268800, 376320, 114240, 67200, 248640, 53760, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 375760, 114688, 66780, 248240, 53375, 101360], false⟩

theorem canonicalMatch7_804 :
    canonicalPose7_804.boxKey 188160 (referenceBox7 (!canonicalBox7_804.bump)) = canonicalBox7_804 := by decide +kernel

theorem canonicalDecode7_804 : canonicalBox7_804.toKeyData 188160 = keys7Chunk25.get ⟨4, by decide⟩ := by
  change canonicalBox7_804.toKeyData 188160 = ⟨![(10 / 7), 2, (17 / 28), (5 / 14), (37 / 28), (2 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (671 / 336), (64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_804 : keySolid (keys7Chunk25.get ⟨4, by decide⟩) = canonicalPose7_804.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_804 (box := canonicalBox7_804) (k := keys7Chunk25.get ⟨4, by decide⟩) (canonicalMatch7_804) (canonicalDecode7_804)

def canonicalPose7_805 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, false, false, false, false], ![2, 2, 0, 0, 1, 0, 0]⟩
def canonicalBox7_805 : BoxKey 7 :=
  ⟨![268800, 262080, 0, 120960, 315840, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, -560, 121380, 316240, 134785, 101360], true⟩

theorem canonicalMatch7_805 :
    canonicalPose7_805.boxKey 188160 (referenceBox7 (!canonicalBox7_805.bump)) = canonicalBox7_805 := by decide +kernel

theorem canonicalDecode7_805 : canonicalBox7_805.toKeyData 188160 = keys7Chunk25.get ⟨5, by decide⟩ := by
  change canonicalBox7_805.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_805 : keySolid (keys7Chunk25.get ⟨5, by decide⟩) = canonicalPose7_805.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_805 (box := canonicalBox7_805) (k := keys7Chunk25.get ⟨5, by decide⟩) (canonicalMatch7_805) (canonicalDecode7_805)

def canonicalPose7_806 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, true, true, false, false], ![1, 1, 0, 0, 2, 0, 0]⟩
def canonicalBox7_806 : BoxKey 7 :=
  ⟨![322560, 315840, 120960, 0, 262080, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 316240, 121380, -560, 261632, 108010, 101360], true⟩

theorem canonicalMatch7_806 :
    canonicalPose7_806.boxKey 188160 (referenceBox7 (!canonicalBox7_806.bump)) = canonicalBox7_806 := by decide +kernel

theorem canonicalDecode7_806 : canonicalBox7_806.toKeyData 188160 = keys7Chunk25.get ⟨6, by decide⟩ := by
  change canonicalBox7_806.toKeyData 188160 = ⟨![(12 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_806 : keySolid (keys7Chunk25.get ⟨6, by decide⟩) = canonicalPose7_806.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_806 (box := canonicalBox7_806) (k := keys7Chunk25.get ⟨6, by decide⟩) (canonicalMatch7_806) (canonicalDecode7_806)

def canonicalPose7_807 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, true, false, true, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_807 : BoxKey 7 :=
  ⟨![275520, 241920, 127680, 67200, 376320, 73920, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 128080, 66780, 376880, 73472, 108010], true⟩

theorem canonicalMatch7_807 :
    canonicalPose7_807.boxKey 188160 (referenceBox7 (!canonicalBox7_807.bump)) = canonicalBox7_807 := by decide +kernel

theorem canonicalDecode7_807 : canonicalBox7_807.toKeyData 188160 = keys7Chunk25.get ⟨7, by decide⟩ := by
  change canonicalBox7_807.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (19 / 28), (5 / 14), 2, (11 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (673 / 336), (41 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_807 : keySolid (keys7Chunk25.get ⟨7, by decide⟩) = canonicalPose7_807.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_807 (box := canonicalBox7_807) (k := keys7Chunk25.get ⟨7, by decide⟩) (canonicalMatch7_807) (canonicalDecode7_807)

def canonicalPose7_808 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, true, true, true, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_808 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 73920, 376320, 67200, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 73472, 375760, 66780, 128080], false⟩

theorem canonicalMatch7_808 :
    canonicalPose7_808.boxKey 188160 (referenceBox7 (!canonicalBox7_808.bump)) = canonicalBox7_808 := by decide +kernel

theorem canonicalDecode7_808 : canonicalBox7_808.toKeyData 188160 = keys7Chunk25.get ⟨8, by decide⟩ := by
  change canonicalBox7_808.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (11 / 28), 2, (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (671 / 336), (159 / 448), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_808 : keySolid (keys7Chunk25.get ⟨8, by decide⟩) = canonicalPose7_808.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_808 (box := canonicalBox7_808) (k := keys7Chunk25.get ⟨8, by decide⟩) (canonicalMatch7_808) (canonicalDecode7_808)

def canonicalPose7_809 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, false, true, false, false], ![1, 1, 0, 0, 2, 0, 0]⟩
def canonicalBox7_809 : BoxKey 7 :=
  ⟨![315840, 322560, 100800, 107520, 262080, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 322945, 101360, 108010, 261632, 560, 121380], false⟩

theorem canonicalMatch7_809 :
    canonicalPose7_809.boxKey 188160 (referenceBox7 (!canonicalBox7_809.bump)) = canonicalBox7_809 := by decide +kernel

theorem canonicalDecode7_809 : canonicalBox7_809.toKeyData 188160 = keys7Chunk25.get ⟨9, by decide⟩ := by
  change canonicalBox7_809.toKeyData 188160 = ⟨![(47 / 28), (12 / 7), (15 / 28), (4 / 7), (39 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_809 : keySolid (keys7Chunk25.get ⟨9, by decide⟩) = canonicalPose7_809.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_809 (box := canonicalBox7_809) (k := keys7Chunk25.get ⟨9, by decide⟩) (canonicalMatch7_809) (canonicalDecode7_809)

def canonicalPose7_810 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, false, false, false, false], ![2, 2, 0, 0, 1, 0, 0]⟩
def canonicalBox7_810 : BoxKey 7 :=
  ⟨![262080, 268800, 100800, 134400, 315840, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 101360, 134785, 316240, 121380, 560], false⟩

theorem canonicalMatch7_810 :
    canonicalPose7_810.boxKey 188160 (referenceBox7 (!canonicalBox7_810.bump)) = canonicalBox7_810 := by decide +kernel

theorem canonicalDecode7_810 : canonicalBox7_810.toKeyData 188160 = keys7Chunk25.get ⟨10, by decide⟩ := by
  change canonicalBox7_810.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (15 / 28), (5 / 7), (47 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_810 : keySolid (keys7Chunk25.get ⟨10, by decide⟩) = canonicalPose7_810.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_810 (box := canonicalBox7_810) (k := keys7Chunk25.get ⟨10, by decide⟩) (canonicalMatch7_810) (canonicalDecode7_810)

def canonicalPose7_811 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, false, false, true, true], ![2, 2, 0, 0, 1, 1, 2]⟩
def canonicalBox7_811 : BoxKey 7 :=
  ⟨![376320, 262080, 107520, 100800, 322560, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 261632, 108010, 101360, 322945, 60080, 254940], false⟩

theorem canonicalMatch7_811 :
    canonicalPose7_811.boxKey 188160 (referenceBox7 (!canonicalBox7_811.bump)) = canonicalBox7_811 := by decide +kernel

theorem canonicalDecode7_811 : canonicalBox7_811.toKeyData 188160 = keys7Chunk25.get ⟨11, by decide⟩ := by
  change canonicalBox7_811.toKeyData 188160 = ⟨![2, (39 / 28), (4 / 7), (15 / 28), (12 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_811 : keySolid (keys7Chunk25.get ⟨11, by decide⟩) = canonicalPose7_811.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_811 (box := canonicalBox7_811) (k := keys7Chunk25.get ⟨11, by decide⟩) (canonicalMatch7_811) (canonicalDecode7_811)

def canonicalPose7_812 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, true, false, true, false, true], ![1, 2, 1, 0, 2, 0, 2]⟩
def canonicalBox7_812 : BoxKey 7 :=
  ⟨![302400, 376320, 67200, 127680, 241920, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, 376880, 66780, 128080, 241535, 101360, 268310], true⟩

theorem canonicalMatch7_812 :
    canonicalPose7_812.boxKey 188160 (referenceBox7 (!canonicalBox7_812.bump)) = canonicalBox7_812 := by decide +kernel

theorem canonicalDecode7_812 : canonicalBox7_812.toKeyData 188160 = keys7Chunk25.get ⟨12, by decide⟩ := by
  change canonicalBox7_812.toKeyData 188160 = ⟨![(45 / 28), 2, (5 / 14), (19 / 28), (9 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (673 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_812 : keySolid (keys7Chunk25.get ⟨12, by decide⟩) = canonicalPose7_812.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_812 (box := canonicalBox7_812) (k := keys7Chunk25.get ⟨12, by decide⟩) (canonicalMatch7_812) (canonicalDecode7_812)

def canonicalPose7_813 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, true, false, true, false, true], ![1, 2, 1, 0, 2, 0, 2]⟩
def canonicalBox7_813 : BoxKey 7 :=
  ⟨![309120, 376320, 73920, 107520, 275520, 134400, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 375760, 73472, 108010, 274960, 134785, 248240], false⟩

theorem canonicalMatch7_813 :
    canonicalPose7_813.boxKey 188160 (referenceBox7 (!canonicalBox7_813.bump)) = canonicalBox7_813 := by decide +kernel

theorem canonicalDecode7_813 : canonicalBox7_813.toKeyData 188160 = keys7Chunk25.get ⟨13, by decide⟩ := by
  change canonicalBox7_813.toKeyData 188160 = ⟨![(23 / 14), 2, (11 / 28), (4 / 7), (41 / 28), (5 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (671 / 336), (41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_813 : keySolid (keys7Chunk25.get ⟨13, by decide⟩) = canonicalPose7_813.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_813 (box := canonicalBox7_813) (k := keys7Chunk25.get ⟨13, by decide⟩) (canonicalMatch7_813) (canonicalDecode7_813)

def canonicalPose7_814 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, false, false, true, true], ![2, 2, 0, 0, 1, 1, 2]⟩
def canonicalBox7_814 : BoxKey 7 :=
  ⟨![268800, 262080, 0, 120960, 315840, 53760, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, -560, 121380, 316240, 53375, 274960], true⟩

theorem canonicalMatch7_814 :
    canonicalPose7_814.boxKey 188160 (referenceBox7 (!canonicalBox7_814.bump)) = canonicalBox7_814 := by decide +kernel

theorem canonicalDecode7_814 : canonicalBox7_814.toKeyData 188160 = keys7Chunk25.get ⟨14, by decide⟩ := by
  change canonicalBox7_814.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (2 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_814 : keySolid (keys7Chunk25.get ⟨14, by decide⟩) = canonicalPose7_814.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_814 (box := canonicalBox7_814) (k := keys7Chunk25.get ⟨14, by decide⟩) (canonicalMatch7_814) (canonicalDecode7_814)

def canonicalPose7_815 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, false, true, true, false, true], ![2, 1, 0, 0, 2, 0, 2]⟩
def canonicalBox7_815 : BoxKey 7 :=
  ⟨![241920, 315840, 120960, 0, 262080, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 316240, 121380, -560, 261632, 108010, 274960], true⟩

theorem canonicalMatch7_815 :
    canonicalPose7_815.boxKey 188160 (referenceBox7 (!canonicalBox7_815.bump)) = canonicalBox7_815 := by decide +kernel

theorem canonicalDecode7_815 : canonicalBox7_815.toKeyData 188160 = keys7Chunk25.get ⟨15, by decide⟩ := by
  change canonicalBox7_815.toKeyData 188160 = ⟨![(9 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_815 : keySolid (keys7Chunk25.get ⟨15, by decide⟩) = canonicalPose7_815.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_815 (box := canonicalBox7_815) (k := keys7Chunk25.get ⟨15, by decide⟩) (canonicalMatch7_815) (canonicalDecode7_815)

def canonicalPose7_816 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, true, true, false, true, false, true], ![1, 2, 1, 0, 2, 0, 2]⟩
def canonicalBox7_816 : BoxKey 7 :=
  ⟨![322560, 248640, 67200, 114240, 376320, 107520, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 248240, 66780, 114688, 375760, 108010, 274960], false⟩

theorem canonicalMatch7_816 :
    canonicalPose7_816.boxKey 188160 (referenceBox7 (!canonicalBox7_816.bump)) = canonicalBox7_816 := by decide +kernel

theorem canonicalDecode7_816 : canonicalBox7_816.toKeyData 188160 = keys7Chunk25.get ⟨16, by decide⟩ := by
  change canonicalBox7_816.toKeyData 188160 = ⟨![(12 / 7), (37 / 28), (5 / 14), (17 / 28), 2, (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (671 / 336), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_816 : keySolid (keys7Chunk25.get ⟨16, by decide⟩) = canonicalPose7_816.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_816 (box := canonicalBox7_816) (k := keys7Chunk25.get ⟨16, by decide⟩) (canonicalMatch7_816) (canonicalDecode7_816)

def canonicalPose7_817 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, true, true, false, true, true, true], ![1, 2, 1, 0, 2, 0, 2]⟩
def canonicalBox7_817 : BoxKey 7 :=
  ⟨![309120, 248640, 53760, 100800, 268800, 0, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 248240, 53375, 101360, 268310, -560, 261632], true⟩

theorem canonicalMatch7_817 :
    canonicalPose7_817.boxKey 188160 (referenceBox7 (!canonicalBox7_817.bump)) = canonicalBox7_817 := by decide +kernel

theorem canonicalDecode7_817 : canonicalBox7_817.toKeyData 188160 = keys7Chunk25.get ⟨17, by decide⟩ := by
  change canonicalBox7_817.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (2 / 7), (15 / 28), (10 / 7), 0, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_817 : keySolid (keys7Chunk25.get ⟨17, by decide⟩) = canonicalPose7_817.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_817 (box := canonicalBox7_817) (k := keys7Chunk25.get ⟨17, by decide⟩) (canonicalMatch7_817) (canonicalDecode7_817)

def canonicalPose7_818 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, false, false, true, false, true], ![2, 1, 0, 0, 2, 0, 2]⟩
def canonicalBox7_818 : BoxKey 7 :=
  ⟨![255360, 315840, 134400, 100800, 268800, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 316240, 134785, 101360, 268310, 114688, 375760], false⟩

theorem canonicalMatch7_818 :
    canonicalPose7_818.boxKey 188160 (referenceBox7 (!canonicalBox7_818.bump)) = canonicalBox7_818 := by decide +kernel

theorem canonicalDecode7_818 : canonicalBox7_818.toKeyData 188160 = keys7Chunk25.get ⟨18, by decide⟩ := by
  change canonicalBox7_818.toKeyData 188160 = ⟨![(19 / 14), (47 / 28), (5 / 7), (15 / 28), (10 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_818 : keySolid (keys7Chunk25.get ⟨18, by decide⟩) = canonicalPose7_818.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_818 (box := canonicalBox7_818) (k := keys7Chunk25.get ⟨18, by decide⟩) (canonicalMatch7_818) (canonicalDecode7_818)

def canonicalPose7_819 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, true, true, true, true, false], ![2, 2, 1, 1, 2, 2, 0]⟩
def canonicalBox7_819 : BoxKey 7 :=
  ⟨![376320, 255360, 60480, 53760, 275520, 268800, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 254940, 60080, 53375, 274960, 268310, 114688], true⟩

theorem canonicalMatch7_819 :
    canonicalPose7_819.boxKey 188160 (referenceBox7 (!canonicalBox7_819.bump)) = canonicalBox7_819 := by decide +kernel

theorem canonicalDecode7_819 : canonicalBox7_819.toKeyData 188160 = keys7Chunk25.get ⟨19, by decide⟩ := by
  change canonicalBox7_819.toKeyData 188160 = ⟨![2, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (10 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_819 : keySolid (keys7Chunk25.get ⟨19, by decide⟩) = canonicalPose7_819.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_819 (box := canonicalBox7_819) (k := keys7Chunk25.get ⟨19, by decide⟩) (canonicalMatch7_819) (canonicalDecode7_819)

def canonicalPose7_820 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, false, false, true, true, true], ![2, 2, 0, 0, 2, 2, 1]⟩
def canonicalBox7_820 : BoxKey 7 :=
  ⟨![255360, 376320, 114240, 107520, 275520, 241920, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 376880, 114688, 108010, 274960, 241535, 60080], true⟩

theorem canonicalMatch7_820 :
    canonicalPose7_820.boxKey 188160 (referenceBox7 (!canonicalBox7_820.bump)) = canonicalBox7_820 := by decide +kernel

theorem canonicalDecode7_820 : canonicalBox7_820.toKeyData 188160 = keys7Chunk25.get ⟨20, by decide⟩ := by
  change canonicalBox7_820.toKeyData 188160 = ⟨![(19 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (9 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (673 / 336), (64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_820 : keySolid (keys7Chunk25.get ⟨20, by decide⟩) = canonicalPose7_820.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_820 (box := canonicalBox7_820) (k := keys7Chunk25.get ⟨20, by decide⟩) (canonicalMatch7_820) (canonicalDecode7_820)

def canonicalPose7_821 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, true, false, false, true, false, false], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_821 : BoxKey 7 :=
  ⟨![309120, 262080, 0, 107520, 275520, 322560, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 261632, 560, 108010, 274960, 322945, 128080], false⟩

theorem canonicalMatch7_821 :
    canonicalPose7_821.boxKey 188160 (referenceBox7 (!canonicalBox7_821.bump)) = canonicalBox7_821 := by decide +kernel

theorem canonicalDecode7_821 : canonicalBox7_821.toKeyData 188160 = keys7Chunk25.get ⟨21, by decide⟩ := by
  change canonicalBox7_821.toKeyData 188160 = ⟨![(23 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (12 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (146 / 105), (1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_821 : keySolid (keys7Chunk25.get ⟨21, by decide⟩) = canonicalPose7_821.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_821 (box := canonicalBox7_821) (k := keys7Chunk25.get ⟨21, by decide⟩) (canonicalMatch7_821) (canonicalDecode7_821)

def canonicalPose7_822 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, true, false, true, true, false, false], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_822 : BoxKey 7 :=
  ⟨![322560, 275520, 107520, 0, 262080, 309120, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 274960, 108010, -560, 261632, 309540, 128080], true⟩

theorem canonicalMatch7_822 :
    canonicalPose7_822.boxKey 188160 (referenceBox7 (!canonicalBox7_822.bump)) = canonicalBox7_822 := by decide +kernel

theorem canonicalDecode7_822 : canonicalBox7_822.toKeyData 188160 = keys7Chunk25.get ⟨22, by decide⟩ := by
  change canonicalBox7_822.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (1543 / 2688), (-1 / 336), (146 / 105), (737 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_822 : keySolid (keys7Chunk25.get ⟨22, by decide⟩) = canonicalPose7_822.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_822 (box := canonicalBox7_822) (k := keys7Chunk25.get ⟨22, by decide⟩) (canonicalMatch7_822) (canonicalDecode7_822)

def canonicalPose7_823 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, false, true, true, true], ![2, 2, 0, 0, 2, 2, 1]⟩
def canonicalBox7_823 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 114240, 376320, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 114688, 375760, 254940, 60080], false⟩

theorem canonicalMatch7_823 :
    canonicalPose7_823.boxKey 188160 (referenceBox7 (!canonicalBox7_823.bump)) = canonicalBox7_823 := by decide +kernel

theorem canonicalDecode7_823 : canonicalBox7_823.toKeyData 188160 = keys7Chunk25.get ⟨23, by decide⟩ := by
  change canonicalBox7_823.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (671 / 336), (607 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_823 : keySolid (keys7Chunk25.get ⟨23, by decide⟩) = canonicalPose7_823.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_823 (box := canonicalBox7_823) (k := keys7Chunk25.get ⟨23, by decide⟩) (canonicalMatch7_823) (canonicalDecode7_823)

def canonicalPose7_824 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, true, true, true, false], ![2, 2, 1, 1, 2, 2, 0]⟩
def canonicalBox7_824 : BoxKey 7 :=
  ⟨![268800, 275520, 53760, 60480, 255360, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 53375, 60080, 254940, 375760, 114688], false⟩

theorem canonicalMatch7_824 :
    canonicalPose7_824.boxKey 188160 (referenceBox7 (!canonicalBox7_824.bump)) = canonicalBox7_824 := by decide +kernel

theorem canonicalDecode7_824 : canonicalBox7_824.toKeyData 188160 = keys7Chunk25.get ⟨24, by decide⟩ := by
  change canonicalBox7_824.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_824 : keySolid (keys7Chunk25.get ⟨24, by decide⟩) = canonicalPose7_824.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_824 (box := canonicalBox7_824) (k := keys7Chunk25.get ⟨24, by decide⟩) (canonicalMatch7_824) (canonicalDecode7_824)

def canonicalPose7_825 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, false, true, false, false], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_825 : BoxKey 7 :=
  ⟨![302400, 268800, 100800, 134400, 248640, 309120, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 268310, 101360, 134785, 248240, 309540, 560], false⟩

theorem canonicalMatch7_825 :
    canonicalPose7_825.boxKey 188160 (referenceBox7 (!canonicalBox7_825.bump)) = canonicalBox7_825 := by decide +kernel

theorem canonicalDecode7_825 : canonicalBox7_825.toKeyData 188160 = keys7Chunk25.get ⟨25, by decide⟩ := by
  change canonicalBox7_825.toKeyData 188160 = ⟨![(45 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (23 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_825 : keySolid (keys7Chunk25.get ⟨25, by decide⟩) = canonicalPose7_825.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_825 (box := canonicalBox7_825) (k := keys7Chunk25.get ⟨25, by decide⟩) (canonicalMatch7_825) (canonicalDecode7_825)

def canonicalPose7_826 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, false, false, true, false, true], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_826 : BoxKey 7 :=
  ⟨![309120, 248640, 134400, 100800, 268800, 302400, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 248240, 134785, 101360, 268310, 302848, -560], true⟩

theorem canonicalMatch7_826 :
    canonicalPose7_826.boxKey 188160 (referenceBox7 (!canonicalBox7_826.bump)) = canonicalBox7_826 := by decide +kernel

theorem canonicalDecode7_826 : canonicalBox7_826.toKeyData 188160 = keys7Chunk25.get ⟨26, by decide⟩ := by
  change canonicalBox7_826.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (45 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_826 : keySolid (keys7Chunk25.get ⟨26, by decide⟩) = canonicalPose7_826.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_826 (box := canonicalBox7_826) (k := keys7Chunk25.get ⟨26, by decide⟩) (canonicalMatch7_826) (canonicalDecode7_826)

def canonicalPose7_827 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, true, true, true, true], ![2, 2, 1, 1, 2, 2, 2]⟩
def canonicalBox7_827 : BoxKey 7 :=
  ⟨![376320, 255360, 60480, 53760, 275520, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 254940, 60080, 53375, 274960, 268310, 261632], false⟩

theorem canonicalMatch7_827 :
    canonicalPose7_827.boxKey 188160 (referenceBox7 (!canonicalBox7_827.bump)) = canonicalBox7_827 := by decide +kernel

theorem canonicalDecode7_827 : canonicalBox7_827.toKeyData 188160 = keys7Chunk25.get ⟨27, by decide⟩ := by
  change canonicalBox7_827.toKeyData 188160 = ⟨![2, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_827 : keySolid (keys7Chunk25.get ⟨27, by decide⟩) = canonicalPose7_827.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_827 (box := canonicalBox7_827) (k := keys7Chunk25.get ⟨27, by decide⟩) (canonicalMatch7_827) (canonicalDecode7_827)

def canonicalPose7_828 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, false, false, true, true, false], ![2, 2, 0, 0, 2, 2, 1]⟩
def canonicalBox7_828 : BoxKey 7 :=
  ⟨![255360, 376320, 114240, 107520, 275520, 241920, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 375760, 114688, 108010, 274960, 241535, 316240], false⟩

theorem canonicalMatch7_828 :
    canonicalPose7_828.boxKey 188160 (referenceBox7 (!canonicalBox7_828.bump)) = canonicalBox7_828 := by decide +kernel

theorem canonicalDecode7_828 : canonicalBox7_828.toKeyData 188160 = keys7Chunk25.get ⟨28, by decide⟩ := by
  change canonicalBox7_828.toKeyData 188160 = ⟨![(19 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (9 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (671 / 336), (64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_828 : keySolid (keys7Chunk25.get ⟨28, by decide⟩) = canonicalPose7_828.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_828 (box := canonicalBox7_828) (k := keys7Chunk25.get ⟨28, by decide⟩) (canonicalMatch7_828) (canonicalDecode7_828)

def canonicalPose7_829 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, true, true, false, true, false, true], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_829 : BoxKey 7 :=
  ⟨![309120, 262080, 0, 107520, 275520, 322560, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 261632, -560, 108010, 274960, 322945, 248240], true⟩

theorem canonicalMatch7_829 :
    canonicalPose7_829.boxKey 188160 (referenceBox7 (!canonicalBox7_829.bump)) = canonicalBox7_829 := by decide +kernel

theorem canonicalDecode7_829 : canonicalBox7_829.toKeyData 188160 = keys7Chunk25.get ⟨29, by decide⟩ := by
  change canonicalBox7_829.toKeyData 188160 = ⟨![(23 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (12 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (146 / 105), (-1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_829 : keySolid (keys7Chunk25.get ⟨29, by decide⟩) = canonicalPose7_829.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_829 (box := canonicalBox7_829) (k := keys7Chunk25.get ⟨29, by decide⟩) (canonicalMatch7_829) (canonicalDecode7_829)

def canonicalPose7_830 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, true, false, false, true, false, true], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_830 : BoxKey 7 :=
  ⟨![322560, 275520, 107520, 0, 262080, 309120, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 274960, 108010, 560, 261632, 309540, 248240], false⟩

theorem canonicalMatch7_830 :
    canonicalPose7_830.boxKey 188160 (referenceBox7 (!canonicalBox7_830.bump)) = canonicalBox7_830 := by decide +kernel

theorem canonicalDecode7_830 : canonicalBox7_830.toKeyData 188160 = keys7Chunk25.get ⟨30, by decide⟩ := by
  change canonicalBox7_830.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (1543 / 2688), (1 / 336), (146 / 105), (737 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_830 : keySolid (keys7Chunk25.get ⟨30, by decide⟩) = canonicalPose7_830.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_830 (box := canonicalBox7_830) (k := keys7Chunk25.get ⟨30, by decide⟩) (canonicalMatch7_830) (canonicalDecode7_830)

def canonicalPose7_831 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, false, false, true, false], ![2, 2, 0, 0, 2, 2, 1]⟩
def canonicalBox7_831 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 114240, 376320, 255360, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 114688, 376880, 254940, 316240], true⟩

theorem canonicalMatch7_831 :
    canonicalPose7_831.boxKey 188160 (referenceBox7 (!canonicalBox7_831.bump)) = canonicalBox7_831 := by decide +kernel

theorem canonicalDecode7_831 : canonicalBox7_831.toKeyData 188160 = keys7Chunk25.get ⟨31, by decide⟩ := by
  change canonicalBox7_831.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (19 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (673 / 336), (607 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_831 : keySolid (keys7Chunk25.get ⟨31, by decide⟩) = canonicalPose7_831.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_831 (box := canonicalBox7_831) (k := keys7Chunk25.get ⟨31, by decide⟩) (canonicalMatch7_831) (canonicalDecode7_831)

theorem keys7Chunk25_canonical : ∀ k ∈ keys7Chunk25,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk25, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_800, canonicalSolid7_800⟩
  · exact ⟨canonicalPose7_801, canonicalSolid7_801⟩
  · exact ⟨canonicalPose7_802, canonicalSolid7_802⟩
  · exact ⟨canonicalPose7_803, canonicalSolid7_803⟩
  · exact ⟨canonicalPose7_804, canonicalSolid7_804⟩
  · exact ⟨canonicalPose7_805, canonicalSolid7_805⟩
  · exact ⟨canonicalPose7_806, canonicalSolid7_806⟩
  · exact ⟨canonicalPose7_807, canonicalSolid7_807⟩
  · exact ⟨canonicalPose7_808, canonicalSolid7_808⟩
  · exact ⟨canonicalPose7_809, canonicalSolid7_809⟩
  · exact ⟨canonicalPose7_810, canonicalSolid7_810⟩
  · exact ⟨canonicalPose7_811, canonicalSolid7_811⟩
  · exact ⟨canonicalPose7_812, canonicalSolid7_812⟩
  · exact ⟨canonicalPose7_813, canonicalSolid7_813⟩
  · exact ⟨canonicalPose7_814, canonicalSolid7_814⟩
  · exact ⟨canonicalPose7_815, canonicalSolid7_815⟩
  · exact ⟨canonicalPose7_816, canonicalSolid7_816⟩
  · exact ⟨canonicalPose7_817, canonicalSolid7_817⟩
  · exact ⟨canonicalPose7_818, canonicalSolid7_818⟩
  · exact ⟨canonicalPose7_819, canonicalSolid7_819⟩
  · exact ⟨canonicalPose7_820, canonicalSolid7_820⟩
  · exact ⟨canonicalPose7_821, canonicalSolid7_821⟩
  · exact ⟨canonicalPose7_822, canonicalSolid7_822⟩
  · exact ⟨canonicalPose7_823, canonicalSolid7_823⟩
  · exact ⟨canonicalPose7_824, canonicalSolid7_824⟩
  · exact ⟨canonicalPose7_825, canonicalSolid7_825⟩
  · exact ⟨canonicalPose7_826, canonicalSolid7_826⟩
  · exact ⟨canonicalPose7_827, canonicalSolid7_827⟩
  · exact ⟨canonicalPose7_828, canonicalSolid7_828⟩
  · exact ⟨canonicalPose7_829, canonicalSolid7_829⟩
  · exact ⟨canonicalPose7_830, canonicalSolid7_830⟩
  · exact ⟨canonicalPose7_831, canonicalSolid7_831⟩

#print axioms keys7Chunk25_canonical

end SparseMonotiles.Canonical
