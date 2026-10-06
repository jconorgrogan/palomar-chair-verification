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

def canonicalPose7_640 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, true, false, true, false], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_640 : BoxKey 7 :=
  ⟨![248640, 134400, 100800, 268800, 302400, 376320, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 134785, 101360, 268310, 302848, 375760, 309540], false⟩

theorem canonicalMatch7_640 :
    canonicalPose7_640.boxKey 188160 (referenceBox7 (!canonicalBox7_640.bump)) = canonicalBox7_640 := by decide +kernel

theorem canonicalDecode7_640 : canonicalBox7_640.toKeyData 188160 = keys7Chunk20.get ⟨0, by decide⟩ := by
  change canonicalBox7_640.toKeyData 188160 = ⟨![(37 / 28), (5 / 7), (15 / 28), (10 / 7), (45 / 28), 2, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (671 / 336), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_640 : keySolid (keys7Chunk20.get ⟨0, by decide⟩) = canonicalPose7_640.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_640 (box := canonicalBox7_640) (k := keys7Chunk20.get ⟨0, by decide⟩) (canonicalMatch7_640) (canonicalDecode7_640)

def canonicalPose7_641 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, true, true, true], ![2, 1, 1, 2, 2, 2, 2]⟩
def canonicalBox7_641 : BoxKey 7 :=
  ⟨![255360, 60480, 53760, 275520, 268800, 262080, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 53375, 274960, 268310, 261632, 375760], false⟩

theorem canonicalMatch7_641 :
    canonicalPose7_641.boxKey 188160 (referenceBox7 (!canonicalBox7_641.bump)) = canonicalBox7_641 := by decide +kernel

theorem canonicalDecode7_641 : canonicalBox7_641.toKeyData 188160 = keys7Chunk20.get ⟨1, by decide⟩ := by
  change canonicalBox7_641.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (2 / 7), (41 / 28), (10 / 7), (39 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_641 : keySolid (keys7Chunk20.get ⟨1, by decide⟩) = canonicalPose7_641.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_641 (box := canonicalBox7_641) (k := keys7Chunk20.get ⟨1, by decide⟩) (canonicalMatch7_641) (canonicalDecode7_641)

def canonicalPose7_642 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, false, true, true, false], ![2, 0, 2, 0, 1, 1, 0]⟩
def canonicalBox7_642 : BoxKey 7 :=
  ⟨![376320, 114240, 268800, 100800, 53760, 60480, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 114688, 268310, 101360, 53375, 60080, 121380], false⟩

theorem canonicalMatch7_642 :
    canonicalPose7_642.boxKey 188160 (referenceBox7 (!canonicalBox7_642.bump)) = canonicalBox7_642 := by decide +kernel

theorem canonicalDecode7_642 : canonicalBox7_642.toKeyData 188160 = keys7Chunk20.get ⟨2, by decide⟩ := by
  change canonicalBox7_642.toKeyData 188160 = ⟨![2, (17 / 28), (10 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_642 : keySolid (keys7Chunk20.get ⟨2, by decide⟩) = canonicalPose7_642.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_642 (box := canonicalBox7_642) (k := keys7Chunk20.get ⟨2, by decide⟩) (canonicalMatch7_642) (canonicalDecode7_642)

def canonicalPose7_643 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, false, false, false, false], ![1, 0, 1, 0, 0, 0, 0]⟩
def canonicalBox7_643 : BoxKey 7 :=
  ⟨![302400, 0, 309120, 127680, 134400, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, -560, 309540, 128080, 134785, 101360, 108010], true⟩

theorem canonicalMatch7_643 :
    canonicalPose7_643.boxKey 188160 (referenceBox7 (!canonicalBox7_643.bump)) = canonicalBox7_643 := by decide +kernel

theorem canonicalDecode7_643 : canonicalBox7_643.toKeyData 188160 = keys7Chunk20.get ⟨3, by decide⟩ := by
  change canonicalBox7_643.toKeyData 188160 = ⟨![(45 / 28), 0, (23 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (-1 / 336), (737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_643 : keySolid (keys7Chunk20.get ⟨3, by decide⟩) = canonicalPose7_643.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_643 (box := canonicalBox7_643) (k := keys7Chunk20.get ⟨3, by decide⟩) (canonicalMatch7_643) (canonicalDecode7_643)

def canonicalPose7_644 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, false, false, false, false], ![1, 0, 1, 0, 0, 0, 0]⟩
def canonicalBox7_644 : BoxKey 7 :=
  ⟨![309120, 0, 302400, 107520, 100800, 134400, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 560, 302848, 108010, 101360, 134785, 128080], false⟩

theorem canonicalMatch7_644 :
    canonicalPose7_644.boxKey 188160 (referenceBox7 (!canonicalBox7_644.bump)) = canonicalBox7_644 := by decide +kernel

theorem canonicalDecode7_644 : canonicalBox7_644.toKeyData 188160 = keys7Chunk20.get ⟨4, by decide⟩ := by
  change canonicalBox7_644.toKeyData 188160 = ⟨![(23 / 14), 0, (45 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (1 / 336), (169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_644 : keySolid (keys7Chunk20.get ⟨4, by decide⟩) = canonicalPose7_644.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_644 (box := canonicalBox7_644) (k := keys7Chunk20.get ⟨4, by decide⟩) (canonicalMatch7_644) (canonicalDecode7_644)

def canonicalPose7_645 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, false, true, true, false], ![2, 0, 2, 0, 1, 1, 0]⟩
def canonicalBox7_645 : BoxKey 7 :=
  ⟨![268800, 114240, 376320, 120960, 60480, 53760, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 114688, 376880, 121380, 60080, 53375, 101360], true⟩

theorem canonicalMatch7_645 :
    canonicalPose7_645.boxKey 188160 (referenceBox7 (!canonicalBox7_645.bump)) = canonicalBox7_645 := by decide +kernel

theorem canonicalDecode7_645 : canonicalBox7_645.toKeyData 188160 = keys7Chunk20.get ⟨5, by decide⟩ := by
  change canonicalBox7_645.toKeyData 188160 = ⟨![(10 / 7), (17 / 28), 2, (9 / 14), (9 / 28), (2 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (64 / 105), (673 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_645 : keySolid (keys7Chunk20.get ⟨5, by decide⟩) = canonicalPose7_645.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_645 (box := canonicalBox7_645) (k := keys7Chunk20.get ⟨5, by decide⟩) (canonicalMatch7_645) (canonicalDecode7_645)

def canonicalPose7_646 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, true, false, false, false], ![2, 1, 2, 0, 0, 0, 0]⟩
def canonicalBox7_646 : BoxKey 7 :=
  ⟨![241920, 60480, 255360, 0, 114240, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 60080, 254940, -560, 114688, 108010, 101360], true⟩

theorem canonicalMatch7_646 :
    canonicalPose7_646.boxKey 188160 (referenceBox7 (!canonicalBox7_646.bump)) = canonicalBox7_646 := by decide +kernel

theorem canonicalDecode7_646 : canonicalBox7_646.toKeyData 188160 = keys7Chunk20.get ⟨6, by decide⟩ := by
  change canonicalBox7_646.toKeyData 188160 = ⟨![(9 / 7), (9 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (64 / 105), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_646 : keySolid (keys7Chunk20.get ⟨6, by decide⟩) = canonicalPose7_646.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_646 (box := canonicalBox7_646) (k := keys7Chunk20.get ⟨6, by decide⟩) (canonicalMatch7_646) (canonicalDecode7_646)

def canonicalPose7_647 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, false, false, false, false, false, false], ![1, 0, 1, 0, 0, 0, 0]⟩
def canonicalBox7_647 : BoxKey 7 :=
  ⟨![322560, 127680, 309120, 114240, 0, 107520, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 128080, 309540, 114688, 560, 108010, 101360], false⟩

theorem canonicalMatch7_647 :
    canonicalPose7_647.boxKey 188160 (referenceBox7 (!canonicalBox7_647.bump)) = canonicalBox7_647 := by decide +kernel

theorem canonicalDecode7_647 : canonicalBox7_647.toKeyData 188160 = keys7Chunk20.get ⟨7, by decide⟩ := by
  change canonicalBox7_647.toKeyData 188160 = ⟨![(12 / 7), (19 / 28), (23 / 14), (17 / 28), 0, (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105), (1 / 336), (1543 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_647 : keySolid (keys7Chunk20.get ⟨7, by decide⟩) = canonicalPose7_647.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_647 (box := canonicalBox7_647) (k := keys7Chunk20.get ⟨7, by decide⟩) (canonicalMatch7_647) (canonicalDecode7_647)

def canonicalPose7_648 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, false, false, false, false, true, false], ![1, 0, 1, 0, 0, 0, 0]⟩
def canonicalBox7_648 : BoxKey 7 :=
  ⟨![309120, 127680, 322560, 100800, 107520, 0, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 128080, 322945, 101360, 108010, -560, 114688], true⟩

theorem canonicalMatch7_648 :
    canonicalPose7_648.boxKey 188160 (referenceBox7 (!canonicalBox7_648.bump)) = canonicalBox7_648 := by decide +kernel

theorem canonicalDecode7_648 : canonicalBox7_648.toKeyData 188160 = keys7Chunk20.get ⟨8, by decide⟩ := by
  change canonicalBox7_648.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (12 / 7), (15 / 28), (4 / 7), 0, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (-1 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_648 : keySolid (keys7Chunk20.get ⟨8, by decide⟩) = canonicalPose7_648.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_648 (box := canonicalBox7_648) (k := keys7Chunk20.get ⟨8, by decide⟩) (canonicalMatch7_648) (canonicalDecode7_648)

def canonicalPose7_649 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, false, false, false, false], ![2, 1, 2, 0, 0, 0, 0]⟩
def canonicalBox7_649 : BoxKey 7 :=
  ⟨![255360, 60480, 241920, 100800, 107520, 114240, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 241535, 101360, 108010, 114688, 560], false⟩

theorem canonicalMatch7_649 :
    canonicalPose7_649.boxKey 188160 (referenceBox7 (!canonicalBox7_649.bump)) = canonicalBox7_649 := by decide +kernel

theorem canonicalDecode7_649 : canonicalBox7_649.toKeyData 188160 = keys7Chunk20.get ⟨9, by decide⟩ := by
  change canonicalBox7_649.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (9 / 7), (15 / 28), (4 / 7), (17 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_649 : keySolid (keys7Chunk20.get ⟨9, by decide⟩) = canonicalPose7_649.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_649 (box := canonicalBox7_649) (k := keys7Chunk20.get ⟨9, by decide⟩) (canonicalMatch7_649) (canonicalDecode7_649)

def canonicalPose7_650 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, false, false, true, true], ![2, 0, 2, 0, 0, 1, 2]⟩
def canonicalBox7_650 : BoxKey 7 :=
  ⟨![376320, 114240, 268800, 100800, 134400, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 114688, 268310, 101360, 134785, 60080, 254940], false⟩

theorem canonicalMatch7_650 :
    canonicalPose7_650.boxKey 188160 (referenceBox7 (!canonicalBox7_650.bump)) = canonicalBox7_650 := by decide +kernel

theorem canonicalDecode7_650 : canonicalBox7_650.toKeyData 188160 = keys7Chunk20.get ⟨10, by decide⟩ := by
  change canonicalBox7_650.toKeyData 188160 = ⟨![2, (17 / 28), (10 / 7), (15 / 28), (5 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_650 : keySolid (keys7Chunk20.get ⟨10, by decide⟩) = canonicalPose7_650.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_650 (box := canonicalBox7_650) (k := keys7Chunk20.get ⟨10, by decide⟩) (canonicalMatch7_650) (canonicalDecode7_650)

def canonicalPose7_651 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, true, true, false, true, false, false], ![2, 0, 2, 0, 1, 0, 1]⟩
def canonicalBox7_651 : BoxKey 7 :=
  ⟨![262080, 0, 268800, 100800, 53760, 127680, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, -560, 268310, 101360, 53375, 128080, 309540], true⟩

theorem canonicalMatch7_651 :
    canonicalPose7_651.boxKey 188160 (referenceBox7 (!canonicalBox7_651.bump)) = canonicalBox7_651 := by decide +kernel

theorem canonicalDecode7_651 : canonicalBox7_651.toKeyData 188160 = keys7Chunk20.get ⟨11, by decide⟩ := by
  change canonicalBox7_651.toKeyData 188160 = ⟨![(39 / 28), 0, (10 / 7), (15 / 28), (2 / 7), (19 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (-1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_651 : keySolid (keys7Chunk20.get ⟨11, by decide⟩) = canonicalPose7_651.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_651 (box := canonicalBox7_651) (k := keys7Chunk20.get ⟨11, by decide⟩) (canonicalMatch7_651) (canonicalDecode7_651)

def canonicalPose7_652 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, false, true, false, true, false, false], ![2, 0, 2, 0, 1, 0, 1]⟩
def canonicalBox7_652 : BoxKey 7 :=
  ⟨![275520, 107520, 376320, 114240, 67200, 127680, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 108010, 375760, 114688, 66780, 128080, 322945], false⟩

theorem canonicalMatch7_652 :
    canonicalPose7_652.boxKey 188160 (referenceBox7 (!canonicalBox7_652.bump)) = canonicalBox7_652 := by decide +kernel

theorem canonicalDecode7_652 : canonicalBox7_652.toKeyData 188160 = keys7Chunk20.get ⟨12, by decide⟩ := by
  change canonicalBox7_652.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), 2, (17 / 28), (5 / 14), (19 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (671 / 336), (64 / 105), (159 / 448), (1601 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_652 : keySolid (keys7Chunk20.get ⟨12, by decide⟩) = canonicalPose7_652.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_652 (box := canonicalBox7_652) (k := keys7Chunk20.get ⟨12, by decide⟩) (canonicalMatch7_652) (canonicalDecode7_652)

def canonicalPose7_653 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, true, false, true, true], ![2, 0, 2, 0, 0, 1, 2]⟩
def canonicalBox7_653 : BoxKey 7 :=
  ⟨![275520, 107520, 262080, 0, 120960, 60480, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 261632, -560, 121380, 60080, 241535], true⟩

theorem canonicalMatch7_653 :
    canonicalPose7_653.boxKey 188160 (referenceBox7 (!canonicalBox7_653.bump)) = canonicalBox7_653 := by decide +kernel

theorem canonicalDecode7_653 : canonicalBox7_653.toKeyData 188160 = keys7Chunk20.get ⟨13, by decide⟩ := by
  change canonicalBox7_653.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (9 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (146 / 105), (-1 / 336), (289 / 448), (751 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_653 : keySolid (keys7Chunk20.get ⟨13, by decide⟩) = canonicalPose7_653.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_653 (box := canonicalBox7_653) (k := keys7Chunk20.get ⟨13, by decide⟩) (canonicalMatch7_653) (canonicalDecode7_653)

def canonicalPose7_654 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, false, true, false, true], ![2, 1, 1, 0, 0, 0, 2]⟩
def canonicalBox7_654 : BoxKey 7 :=
  ⟨![275520, 53760, 315840, 120960, 0, 114240, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 53375, 316240, 121380, -560, 114688, 268310], true⟩

theorem canonicalMatch7_654 :
    canonicalPose7_654.boxKey 188160 (referenceBox7 (!canonicalBox7_654.bump)) = canonicalBox7_654 := by decide +kernel

theorem canonicalDecode7_654 : canonicalBox7_654.toKeyData 188160 = keys7Chunk20.get ⟨14, by decide⟩ := by
  change canonicalBox7_654.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (47 / 28), (9 / 14), 0, (17 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (64 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_654 : keySolid (keys7Chunk20.get ⟨14, by decide⟩) = canonicalPose7_654.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_654 (box := canonicalBox7_654) (k := keys7Chunk20.get ⟨14, by decide⟩) (canonicalMatch7_654) (canonicalDecode7_654)

def canonicalPose7_655 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, true, false, true, true, false], ![2, 0, 2, 0, 1, 0, 1]⟩
def canonicalBox7_655 : BoxKey 7 :=
  ⟨![268800, 100800, 241920, 127680, 67200, 0, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 241535, 128080, 66780, -560, 302848], true⟩

theorem canonicalMatch7_655 :
    canonicalPose7_655.boxKey 188160 (referenceBox7 (!canonicalBox7_655.bump)) = canonicalBox7_655 := by decide +kernel

theorem canonicalDecode7_655 : canonicalBox7_655.toKeyData 188160 = keys7Chunk20.get ⟨15, by decide⟩ := by
  change canonicalBox7_655.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (9 / 7), (19 / 28), (5 / 14), 0, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (-1 / 336), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_655 : keySolid (keys7Chunk20.get ⟨15, by decide⟩) = canonicalPose7_655.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_655 (box := canonicalBox7_655) (k := keys7Chunk20.get ⟨15, by decide⟩) (canonicalMatch7_655) (canonicalDecode7_655)

def canonicalPose7_656 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, true, false, true, false, false], ![2, 0, 2, 0, 1, 0, 1]⟩
def canonicalBox7_656 : BoxKey 7 :=
  ⟨![248640, 134400, 275520, 107520, 73920, 0, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 134785, 274960, 108010, 73472, 560, 309540], false⟩

theorem canonicalMatch7_656 :
    canonicalPose7_656.boxKey 188160 (referenceBox7 (!canonicalBox7_656.bump)) = canonicalBox7_656 := by decide +kernel

theorem canonicalDecode7_656 : canonicalBox7_656.toKeyData 188160 = keys7Chunk20.get ⟨16, by decide⟩ := by
  change canonicalBox7_656.toKeyData 188160 = ⟨![(37 / 28), (5 / 7), (41 / 28), (4 / 7), (11 / 28), 0, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (1 / 336), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_656 : keySolid (keys7Chunk20.get ⟨16, by decide⟩) = canonicalPose7_656.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_656 (box := canonicalBox7_656) (k := keys7Chunk20.get ⟨16, by decide⟩) (canonicalMatch7_656) (canonicalDecode7_656)

def canonicalPose7_657 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, false, false, false, false, true], ![2, 1, 1, 0, 0, 0, 2]⟩
def canonicalBox7_657 : BoxKey 7 :=
  ⟨![255360, 60480, 322560, 100800, 107520, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 322945, 101360, 108010, 114688, 375760], false⟩

theorem canonicalMatch7_657 :
    canonicalPose7_657.boxKey 188160 (referenceBox7 (!canonicalBox7_657.bump)) = canonicalBox7_657 := by decide +kernel

theorem canonicalDecode7_657 : canonicalBox7_657.toKeyData 188160 = keys7Chunk20.get ⟨17, by decide⟩ := by
  change canonicalBox7_657.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (12 / 7), (15 / 28), (4 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_657 : keySolid (keys7Chunk20.get ⟨17, by decide⟩) = canonicalPose7_657.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_657 (box := canonicalBox7_657) (k := keys7Chunk20.get ⟨17, by decide⟩) (canonicalMatch7_657) (canonicalDecode7_657)

def canonicalPose7_658 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, false, false, true, true], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_658 : BoxKey 7 :=
  ⟨![376320, 73920, 268800, 100800, 134400, 248640, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 73472, 268310, 101360, 134785, 248240, 66780], true⟩

theorem canonicalMatch7_658 :
    canonicalPose7_658.boxKey 188160 (referenceBox7 (!canonicalBox7_658.bump)) = canonicalBox7_658 := by decide +kernel

theorem canonicalDecode7_658 : canonicalBox7_658.toKeyData 188160 = keys7Chunk20.get ⟨18, by decide⟩ := by
  change canonicalBox7_658.toKeyData 188160 = ⟨![2, (11 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_658 : keySolid (keys7Chunk20.get ⟨18, by decide⟩) = canonicalPose7_658.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_658 (box := canonicalBox7_658) (k := keys7Chunk20.get ⟨18, by decide⟩) (canonicalMatch7_658) (canonicalDecode7_658)

def canonicalPose7_659 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, false, false, true, true], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_659 : BoxKey 7 :=
  ⟨![376320, 67200, 248640, 134400, 100800, 268800, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 66780, 248240, 134785, 101360, 268310, 73472], false⟩

theorem canonicalMatch7_659 :
    canonicalPose7_659.boxKey 188160 (referenceBox7 (!canonicalBox7_659.bump)) = canonicalBox7_659 := by decide +kernel

theorem canonicalDecode7_659 : canonicalBox7_659.toKeyData 188160 = keys7Chunk20.get ⟨19, by decide⟩ := by
  change canonicalBox7_659.toKeyData 188160 = ⟨![2, (5 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_659 : keySolid (keys7Chunk20.get ⟨19, by decide⟩) = canonicalPose7_659.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_659 (box := canonicalBox7_659) (k := keys7Chunk20.get ⟨19, by decide⟩) (canonicalMatch7_659) (canonicalDecode7_659)

def canonicalPose7_660 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, true, true, true, true, false], ![2, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_660 : BoxKey 7 :=
  ⟨![262080, 0, 255360, 60480, 53760, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 560, 254940, 60080, 53375, 274960, 108010], false⟩

theorem canonicalMatch7_660 :
    canonicalPose7_660.boxKey 188160 (referenceBox7 (!canonicalBox7_660.bump)) = canonicalBox7_660 := by decide +kernel

theorem canonicalDecode7_660 : canonicalBox7_660.toKeyData 188160 = keys7Chunk20.get ⟨20, by decide⟩ := by
  change canonicalBox7_660.toKeyData 188160 = ⟨![(39 / 28), 0, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (1 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_660 : keySolid (keys7Chunk20.get ⟨20, by decide⟩) = canonicalPose7_660.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_660 (box := canonicalBox7_660) (k := keys7Chunk20.get ⟨20, by decide⟩) (canonicalMatch7_660) (canonicalDecode7_660)

def canonicalPose7_661 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, true, false, false, true, false], ![1, 0, 2, 0, 0, 2, 0]⟩
def canonicalBox7_661 : BoxKey 7 :=
  ⟨![315840, 120960, 376320, 114240, 107520, 275520, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 375760, 114688, 108010, 274960, 134785], false⟩

theorem canonicalMatch7_661 :
    canonicalPose7_661.boxKey 188160 (referenceBox7 (!canonicalBox7_661.bump)) = canonicalBox7_661 := by decide +kernel

theorem canonicalDecode7_661 : canonicalBox7_661.toKeyData 188160 = keys7Chunk20.get ⟨21, by decide⟩ := by
  change canonicalBox7_661.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (671 / 336), (64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_661 : keySolid (keys7Chunk20.get ⟨21, by decide⟩) = canonicalPose7_661.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_661 (box := canonicalBox7_661) (k := keys7Chunk20.get ⟨21, by decide⟩) (canonicalMatch7_661) (canonicalDecode7_661)

def canonicalPose7_662 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, true, true, true, false, true, true], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_662 : BoxKey 7 :=
  ⟨![248640, 67200, 262080, 0, 107520, 275520, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 66780, 261632, -560, 108010, 274960, 53375], true⟩

theorem canonicalMatch7_662 :
    canonicalPose7_662.boxKey 188160 (referenceBox7 (!canonicalBox7_662.bump)) = canonicalBox7_662 := by decide +kernel

theorem canonicalDecode7_662 : canonicalBox7_662.toKeyData 188160 = keys7Chunk20.get ⟨22, by decide⟩ := by
  change canonicalBox7_662.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (146 / 105), (-1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_662 : keySolid (keys7Chunk20.get ⟨22, by decide⟩) = canonicalPose7_662.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_662 (box := canonicalBox7_662) (k := keys7Chunk20.get ⟨22, by decide⟩) (canonicalMatch7_662) (canonicalDecode7_662)

def canonicalPose7_663 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, true, true, false, false, true, true], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_663 : BoxKey 7 :=
  ⟨![248640, 53760, 275520, 107520, 0, 262080, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 53375, 274960, 108010, 560, 261632, 66780], false⟩

theorem canonicalMatch7_663 :
    canonicalPose7_663.boxKey 188160 (referenceBox7 (!canonicalBox7_663.bump)) = canonicalBox7_663 := by decide +kernel

theorem canonicalDecode7_663 : canonicalBox7_663.toKeyData 188160 = keys7Chunk20.get ⟨23, by decide⟩ := by
  change canonicalBox7_663.toKeyData 188160 = ⟨![(37 / 28), (2 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (1 / 336), (146 / 105), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_663 : keySolid (keys7Chunk20.get ⟨23, by decide⟩) = canonicalPose7_663.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_663 (box := canonicalBox7_663) (k := keys7Chunk20.get ⟨23, by decide⟩) (canonicalMatch7_663) (canonicalDecode7_663)

def canonicalPose7_664 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, true, false, false, false, false], ![1, 0, 2, 0, 0, 2, 0]⟩
def canonicalBox7_664 : BoxKey 7 :=
  ⟨![315840, 134400, 275520, 107520, 114240, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 134785, 274960, 108010, 114688, 376880, 121380], true⟩

theorem canonicalMatch7_664 :
    canonicalPose7_664.boxKey 188160 (referenceBox7 (!canonicalBox7_664.bump)) = canonicalBox7_664 := by decide +kernel

theorem canonicalDecode7_664 : canonicalBox7_664.toKeyData 188160 = keys7Chunk20.get ⟨24, by decide⟩ := by
  change canonicalBox7_664.toKeyData 188160 = ⟨![(47 / 28), (5 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (673 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_664 : keySolid (keys7Chunk20.get ⟨24, by decide⟩) = canonicalPose7_664.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_664 (box := canonicalBox7_664) (k := keys7Chunk20.get ⟨24, by decide⟩) (canonicalMatch7_664) (canonicalDecode7_664)

def canonicalPose7_665 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, true, true, true, true], ![2, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_665 : BoxKey 7 :=
  ⟨![262080, 107520, 275520, 53760, 60480, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 108010, 274960, 53375, 60080, 254940, -560], true⟩

theorem canonicalMatch7_665 :
    canonicalPose7_665.boxKey 188160 (referenceBox7 (!canonicalBox7_665.bump)) = canonicalBox7_665 := by decide +kernel

theorem canonicalDecode7_665 : canonicalBox7_665.toKeyData 188160 = keys7Chunk20.get ⟨25, by decide⟩ := by
  change canonicalBox7_665.toKeyData 188160 = ⟨![(39 / 28), (4 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_665 : keySolid (keys7Chunk20.get ⟨25, by decide⟩) = canonicalPose7_665.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_665 (box := canonicalBox7_665) (k := keys7Chunk20.get ⟨25, by decide⟩) (canonicalMatch7_665) (canonicalDecode7_665)

def canonicalPose7_666 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, true, false, false, false, true], ![2, 0, 2, 0, 0, 1, 2]⟩
def canonicalBox7_666 : BoxKey 7 :=
  ⟨![376320, 114240, 268800, 100800, 134400, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 114688, 268310, 101360, 134785, 316240, 254940], true⟩

theorem canonicalMatch7_666 :
    canonicalPose7_666.boxKey 188160 (referenceBox7 (!canonicalBox7_666.bump)) = canonicalBox7_666 := by decide +kernel

theorem canonicalDecode7_666 : canonicalBox7_666.toKeyData 188160 = keys7Chunk20.get ⟨26, by decide⟩ := by
  change canonicalBox7_666.toKeyData 188160 = ⟨![2, (17 / 28), (10 / 7), (15 / 28), (5 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_666 : keySolid (keys7Chunk20.get ⟨26, by decide⟩) = canonicalPose7_666.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_666 (box := canonicalBox7_666) (k := keys7Chunk20.get ⟨26, by decide⟩) (canonicalMatch7_666) (canonicalDecode7_666)

def canonicalPose7_667 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, false, true, false, true, true, false], ![2, 0, 2, 0, 1, 2, 1]⟩
def canonicalBox7_667 : BoxKey 7 :=
  ⟨![262080, 0, 268800, 100800, 53760, 248640, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, 560, 268310, 101360, 53375, 248240, 309540], false⟩

theorem canonicalMatch7_667 :
    canonicalPose7_667.boxKey 188160 (referenceBox7 (!canonicalBox7_667.bump)) = canonicalBox7_667 := by decide +kernel

theorem canonicalDecode7_667 : canonicalBox7_667.toKeyData 188160 = keys7Chunk20.get ⟨27, by decide⟩ := by
  change canonicalBox7_667.toKeyData 188160 = ⟨![(39 / 28), 0, (10 / 7), (15 / 28), (2 / 7), (37 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_667 : keySolid (keys7Chunk20.get ⟨27, by decide⟩) = canonicalPose7_667.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_667 (box := canonicalBox7_667) (k := keys7Chunk20.get ⟨27, by decide⟩) (canonicalMatch7_667) (canonicalDecode7_667)

def canonicalPose7_668 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, false, false, false, true, true, false], ![2, 0, 2, 0, 1, 2, 1]⟩
def canonicalBox7_668 : BoxKey 7 :=
  ⟨![275520, 107520, 376320, 114240, 67200, 248640, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 108010, 376880, 114688, 66780, 248240, 322945], true⟩

theorem canonicalMatch7_668 :
    canonicalPose7_668.boxKey 188160 (referenceBox7 (!canonicalBox7_668.bump)) = canonicalBox7_668 := by decide +kernel

theorem canonicalDecode7_668 : canonicalBox7_668.toKeyData 188160 = keys7Chunk20.get ⟨28, by decide⟩ := by
  change canonicalBox7_668.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), 2, (17 / 28), (5 / 14), (37 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (673 / 336), (64 / 105), (159 / 448), (3103 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_668 : keySolid (keys7Chunk20.get ⟨28, by decide⟩) = canonicalPose7_668.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_668 (box := canonicalBox7_668) (k := keys7Chunk20.get ⟨28, by decide⟩) (canonicalMatch7_668) (canonicalDecode7_668)

def canonicalPose7_669 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, false, false, false, true], ![2, 0, 2, 0, 0, 1, 2]⟩
def canonicalBox7_669 : BoxKey 7 :=
  ⟨![275520, 107520, 262080, 0, 120960, 315840, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 261632, 560, 121380, 316240, 241535], false⟩

theorem canonicalMatch7_669 :
    canonicalPose7_669.boxKey 188160 (referenceBox7 (!canonicalBox7_669.bump)) = canonicalBox7_669 := by decide +kernel

theorem canonicalDecode7_669 : canonicalBox7_669.toKeyData 188160 = keys7Chunk20.get ⟨29, by decide⟩ := by
  change canonicalBox7_669.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (3953 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_669 : keySolid (keys7Chunk20.get ⟨29, by decide⟩) = canonicalPose7_669.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_669 (box := canonicalBox7_669) (k := keys7Chunk20.get ⟨29, by decide⟩) (canonicalMatch7_669) (canonicalDecode7_669)

def canonicalPose7_670 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, false, false, true, true], ![2, 1, 1, 0, 0, 2, 2]⟩
def canonicalBox7_670 : BoxKey 7 :=
  ⟨![275520, 53760, 315840, 120960, 0, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 53375, 316240, 121380, 560, 261632, 268310], false⟩

theorem canonicalMatch7_670 :
    canonicalPose7_670.boxKey 188160 (referenceBox7 (!canonicalBox7_670.bump)) = canonicalBox7_670 := by decide +kernel

theorem canonicalDecode7_670 : canonicalBox7_670.toKeyData 188160 = keys7Chunk20.get ⟨30, by decide⟩ := by
  change canonicalBox7_670.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (146 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_670 : keySolid (keys7Chunk20.get ⟨30, by decide⟩) = canonicalPose7_670.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_670 (box := canonicalBox7_670) (k := keys7Chunk20.get ⟨30, by decide⟩) (canonicalMatch7_670) (canonicalDecode7_670)

def canonicalPose7_671 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, true, false, true, true, false], ![2, 0, 2, 0, 1, 2, 1]⟩
def canonicalBox7_671 : BoxKey 7 :=
  ⟨![268800, 100800, 241920, 127680, 67200, 376320, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 241535, 128080, 66780, 375760, 302848], false⟩

theorem canonicalMatch7_671 :
    canonicalPose7_671.boxKey 188160 (referenceBox7 (!canonicalBox7_671.bump)) = canonicalBox7_671 := by decide +kernel

theorem canonicalDecode7_671 : canonicalBox7_671.toKeyData 188160 = keys7Chunk20.get ⟨31, by decide⟩ := by
  change canonicalBox7_671.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (9 / 7), (19 / 28), (5 / 14), 2, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (671 / 336), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_671 : keySolid (keys7Chunk20.get ⟨31, by decide⟩) = canonicalPose7_671.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_671 (box := canonicalBox7_671) (k := keys7Chunk20.get ⟨31, by decide⟩) (canonicalMatch7_671) (canonicalDecode7_671)

theorem keys7Chunk20_canonical : ∀ k ∈ keys7Chunk20,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk20, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_640, canonicalSolid7_640⟩
  · exact ⟨canonicalPose7_641, canonicalSolid7_641⟩
  · exact ⟨canonicalPose7_642, canonicalSolid7_642⟩
  · exact ⟨canonicalPose7_643, canonicalSolid7_643⟩
  · exact ⟨canonicalPose7_644, canonicalSolid7_644⟩
  · exact ⟨canonicalPose7_645, canonicalSolid7_645⟩
  · exact ⟨canonicalPose7_646, canonicalSolid7_646⟩
  · exact ⟨canonicalPose7_647, canonicalSolid7_647⟩
  · exact ⟨canonicalPose7_648, canonicalSolid7_648⟩
  · exact ⟨canonicalPose7_649, canonicalSolid7_649⟩
  · exact ⟨canonicalPose7_650, canonicalSolid7_650⟩
  · exact ⟨canonicalPose7_651, canonicalSolid7_651⟩
  · exact ⟨canonicalPose7_652, canonicalSolid7_652⟩
  · exact ⟨canonicalPose7_653, canonicalSolid7_653⟩
  · exact ⟨canonicalPose7_654, canonicalSolid7_654⟩
  · exact ⟨canonicalPose7_655, canonicalSolid7_655⟩
  · exact ⟨canonicalPose7_656, canonicalSolid7_656⟩
  · exact ⟨canonicalPose7_657, canonicalSolid7_657⟩
  · exact ⟨canonicalPose7_658, canonicalSolid7_658⟩
  · exact ⟨canonicalPose7_659, canonicalSolid7_659⟩
  · exact ⟨canonicalPose7_660, canonicalSolid7_660⟩
  · exact ⟨canonicalPose7_661, canonicalSolid7_661⟩
  · exact ⟨canonicalPose7_662, canonicalSolid7_662⟩
  · exact ⟨canonicalPose7_663, canonicalSolid7_663⟩
  · exact ⟨canonicalPose7_664, canonicalSolid7_664⟩
  · exact ⟨canonicalPose7_665, canonicalSolid7_665⟩
  · exact ⟨canonicalPose7_666, canonicalSolid7_666⟩
  · exact ⟨canonicalPose7_667, canonicalSolid7_667⟩
  · exact ⟨canonicalPose7_668, canonicalSolid7_668⟩
  · exact ⟨canonicalPose7_669, canonicalSolid7_669⟩
  · exact ⟨canonicalPose7_670, canonicalSolid7_670⟩
  · exact ⟨canonicalPose7_671, canonicalSolid7_671⟩

#print axioms keys7Chunk20_canonical

end SparseMonotiles.Canonical
