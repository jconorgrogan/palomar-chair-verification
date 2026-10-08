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

def canonicalPose7_736 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, true, false, false, false], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_736 : BoxKey 7 :=
  ⟨![302400, 107520, 275520, 241920, 127680, 309120, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 108010, 274960, 241535, 128080, 309540, 376880], true⟩

theorem canonicalMatch7_736 :
    canonicalPose7_736.boxKey 188160 (referenceBox7 (!canonicalBox7_736.bump)) = canonicalBox7_736 := by decide +kernel

theorem canonicalDecode7_736 : canonicalBox7_736.toKeyData 188160 = keys7Chunk23.get ⟨0, by decide⟩ := by
  change canonicalBox7_736.toKeyData 188160 = ⟨![(45 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (23 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_736 : keySolid (keys7Chunk23.get ⟨0, by decide⟩) = canonicalPose7_736.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_736 (box := canonicalBox7_736) (k := keys7Chunk23.get ⟨0, by decide⟩) (canonicalMatch7_736) (canonicalDecode7_736)

def canonicalPose7_737 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, true, true, false, false, true], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_737 : BoxKey 7 :=
  ⟨![309120, 127680, 241920, 275520, 107520, 302400, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 128080, 241535, 274960, 108010, 302848, 375760], false⟩

theorem canonicalMatch7_737 :
    canonicalPose7_737.boxKey 188160 (referenceBox7 (!canonicalBox7_737.bump)) = canonicalBox7_737 := by decide +kernel

theorem canonicalDecode7_737 : canonicalBox7_737.toKeyData 188160 = keys7Chunk23.get ⟨1, by decide⟩ := by
  change canonicalBox7_737.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (45 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_737 : keySolid (keys7Chunk23.get ⟨1, by decide⟩) = canonicalPose7_737.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_737 (box := canonicalBox7_737) (k := keys7Chunk23.get ⟨1, by decide⟩) (canonicalMatch7_737) (canonicalDecode7_737)

def canonicalPose7_738 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, false, true, false, true, true, false], ![2, 0, 2, 1, 2, 1, 0]⟩
def canonicalBox7_738 : BoxKey 7 :=
  ⟨![376320, 107520, 275520, 322560, 248640, 67200, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![375760, 108010, 274960, 322945, 248240, 66780, 114688], false⟩

theorem canonicalMatch7_738 :
    canonicalPose7_738.boxKey 188160 (referenceBox7 (!canonicalBox7_738.bump)) = canonicalBox7_738 := by decide +kernel

theorem canonicalDecode7_738 : canonicalBox7_738.toKeyData 188160 = keys7Chunk23.get ⟨2, by decide⟩ := by
  change canonicalBox7_738.toKeyData 188160 = ⟨![2, (4 / 7), (41 / 28), (12 / 7), (37 / 28), (5 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(671 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352), (159 / 448), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_738 : keySolid (keys7Chunk23.get ⟨2, by decide⟩) = canonicalPose7_738.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_738 (box := canonicalBox7_738) (k := keys7Chunk23.get ⟨2, by decide⟩) (canonicalMatch7_738) (canonicalDecode7_738)

def canonicalPose7_739 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, true, true, false, true, true, false], ![2, 0, 2, 1, 2, 1, 0]⟩
def canonicalBox7_739 : BoxKey 7 :=
  ⟨![268800, 0, 262080, 309120, 248640, 53760, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, -560, 261632, 309540, 248240, 53375, 101360], true⟩

theorem canonicalMatch7_739 :
    canonicalPose7_739.boxKey 188160 (referenceBox7 (!canonicalBox7_739.bump)) = canonicalBox7_739 := by decide +kernel

theorem canonicalDecode7_739 : canonicalBox7_739.toKeyData 188160 = keys7Chunk23.get ⟨3, by decide⟩ := by
  change canonicalBox7_739.toKeyData 188160 = ⟨![(10 / 7), 0, (39 / 28), (23 / 14), (37 / 28), (2 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (-1 / 336), (146 / 105), (737 / 448), (3103 / 2352), (1525 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_739 : keySolid (keys7Chunk23.get ⟨3, by decide⟩) = canonicalPose7_739.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_739 (box := canonicalBox7_739) (k := keys7Chunk23.get ⟨3, by decide⟩) (canonicalMatch7_739) (canonicalDecode7_739)

def canonicalPose7_740 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, true, true, false, false, false], ![2, 0, 2, 2, 1, 0, 0]⟩
def canonicalBox7_740 : BoxKey 7 :=
  ⟨![268800, 114240, 376320, 255360, 315840, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 114688, 375760, 254940, 316240, 134785, 101360], false⟩

theorem canonicalMatch7_740 :
    canonicalPose7_740.boxKey 188160 (referenceBox7 (!canonicalBox7_740.bump)) = canonicalBox7_740 := by decide +kernel

theorem canonicalDecode7_740 : canonicalBox7_740.toKeyData 188160 = keys7Chunk23.get ⟨4, by decide⟩ := by
  change canonicalBox7_740.toKeyData 188160 = ⟨![(10 / 7), (17 / 28), 2, (19 / 14), (47 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (64 / 105), (671 / 336), (607 / 448), (3953 / 2352), (3851 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_740 : keySolid (keys7Chunk23.get ⟨4, by decide⟩) = canonicalPose7_740.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_740 (box := canonicalBox7_740) (k := keys7Chunk23.get ⟨4, by decide⟩) (canonicalMatch7_740) (canonicalDecode7_740)

def canonicalPose7_741 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, true, true, true, false, false], ![1, 1, 2, 2, 2, 0, 0]⟩
def canonicalBox7_741 : BoxKey 7 :=
  ⟨![322560, 60480, 255360, 376320, 262080, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 60080, 254940, 375760, 261632, 108010, 101360], false⟩

theorem canonicalMatch7_741 :
    canonicalPose7_741.boxKey 188160 (referenceBox7 (!canonicalBox7_741.bump)) = canonicalBox7_741 := by decide +kernel

theorem canonicalDecode7_741 : canonicalBox7_741.toKeyData 188160 = keys7Chunk23.get ⟨5, by decide⟩ := by
  change canonicalBox7_741.toKeyData 188160 = ⟨![(12 / 7), (9 / 28), (19 / 14), 2, (39 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (751 / 2352), (607 / 448), (671 / 336), (146 / 105), (1543 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_741 : keySolid (keys7Chunk23.get ⟨5, by decide⟩) = canonicalPose7_741.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_741 (box := canonicalBox7_741) (k := keys7Chunk23.get ⟨5, by decide⟩) (canonicalMatch7_741) (canonicalDecode7_741)

def canonicalPose7_742 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, true, false, true, true, false], ![2, 0, 2, 1, 2, 1, 0]⟩
def canonicalBox7_742 : BoxKey 7 :=
  ⟨![275520, 134400, 248640, 309120, 376320, 73920, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 134785, 248240, 309540, 375760, 73472, 108010], false⟩

theorem canonicalMatch7_742 :
    canonicalPose7_742.boxKey 188160 (referenceBox7 (!canonicalBox7_742.bump)) = canonicalBox7_742 := by decide +kernel

theorem canonicalDecode7_742 : canonicalBox7_742.toKeyData 188160 = keys7Chunk23.get ⟨6, by decide⟩ := by
  change canonicalBox7_742.toKeyData 188160 = ⟨![(41 / 28), (5 / 7), (37 / 28), (23 / 14), 2, (11 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (671 / 336), (41 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_742 : keySolid (keys7Chunk23.get ⟨6, by decide⟩) = canonicalPose7_742.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_742 (box := canonicalBox7_742) (k := keys7Chunk23.get ⟨6, by decide⟩) (canonicalMatch7_742) (canonicalDecode7_742)

def canonicalPose7_743 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, true, false, false, true, false], ![2, 0, 2, 1, 2, 1, 0]⟩
def canonicalBox7_743 : BoxKey 7 :=
  ⟨![241920, 100800, 268800, 302400, 376320, 67200, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 101360, 268310, 302848, 376880, 66780, 128080], true⟩

theorem canonicalMatch7_743 :
    canonicalPose7_743.boxKey 188160 (referenceBox7 (!canonicalBox7_743.bump)) = canonicalBox7_743 := by decide +kernel

theorem canonicalDecode7_743 : canonicalBox7_743.toKeyData 188160 = keys7Chunk23.get ⟨7, by decide⟩ := by
  change canonicalBox7_743.toKeyData 188160 = ⟨![(9 / 7), (15 / 28), (10 / 7), (45 / 28), 2, (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (673 / 336), (159 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_743 : keySolid (keys7Chunk23.get ⟨7, by decide⟩) = canonicalPose7_743.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_743 (box := canonicalBox7_743) (k := keys7Chunk23.get ⟨7, by decide⟩) (canonicalMatch7_743) (canonicalDecode7_743)

def canonicalPose7_744 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, true, true, true, false], ![1, 1, 2, 2, 2, 0, 0]⟩
def canonicalBox7_744 : BoxKey 7 :=
  ⟨![315840, 53760, 275520, 268800, 262080, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 53375, 274960, 268310, 261632, -560, 121380], true⟩

theorem canonicalMatch7_744 :
    canonicalPose7_744.boxKey 188160 (referenceBox7 (!canonicalBox7_744.bump)) = canonicalBox7_744 := by decide +kernel

theorem canonicalDecode7_744 : canonicalBox7_744.toKeyData 188160 = keys7Chunk23.get ⟨8, by decide⟩ := by
  change canonicalBox7_744.toKeyData 188160 = ⟨![(47 / 28), (2 / 7), (41 / 28), (10 / 7), (39 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_744 : keySolid (keys7Chunk23.get ⟨8, by decide⟩) = canonicalPose7_744.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_744 (box := canonicalBox7_744) (k := keys7Chunk23.get ⟨8, by decide⟩) (canonicalMatch7_744) (canonicalDecode7_744)

def canonicalPose7_745 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, true, false, false, true], ![2, 0, 2, 2, 1, 0, 0]⟩
def canonicalBox7_745 : BoxKey 7 :=
  ⟨![262080, 107520, 275520, 241920, 315840, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 108010, 274960, 241535, 316240, 121380, -560], true⟩

theorem canonicalMatch7_745 :
    canonicalPose7_745.boxKey 188160 (referenceBox7 (!canonicalBox7_745.bump)) = canonicalBox7_745 := by decide +kernel

theorem canonicalDecode7_745 : canonicalBox7_745.toKeyData 188160 = keys7Chunk23.get ⟨9, by decide⟩ := by
  change canonicalBox7_745.toKeyData 188160 = ⟨![(39 / 28), (4 / 7), (41 / 28), (9 / 7), (47 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352), (289 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_745 : keySolid (keys7Chunk23.get ⟨9, by decide⟩) = canonicalPose7_745.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_745 (box := canonicalBox7_745) (k := keys7Chunk23.get ⟨9, by decide⟩) (canonicalMatch7_745) (canonicalDecode7_745)

def canonicalPose7_746 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, false, false, true, false, false, true], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_746 : BoxKey 7 :=
  ⟨![376320, 114240, 309120, 248640, 322560, 100800, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![375760, 114688, 309540, 248240, 322945, 101360, 268310], false⟩

theorem canonicalMatch7_746 :
    canonicalPose7_746.boxKey 188160 (referenceBox7 (!canonicalBox7_746.bump)) = canonicalBox7_746 := by decide +kernel

theorem canonicalDecode7_746 : canonicalBox7_746.toKeyData 188160 = keys7Chunk23.get ⟨10, by decide⟩ := by
  change canonicalBox7_746.toKeyData 188160 = ⟨![2, (17 / 28), (23 / 14), (37 / 28), (12 / 7), (15 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(671 / 336), (64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_746 : keySolid (keys7Chunk23.get ⟨10, by decide⟩) = canonicalPose7_746.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_746 (box := canonicalBox7_746) (k := keys7Chunk23.get ⟨10, by decide⟩) (canonicalMatch7_746) (canonicalDecode7_746)

def canonicalPose7_747 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, false, true, false, true], ![2, 0, 2, 1, 2, 0, 2]⟩
def canonicalBox7_747 : BoxKey 7 :=
  ⟨![262080, 0, 255360, 315840, 241920, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, -560, 254940, 316240, 241535, 101360, 268310], true⟩

theorem canonicalMatch7_747 :
    canonicalPose7_747.boxKey 188160 (referenceBox7 (!canonicalBox7_747.bump)) = canonicalBox7_747 := by decide +kernel

theorem canonicalDecode7_747 : canonicalBox7_747.toKeyData 188160 = keys7Chunk23.get ⟨11, by decide⟩ := by
  change canonicalBox7_747.toKeyData 188160 = ⟨![(39 / 28), 0, (19 / 14), (47 / 28), (9 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_747 : keySolid (keys7Chunk23.get ⟨11, by decide⟩) = canonicalPose7_747.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_747 (box := canonicalBox7_747) (k := keys7Chunk23.get ⟨11, by decide⟩) (canonicalMatch7_747) (canonicalDecode7_747)

def canonicalPose7_748 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, true, true, false, false], ![1, 0, 2, 2, 2, 0, 1]⟩
def canonicalBox7_748 : BoxKey 7 :=
  ⟨![315840, 120960, 376320, 262080, 268800, 100800, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 376880, 261632, 268310, 101360, 322945], true⟩

theorem canonicalMatch7_748 :
    canonicalPose7_748.boxKey 188160 (referenceBox7 (!canonicalBox7_748.bump)) = canonicalBox7_748 := by decide +kernel

theorem canonicalDecode7_748 : canonicalBox7_748.toKeyData 188160 = keys7Chunk23.get ⟨12, by decide⟩ := by
  change canonicalBox7_748.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (181 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_748 : keySolid (keys7Chunk23.get ⟨12, by decide⟩) = canonicalPose7_748.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_748 (box := canonicalBox7_748) (k := keys7Chunk23.get ⟨12, by decide⟩) (canonicalMatch7_748) (canonicalDecode7_748)

def canonicalPose7_749 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, true, false, false, true], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_749 : BoxKey 7 :=
  ⟨![275520, 107520, 302400, 376320, 309120, 127680, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 302848, 375760, 309540, 128080, 241535], false⟩

theorem canonicalMatch7_749 :
    canonicalPose7_749.boxKey 188160 (referenceBox7 (!canonicalBox7_749.bump)) = canonicalBox7_749 := by decide +kernel

theorem canonicalDecode7_749 : canonicalBox7_749.toKeyData 188160 = keys7Chunk23.get ⟨13, by decide⟩ := by
  change canonicalBox7_749.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (45 / 28), 2, (23 / 14), (19 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (169 / 105), (671 / 336), (737 / 448), (1601 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_749 : keySolid (keys7Chunk23.get ⟨13, by decide⟩) = canonicalPose7_749.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_749 (box := canonicalBox7_749) (k := keys7Chunk23.get ⟨13, by decide⟩) (canonicalMatch7_749) (canonicalDecode7_749)

def canonicalPose7_750 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, false, false, false, false, true], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_750 : BoxKey 7 :=
  ⟨![241920, 127680, 309120, 376320, 302400, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 128080, 309540, 376880, 302848, 108010, 274960], true⟩

theorem canonicalMatch7_750 :
    canonicalPose7_750.boxKey 188160 (referenceBox7 (!canonicalBox7_750.bump)) = canonicalBox7_750 := by decide +kernel

theorem canonicalDecode7_750 : canonicalBox7_750.toKeyData 188160 = keys7Chunk23.get ⟨14, by decide⟩ := by
  change canonicalBox7_750.toKeyData 188160 = ⟨![(9 / 7), (19 / 28), (23 / 14), 2, (45 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (1601 / 2352), (737 / 448), (673 / 336), (169 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_750 : keySolid (keys7Chunk23.get ⟨14, by decide⟩) = canonicalPose7_750.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_750 (box := canonicalBox7_750) (k := keys7Chunk23.get ⟨14, by decide⟩) (canonicalMatch7_750) (canonicalDecode7_750)

def canonicalPose7_751 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, true, true, false, false], ![1, 0, 2, 2, 2, 0, 1]⟩
def canonicalBox7_751 : BoxKey 7 :=
  ⟨![322560, 100800, 268800, 262080, 376320, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 101360, 268310, 261632, 375760, 121380, 316240], false⟩

theorem canonicalMatch7_751 :
    canonicalPose7_751.boxKey 188160 (referenceBox7 (!canonicalBox7_751.bump)) = canonicalBox7_751 := by decide +kernel

theorem canonicalDecode7_751 : canonicalBox7_751.toKeyData 188160 = keys7Chunk23.get ⟨15, by decide⟩ := by
  change canonicalBox7_751.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_751 : keySolid (keys7Chunk23.get ⟨15, by decide⟩) = canonicalPose7_751.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_751 (box := canonicalBox7_751) (k := keys7Chunk23.get ⟨15, by decide⟩) (canonicalMatch7_751) (canonicalDecode7_751)

def canonicalPose7_752 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, true, false, true, false, true], ![2, 0, 2, 1, 2, 0, 2]⟩
def canonicalBox7_752 : BoxKey 7 :=
  ⟨![268800, 100800, 241920, 315840, 255360, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 241535, 316240, 254940, 560, 261632], false⟩

theorem canonicalMatch7_752 :
    canonicalPose7_752.boxKey 188160 (referenceBox7 (!canonicalBox7_752.bump)) = canonicalBox7_752 := by decide +kernel

theorem canonicalDecode7_752 : canonicalBox7_752.toKeyData 188160 = keys7Chunk23.get ⟨16, by decide⟩ := by
  change canonicalBox7_752.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (9 / 7), (47 / 28), (19 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_752 : keySolid (keys7Chunk23.get ⟨16, by decide⟩) = canonicalPose7_752.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_752 (box := canonicalBox7_752) (k := keys7Chunk23.get ⟨16, by decide⟩) (canonicalMatch7_752) (canonicalDecode7_752)

def canonicalPose7_753 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, false, false, true, false, false, false], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_753 : BoxKey 7 :=
  ⟨![268800, 100800, 322560, 248640, 309120, 114240, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 101360, 322945, 248240, 309540, 114688, 376880], true⟩

theorem canonicalMatch7_753 :
    canonicalPose7_753.boxKey 188160 (referenceBox7 (!canonicalBox7_753.bump)) = canonicalBox7_753 := by decide +kernel

theorem canonicalDecode7_753 : canonicalBox7_753.toKeyData 188160 = keys7Chunk23.get ⟨17, by decide⟩ := by
  change canonicalBox7_753.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (12 / 7), (37 / 28), (23 / 14), (17 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_753 : keySolid (keys7Chunk23.get ⟨17, by decide⟩) = canonicalPose7_753.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_753 (box := canonicalBox7_753) (k := keys7Chunk23.get ⟨17, by decide⟩) (canonicalMatch7_753) (canonicalDecode7_753)

def canonicalPose7_754 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, true, true, true, true], ![2, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_754 : BoxKey 7 :=
  ⟨![376320, 73920, 268800, 275520, 241920, 248640, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 73472, 268310, 274960, 241535, 248240, 66780], true⟩

theorem canonicalMatch7_754 :
    canonicalPose7_754.boxKey 188160 (referenceBox7 (!canonicalBox7_754.bump)) = canonicalBox7_754 := by decide +kernel

theorem canonicalDecode7_754 : canonicalBox7_754.toKeyData 188160 = keys7Chunk23.get ⟨18, by decide⟩ := by
  change canonicalBox7_754.toKeyData 188160 = ⟨![2, (11 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_754 : keySolid (keys7Chunk23.get ⟨18, by decide⟩) = canonicalPose7_754.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_754 (box := canonicalBox7_754) (k := keys7Chunk23.get ⟨18, by decide⟩) (canonicalMatch7_754) (canonicalDecode7_754)

def canonicalPose7_755 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, true, true, true, true], ![2, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_755 : BoxKey 7 :=
  ⟨![376320, 67200, 248640, 241920, 275520, 268800, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 66780, 248240, 241535, 274960, 268310, 73472], false⟩

theorem canonicalMatch7_755 :
    canonicalPose7_755.boxKey 188160 (referenceBox7 (!canonicalBox7_755.bump)) = canonicalBox7_755 := by decide +kernel

theorem canonicalDecode7_755 : canonicalBox7_755.toKeyData 188160 = keys7Chunk23.get ⟨19, by decide⟩ := by
  change canonicalBox7_755.toKeyData 188160 = ⟨![2, (5 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_755 : keySolid (keys7Chunk23.get ⟨19, by decide⟩) = canonicalPose7_755.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_755 (box := canonicalBox7_755) (k := keys7Chunk23.get ⟨19, by decide⟩) (canonicalMatch7_755) (canonicalDecode7_755)

def canonicalPose7_756 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, true, false, false, true, false], ![2, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_756 : BoxKey 7 :=
  ⟨![262080, 0, 255360, 315840, 322560, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 560, 254940, 316240, 322945, 274960, 108010], false⟩

theorem canonicalMatch7_756 :
    canonicalPose7_756.boxKey 188160 (referenceBox7 (!canonicalBox7_756.bump)) = canonicalBox7_756 := by decide +kernel

theorem canonicalDecode7_756 : canonicalBox7_756.toKeyData 188160 = keys7Chunk23.get ⟨20, by decide⟩ := by
  change canonicalBox7_756.toKeyData 188160 = ⟨![(39 / 28), 0, (19 / 14), (47 / 28), (12 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_756 : keySolid (keys7Chunk23.get ⟨20, by decide⟩) = canonicalPose7_756.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_756 (box := canonicalBox7_756) (k := keys7Chunk23.get ⟨20, by decide⟩) (canonicalMatch7_756) (canonicalDecode7_756)

def canonicalPose7_757 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, true, true, true, true, false], ![1, 0, 2, 2, 2, 2, 0]⟩
def canonicalBox7_757 : BoxKey 7 :=
  ⟨![315840, 120960, 376320, 262080, 268800, 275520, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 375760, 261632, 268310, 274960, 134785], false⟩

theorem canonicalMatch7_757 :
    canonicalPose7_757.boxKey 188160 (referenceBox7 (!canonicalBox7_757.bump)) = canonicalBox7_757 := by decide +kernel

theorem canonicalDecode7_757 : canonicalBox7_757.toKeyData 188160 = keys7Chunk23.get ⟨21, by decide⟩ := by
  change canonicalBox7_757.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (671 / 336), (146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_757 : keySolid (keys7Chunk23.get ⟨21, by decide⟩) = canonicalPose7_757.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_757 (box := canonicalBox7_757) (k := keys7Chunk23.get ⟨21, by decide⟩) (canonicalMatch7_757) (canonicalDecode7_757)

def canonicalPose7_758 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, true, true, false, true, true, true], ![2, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_758 : BoxKey 7 :=
  ⟨![248640, 67200, 262080, 376320, 268800, 275520, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 66780, 261632, 376880, 268310, 274960, 53375], true⟩

theorem canonicalMatch7_758 :
    canonicalPose7_758.boxKey 188160 (referenceBox7 (!canonicalBox7_758.bump)) = canonicalBox7_758 := by decide +kernel

theorem canonicalDecode7_758 : canonicalBox7_758.toKeyData 188160 = keys7Chunk23.get ⟨22, by decide⟩ := by
  change canonicalBox7_758.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), (39 / 28), 2, (10 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (146 / 105), (673 / 336), (3833 / 2688), (491 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_758 : keySolid (keys7Chunk23.get ⟨22, by decide⟩) = canonicalPose7_758.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_758 (box := canonicalBox7_758) (k := keys7Chunk23.get ⟨22, by decide⟩) (canonicalMatch7_758) (canonicalDecode7_758)

def canonicalPose7_759 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, true, true, true, true, true, true], ![2, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_759 : BoxKey 7 :=
  ⟨![248640, 53760, 275520, 268800, 376320, 262080, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 53375, 274960, 268310, 375760, 261632, 66780], false⟩

theorem canonicalMatch7_759 :
    canonicalPose7_759.boxKey 188160 (referenceBox7 (!canonicalBox7_759.bump)) = canonicalBox7_759 := by decide +kernel

theorem canonicalDecode7_759 : canonicalBox7_759.toKeyData 188160 = keys7Chunk23.get ⟨23, by decide⟩ := by
  change canonicalBox7_759.toKeyData 188160 = ⟨![(37 / 28), (2 / 7), (41 / 28), (10 / 7), 2, (39 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (671 / 336), (146 / 105), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_759 : keySolid (keys7Chunk23.get ⟨23, by decide⟩) = canonicalPose7_759.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_759 (box := canonicalBox7_759) (k := keys7Chunk23.get ⟨23, by decide⟩) (canonicalMatch7_759) (canonicalDecode7_759)

def canonicalPose7_760 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, true, true, true, false, false], ![1, 0, 2, 2, 2, 2, 0]⟩
def canonicalBox7_760 : BoxKey 7 :=
  ⟨![315840, 134400, 275520, 268800, 262080, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 134785, 274960, 268310, 261632, 376880, 121380], true⟩

theorem canonicalMatch7_760 :
    canonicalPose7_760.boxKey 188160 (referenceBox7 (!canonicalBox7_760.bump)) = canonicalBox7_760 := by decide +kernel

theorem canonicalDecode7_760 : canonicalBox7_760.toKeyData 188160 = keys7Chunk23.get ⟨24, by decide⟩ := by
  change canonicalBox7_760.toKeyData 188160 = ⟨![(47 / 28), (5 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (673 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_760 : keySolid (keys7Chunk23.get ⟨24, by decide⟩) = canonicalPose7_760.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_760 (box := canonicalBox7_760) (k := keys7Chunk23.get ⟨24, by decide⟩) (canonicalMatch7_760) (canonicalDecode7_760)

def canonicalPose7_761 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, false, false, true, true], ![2, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_761 : BoxKey 7 :=
  ⟨![262080, 107520, 275520, 322560, 315840, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 108010, 274960, 322945, 316240, 254940, -560], true⟩

theorem canonicalMatch7_761 :
    canonicalPose7_761.boxKey 188160 (referenceBox7 (!canonicalBox7_761.bump)) = canonicalBox7_761 := by decide +kernel

theorem canonicalDecode7_761 : canonicalBox7_761.toKeyData 188160 = keys7Chunk23.get ⟨25, by decide⟩ := by
  change canonicalBox7_761.toKeyData 188160 = ⟨![(39 / 28), (4 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_761 : keySolid (keys7Chunk23.get ⟨25, by decide⟩) = canonicalPose7_761.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_761 (box := canonicalBox7_761) (k := keys7Chunk23.get ⟨25, by decide⟩) (canonicalMatch7_761) (canonicalDecode7_761)

def canonicalPose7_762 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, true, false, false, true], ![2, 0, 2, 2, 1, 1, 2]⟩
def canonicalBox7_762 : BoxKey 7 :=
  ⟨![376320, 114240, 268800, 275520, 322560, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 114688, 268310, 274960, 322945, 316240, 254940], false⟩

theorem canonicalMatch7_762 :
    canonicalPose7_762.boxKey 188160 (referenceBox7 (!canonicalBox7_762.bump)) = canonicalBox7_762 := by decide +kernel

theorem canonicalDecode7_762 : canonicalBox7_762.toKeyData 188160 = keys7Chunk23.get ⟨26, by decide⟩ := by
  change canonicalBox7_762.toKeyData 188160 = ⟨![2, (17 / 28), (10 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (64 / 105), (3833 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_762 : keySolid (keys7Chunk23.get ⟨26, by decide⟩) = canonicalPose7_762.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_762 (box := canonicalBox7_762) (k := keys7Chunk23.get ⟨26, by decide⟩) (canonicalMatch7_762) (canonicalDecode7_762)

def canonicalPose7_763 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, true, true, true, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_763 : BoxKey 7 :=
  ⟨![302400, 0, 309120, 248640, 241920, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, -560, 309540, 248240, 241535, 274960, 268310], true⟩

theorem canonicalMatch7_763 :
    canonicalPose7_763.boxKey 188160 (referenceBox7 (!canonicalBox7_763.bump)) = canonicalBox7_763 := by decide +kernel

theorem canonicalDecode7_763 : canonicalBox7_763.toKeyData 188160 = keys7Chunk23.get ⟨27, by decide⟩ := by
  change canonicalBox7_763.toKeyData 188160 = ⟨![(45 / 28), 0, (23 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (-1 / 336), (737 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_763 : keySolid (keys7Chunk23.get ⟨27, by decide⟩) = canonicalPose7_763.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_763 (box := canonicalBox7_763) (k := keys7Chunk23.get ⟨27, by decide⟩) (canonicalMatch7_763) (canonicalDecode7_763)

def canonicalPose7_764 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, true, true, true, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_764 : BoxKey 7 :=
  ⟨![309120, 0, 302400, 268800, 275520, 241920, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 560, 302848, 268310, 274960, 241535, 248240], false⟩

theorem canonicalMatch7_764 :
    canonicalPose7_764.boxKey 188160 (referenceBox7 (!canonicalBox7_764.bump)) = canonicalBox7_764 := by decide +kernel

theorem canonicalDecode7_764 : canonicalBox7_764.toKeyData 188160 = keys7Chunk23.get ⟨28, by decide⟩ := by
  change canonicalBox7_764.toKeyData 188160 = ⟨![(23 / 14), 0, (45 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (1 / 336), (169 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_764 : keySolid (keys7Chunk23.get ⟨28, by decide⟩) = canonicalPose7_764.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_764 (box := canonicalBox7_764) (k := keys7Chunk23.get ⟨28, by decide⟩) (canonicalMatch7_764) (canonicalDecode7_764)

def canonicalPose7_765 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, true, true, false, false], ![1, 1, 1, 2, 2, 1, 1]⟩
def canonicalBox7_765 : BoxKey 7 :=
  ⟨![302400, 188160, 309120, 248640, 241920, 288960, 295680], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, 187600, 309540, 248240, 241535, 289520, 296170], false⟩

theorem canonicalMatch7_765 :
    canonicalPose7_765.boxKey 188160 (referenceBox7 (!canonicalBox7_765.bump)) = canonicalBox7_765 := by decide +kernel

theorem canonicalDecode7_765 : canonicalBox7_765.toKeyData 188160 = keys7Chunk23.get ⟨29, by decide⟩ := by
  change canonicalBox7_765.toKeyData 188160 = ⟨![(45 / 28), 1, (23 / 14), (37 / 28), (9 / 7), (43 / 28), (11 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (335 / 336), (737 / 448), (3103 / 2352), (6901 / 5376), (517 / 336), (4231 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_765 : keySolid (keys7Chunk23.get ⟨29, by decide⟩) = canonicalPose7_765.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_765 (box := canonicalBox7_765) (k := keys7Chunk23.get ⟨29, by decide⟩) (canonicalMatch7_765) (canonicalDecode7_765)

def canonicalPose7_766 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, true, false, false, true], ![2, 0, 2, 2, 1, 1, 2]⟩
def canonicalBox7_766 : BoxKey 7 :=
  ⟨![268800, 114240, 376320, 255360, 315840, 322560, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 114688, 376880, 254940, 316240, 322945, 274960], true⟩

theorem canonicalMatch7_766 :
    canonicalPose7_766.boxKey 188160 (referenceBox7 (!canonicalBox7_766.bump)) = canonicalBox7_766 := by decide +kernel

theorem canonicalDecode7_766 : canonicalBox7_766.toKeyData 188160 = keys7Chunk23.get ⟨30, by decide⟩ := by
  change canonicalBox7_766.toKeyData 188160 = ⟨![(10 / 7), (17 / 28), 2, (19 / 14), (47 / 28), (12 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_766 : keySolid (keys7Chunk23.get ⟨30, by decide⟩) = canonicalPose7_766.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_766 (box := canonicalBox7_766) (k := keys7Chunk23.get ⟨30, by decide⟩) (canonicalMatch7_766) (canonicalDecode7_766)

def canonicalPose7_767 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, false, true, true, true], ![2, 1, 2, 2, 2, 2, 2]⟩
def canonicalBox7_767 : BoxKey 7 :=
  ⟨![241920, 60480, 255360, 376320, 262080, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 60080, 254940, 376880, 261632, 268310, 274960], true⟩

theorem canonicalMatch7_767 :
    canonicalPose7_767.boxKey 188160 (referenceBox7 (!canonicalBox7_767.bump)) = canonicalBox7_767 := by decide +kernel

theorem canonicalDecode7_767 : canonicalBox7_767.toKeyData 188160 = keys7Chunk23.get ⟨31, by decide⟩ := by
  change canonicalBox7_767.toKeyData 188160 = ⟨![(9 / 7), (9 / 28), (19 / 14), 2, (39 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (751 / 2352), (607 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_767 : keySolid (keys7Chunk23.get ⟨31, by decide⟩) = canonicalPose7_767.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_767 (box := canonicalBox7_767) (k := keys7Chunk23.get ⟨31, by decide⟩) (canonicalMatch7_767) (canonicalDecode7_767)

theorem keys7Chunk23_canonical : ∀ k ∈ keys7Chunk23,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk23, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_736, canonicalSolid7_736⟩
  · exact ⟨canonicalPose7_737, canonicalSolid7_737⟩
  · exact ⟨canonicalPose7_738, canonicalSolid7_738⟩
  · exact ⟨canonicalPose7_739, canonicalSolid7_739⟩
  · exact ⟨canonicalPose7_740, canonicalSolid7_740⟩
  · exact ⟨canonicalPose7_741, canonicalSolid7_741⟩
  · exact ⟨canonicalPose7_742, canonicalSolid7_742⟩
  · exact ⟨canonicalPose7_743, canonicalSolid7_743⟩
  · exact ⟨canonicalPose7_744, canonicalSolid7_744⟩
  · exact ⟨canonicalPose7_745, canonicalSolid7_745⟩
  · exact ⟨canonicalPose7_746, canonicalSolid7_746⟩
  · exact ⟨canonicalPose7_747, canonicalSolid7_747⟩
  · exact ⟨canonicalPose7_748, canonicalSolid7_748⟩
  · exact ⟨canonicalPose7_749, canonicalSolid7_749⟩
  · exact ⟨canonicalPose7_750, canonicalSolid7_750⟩
  · exact ⟨canonicalPose7_751, canonicalSolid7_751⟩
  · exact ⟨canonicalPose7_752, canonicalSolid7_752⟩
  · exact ⟨canonicalPose7_753, canonicalSolid7_753⟩
  · exact ⟨canonicalPose7_754, canonicalSolid7_754⟩
  · exact ⟨canonicalPose7_755, canonicalSolid7_755⟩
  · exact ⟨canonicalPose7_756, canonicalSolid7_756⟩
  · exact ⟨canonicalPose7_757, canonicalSolid7_757⟩
  · exact ⟨canonicalPose7_758, canonicalSolid7_758⟩
  · exact ⟨canonicalPose7_759, canonicalSolid7_759⟩
  · exact ⟨canonicalPose7_760, canonicalSolid7_760⟩
  · exact ⟨canonicalPose7_761, canonicalSolid7_761⟩
  · exact ⟨canonicalPose7_762, canonicalSolid7_762⟩
  · exact ⟨canonicalPose7_763, canonicalSolid7_763⟩
  · exact ⟨canonicalPose7_764, canonicalSolid7_764⟩
  · exact ⟨canonicalPose7_765, canonicalSolid7_765⟩
  · exact ⟨canonicalPose7_766, canonicalSolid7_766⟩
  · exact ⟨canonicalPose7_767, canonicalSolid7_767⟩

#print axioms keys7Chunk23_canonical

end SparseMonotiles.Canonical
