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

def canonicalPose7_608 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, true, false, true, true], ![1, 0, 0, 2, 0, 2, 2]⟩
def canonicalBox7_608 : BoxKey 7 :=
  ⟨![315840, 134400, 100800, 268800, 114240, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 134785, 101360, 268310, 114688, 375760, 254940], false⟩

theorem canonicalMatch7_608 :
    canonicalPose7_608.boxKey 188160 (referenceBox7 (!canonicalBox7_608.bump)) = canonicalBox7_608 := by decide +kernel

theorem canonicalDecode7_608 : canonicalBox7_608.toKeyData 188160 = keys7Chunk19.get ⟨0, by decide⟩ := by
  change canonicalBox7_608.toKeyData 188160 = ⟨![(47 / 28), (5 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (671 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_608 : keySolid (keys7Chunk19.get ⟨0, by decide⟩) = canonicalPose7_608.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_608 (box := canonicalBox7_608) (k := keys7Chunk19.get ⟨0, by decide⟩) (canonicalMatch7_608) (canonicalDecode7_608)

def canonicalPose7_609 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, false, false, true, true, true], ![2, 0, 0, 1, 1, 2, 2]⟩
def canonicalBox7_609 : BoxKey 7 :=
  ⟨![262080, 107520, 100800, 322560, 60480, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 108010, 101360, 322945, 60080, 254940, 375760], false⟩

theorem canonicalMatch7_609 :
    canonicalPose7_609.boxKey 188160 (referenceBox7 (!canonicalBox7_609.bump)) = canonicalBox7_609 := by decide +kernel

theorem canonicalDecode7_609 : canonicalBox7_609.toKeyData 188160 = keys7Chunk19.get ⟨1, by decide⟩ := by
  change canonicalBox7_609.toKeyData 188160 = ⟨![(39 / 28), (4 / 7), (15 / 28), (12 / 7), (9 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352), (607 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_609 : keySolid (keys7Chunk19.get ⟨1, by decide⟩) = canonicalPose7_609.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_609 (box := canonicalBox7_609) (k := keys7Chunk19.get ⟨1, by decide⟩) (canonicalMatch7_609) (canonicalDecode7_609)

def canonicalPose7_610 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, false, true, true, false, true], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_610 : BoxKey 7 :=
  ⟨![376320, 73920, 107520, 275520, 241920, 127680, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 73472, 108010, 274960, 241535, 128080, 66780], true⟩

theorem canonicalMatch7_610 :
    canonicalPose7_610.boxKey 188160 (referenceBox7 (!canonicalBox7_610.bump)) = canonicalBox7_610 := by decide +kernel

theorem canonicalDecode7_610 : canonicalBox7_610.toKeyData 188160 = keys7Chunk19.get ⟨2, by decide⟩ := by
  change canonicalBox7_610.toKeyData 188160 = ⟨![2, (11 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_610 : keySolid (keys7Chunk19.get ⟨2, by decide⟩) = canonicalPose7_610.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_610 (box := canonicalBox7_610) (k := keys7Chunk19.get ⟨2, by decide⟩) (canonicalMatch7_610) (canonicalDecode7_610)

def canonicalPose7_611 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, true, true, false, true], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_611 : BoxKey 7 :=
  ⟨![376320, 67200, 127680, 241920, 275520, 107520, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 66780, 128080, 241535, 274960, 108010, 73472], false⟩

theorem canonicalMatch7_611 :
    canonicalPose7_611.boxKey 188160 (referenceBox7 (!canonicalBox7_611.bump)) = canonicalBox7_611 := by decide +kernel

theorem canonicalDecode7_611 : canonicalBox7_611.toKeyData 188160 = keys7Chunk19.get ⟨3, by decide⟩ := by
  change canonicalBox7_611.toKeyData 188160 = ⟨![2, (5 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_611 : keySolid (keys7Chunk19.get ⟨3, by decide⟩) = canonicalPose7_611.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_611 (box := canonicalBox7_611) (k := keys7Chunk19.get ⟨3, by decide⟩) (canonicalMatch7_611) (canonicalDecode7_611)

def canonicalPose7_612 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, false, false, false, false, false], ![2, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_612 : BoxKey 7 :=
  ⟨![262080, 0, 120960, 315840, 322560, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 560, 121380, 316240, 322945, 101360, 108010], false⟩

theorem canonicalMatch7_612 :
    canonicalPose7_612.boxKey 188160 (referenceBox7 (!canonicalBox7_612.bump)) = canonicalBox7_612 := by decide +kernel

theorem canonicalDecode7_612 : canonicalBox7_612.toKeyData 188160 = keys7Chunk19.get ⟨4, by decide⟩ := by
  change canonicalBox7_612.toKeyData 188160 = ⟨![(39 / 28), 0, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_612 : keySolid (keys7Chunk19.get ⟨4, by decide⟩) = canonicalPose7_612.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_612 (box := canonicalBox7_612) (k := keys7Chunk19.get ⟨4, by decide⟩) (canonicalMatch7_612) (canonicalDecode7_612)

def canonicalPose7_613 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, true, true, false, false], ![1, 0, 0, 2, 2, 0, 0]⟩
def canonicalBox7_613 : BoxKey 7 :=
  ⟨![315840, 120960, 0, 262080, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 560, 261632, 268310, 101360, 134785], false⟩

theorem canonicalMatch7_613 :
    canonicalPose7_613.boxKey 188160 (referenceBox7 (!canonicalBox7_613.bump)) = canonicalBox7_613 := by decide +kernel

theorem canonicalDecode7_613 : canonicalBox7_613.toKeyData 188160 = keys7Chunk19.get ⟨5, by decide⟩ := by
  change canonicalBox7_613.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_613 : keySolid (keys7Chunk19.get ⟨5, by decide⟩) = canonicalPose7_613.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_613 (box := canonicalBox7_613) (k := keys7Chunk19.get ⟨5, by decide⟩) (canonicalMatch7_613) (canonicalDecode7_613)

def canonicalPose7_614 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, true, false, false, true, false, true], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_614 : BoxKey 7 :=
  ⟨![248640, 67200, 114240, 376320, 268800, 100800, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 66780, 114688, 376880, 268310, 101360, 53375], true⟩

theorem canonicalMatch7_614 :
    canonicalPose7_614.boxKey 188160 (referenceBox7 (!canonicalBox7_614.bump)) = canonicalBox7_614 := by decide +kernel

theorem canonicalDecode7_614 : canonicalBox7_614.toKeyData 188160 = keys7Chunk19.get ⟨6, by decide⟩ := by
  change canonicalBox7_614.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (64 / 105), (673 / 336), (3833 / 2688), (181 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_614 : keySolid (keys7Chunk19.get ⟨6, by decide⟩) = canonicalPose7_614.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_614 (box := canonicalBox7_614) (k := keys7Chunk19.get ⟨6, by decide⟩) (canonicalMatch7_614) (canonicalDecode7_614)

def canonicalPose7_615 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, true, false, true, true, false, true], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_615 : BoxKey 7 :=
  ⟨![248640, 53760, 100800, 268800, 376320, 114240, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 53375, 101360, 268310, 375760, 114688, 66780], false⟩

theorem canonicalMatch7_615 :
    canonicalPose7_615.boxKey 188160 (referenceBox7 (!canonicalBox7_615.bump)) = canonicalBox7_615 := by decide +kernel

theorem canonicalDecode7_615 : canonicalBox7_615.toKeyData 188160 = keys7Chunk19.get ⟨7, by decide⟩ := by
  change canonicalBox7_615.toKeyData 188160 = ⟨![(37 / 28), (2 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (671 / 336), (64 / 105), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_615 : keySolid (keys7Chunk19.get ⟨7, by decide⟩) = canonicalPose7_615.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_615 (box := canonicalBox7_615) (k := keys7Chunk19.get ⟨7, by decide⟩) (canonicalMatch7_615) (canonicalDecode7_615)

def canonicalPose7_616 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, true, true, true, false], ![1, 0, 0, 2, 2, 0, 0]⟩
def canonicalBox7_616 : BoxKey 7 :=
  ⟨![315840, 134400, 100800, 268800, 262080, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 134785, 101360, 268310, 261632, -560, 121380], true⟩

theorem canonicalMatch7_616 :
    canonicalPose7_616.boxKey 188160 (referenceBox7 (!canonicalBox7_616.bump)) = canonicalBox7_616 := by decide +kernel

theorem canonicalDecode7_616 : canonicalBox7_616.toKeyData 188160 = keys7Chunk19.get ⟨8, by decide⟩ := by
  change canonicalBox7_616.toKeyData 188160 = ⟨![(47 / 28), (5 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_616 : keySolid (keys7Chunk19.get ⟨8, by decide⟩) = canonicalPose7_616.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_616 (box := canonicalBox7_616) (k := keys7Chunk19.get ⟨8, by decide⟩) (canonicalMatch7_616) (canonicalDecode7_616)

def canonicalPose7_617 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, false, false, false, false, true], ![2, 0, 0, 1, 1, 0, 0]⟩
def canonicalBox7_617 : BoxKey 7 :=
  ⟨![262080, 107520, 100800, 322560, 315840, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 108010, 101360, 322945, 316240, 121380, -560], true⟩

theorem canonicalMatch7_617 :
    canonicalPose7_617.boxKey 188160 (referenceBox7 (!canonicalBox7_617.bump)) = canonicalBox7_617 := by decide +kernel

theorem canonicalDecode7_617 : canonicalBox7_617.toKeyData 188160 = keys7Chunk19.get ⟨9, by decide⟩ := by
  change canonicalBox7_617.toKeyData 188160 = ⟨![(39 / 28), (4 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_617 : keySolid (keys7Chunk19.get ⟨9, by decide⟩) = canonicalPose7_617.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_617 (box := canonicalBox7_617) (k := keys7Chunk19.get ⟨9, by decide⟩) (canonicalMatch7_617) (canonicalDecode7_617)

def canonicalPose7_618 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, true, true, true, true], ![2, 0, 0, 2, 2, 1, 2]⟩
def canonicalBox7_618 : BoxKey 7 :=
  ⟨![376320, 114240, 107520, 275520, 241920, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 114688, 108010, 274960, 241535, 60080, 254940], true⟩

theorem canonicalMatch7_618 :
    canonicalPose7_618.boxKey 188160 (referenceBox7 (!canonicalBox7_618.bump)) = canonicalBox7_618 := by decide +kernel

theorem canonicalDecode7_618 : canonicalBox7_618.toKeyData 188160 = keys7Chunk19.get ⟨10, by decide⟩ := by
  change canonicalBox7_618.toKeyData 188160 = ⟨![2, (17 / 28), (4 / 7), (41 / 28), (9 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_618 : keySolid (keys7Chunk19.get ⟨10, by decide⟩) = canonicalPose7_618.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_618 (box := canonicalBox7_618) (k := keys7Chunk19.get ⟨10, by decide⟩) (canonicalMatch7_618) (canonicalDecode7_618)

def canonicalPose7_619 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, false, false, true, false, false, false], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_619 : BoxKey 7 :=
  ⟨![262080, 0, 107520, 275520, 322560, 127680, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, 560, 108010, 274960, 322945, 128080, 309540], false⟩

theorem canonicalMatch7_619 :
    canonicalPose7_619.boxKey 188160 (referenceBox7 (!canonicalBox7_619.bump)) = canonicalBox7_619 := by decide +kernel

theorem canonicalDecode7_619 : canonicalBox7_619.toKeyData 188160 = keys7Chunk19.get ⟨11, by decide⟩ := by
  change canonicalBox7_619.toKeyData 188160 = ⟨![(39 / 28), 0, (4 / 7), (41 / 28), (12 / 7), (19 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_619 : keySolid (keys7Chunk19.get ⟨11, by decide⟩) = canonicalPose7_619.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_619 (box := canonicalBox7_619) (k := keys7Chunk19.get ⟨11, by decide⟩) (canonicalMatch7_619) (canonicalDecode7_619)

def canonicalPose7_620 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, false, true, true, false, false, false], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_620 : BoxKey 7 :=
  ⟨![275520, 107520, 0, 262080, 309120, 127680, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 108010, -560, 261632, 309540, 128080, 322945], true⟩

theorem canonicalMatch7_620 :
    canonicalPose7_620.boxKey 188160 (referenceBox7 (!canonicalBox7_620.bump)) = canonicalBox7_620 := by decide +kernel

theorem canonicalDecode7_620 : canonicalBox7_620.toKeyData 188160 = keys7Chunk19.get ⟨12, by decide⟩ := by
  change canonicalBox7_620.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), 0, (39 / 28), (23 / 14), (19 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (-1 / 336), (146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_620 : keySolid (keys7Chunk19.get ⟨12, by decide⟩) = canonicalPose7_620.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_620 (box := canonicalBox7_620) (k := keys7Chunk19.get ⟨12, by decide⟩) (canonicalMatch7_620) (canonicalDecode7_620)

def canonicalPose7_621 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, true, true, true, true], ![2, 0, 0, 2, 2, 1, 2]⟩
def canonicalBox7_621 : BoxKey 7 :=
  ⟨![275520, 107520, 114240, 376320, 255360, 60480, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 114688, 375760, 254940, 60080, 241535], false⟩

theorem canonicalMatch7_621 :
    canonicalPose7_621.boxKey 188160 (referenceBox7 (!canonicalBox7_621.bump)) = canonicalBox7_621 := by decide +kernel

theorem canonicalDecode7_621 : canonicalBox7_621.toKeyData 188160 = keys7Chunk19.get ⟨13, by decide⟩ := by
  change canonicalBox7_621.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (64 / 105), (671 / 336), (607 / 448), (751 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_621 : keySolid (keys7Chunk19.get ⟨13, by decide⟩) = canonicalPose7_621.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_621 (box := canonicalBox7_621) (k := keys7Chunk19.get ⟨13, by decide⟩) (canonicalMatch7_621) (canonicalDecode7_621)

def canonicalPose7_622 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, true, false, true], ![2, 1, 1, 2, 2, 0, 2]⟩
def canonicalBox7_622 : BoxKey 7 :=
  ⟨![275520, 53760, 60480, 255360, 376320, 114240, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 53375, 60080, 254940, 375760, 114688, 268310], false⟩

theorem canonicalMatch7_622 :
    canonicalPose7_622.boxKey 188160 (referenceBox7 (!canonicalBox7_622.bump)) = canonicalBox7_622 := by decide +kernel

theorem canonicalDecode7_622 : canonicalBox7_622.toKeyData 188160 = keys7Chunk19.get ⟨14, by decide⟩ := by
  change canonicalBox7_622.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_622 : keySolid (keys7Chunk19.get ⟨14, by decide⟩) = canonicalPose7_622.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_622 (box := canonicalBox7_622) (k := keys7Chunk19.get ⟨14, by decide⟩) (canonicalMatch7_622) (canonicalDecode7_622)

def canonicalPose7_623 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, true, false, false, false], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_623 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 248640, 309120, 0, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 248240, 309540, 560, 302848], false⟩

theorem canonicalMatch7_623 :
    canonicalPose7_623.boxKey 188160 (referenceBox7 (!canonicalBox7_623.bump)) = canonicalBox7_623 := by decide +kernel

theorem canonicalDecode7_623 : canonicalBox7_623.toKeyData 188160 = keys7Chunk19.get ⟨15, by decide⟩ := by
  change canonicalBox7_623.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (37 / 28), (23 / 14), 0, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (1 / 336), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_623 : keySolid (keys7Chunk19.get ⟨15, by decide⟩) = canonicalPose7_623.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_623 (box := canonicalBox7_623) (k := keys7Chunk19.get ⟨15, by decide⟩) (canonicalMatch7_623) (canonicalDecode7_623)

def canonicalPose7_624 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, true, false, true, false], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_624 : BoxKey 7 :=
  ⟨![248640, 134400, 100800, 268800, 302400, 0, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 134785, 101360, 268310, 302848, -560, 309540], true⟩

theorem canonicalMatch7_624 :
    canonicalPose7_624.boxKey 188160 (referenceBox7 (!canonicalBox7_624.bump)) = canonicalBox7_624 := by decide +kernel

theorem canonicalDecode7_624 : canonicalBox7_624.toKeyData 188160 = keys7Chunk19.get ⟨16, by decide⟩ := by
  change canonicalBox7_624.toKeyData 188160 = ⟨![(37 / 28), (5 / 7), (15 / 28), (10 / 7), (45 / 28), 0, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (-1 / 336), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_624 : keySolid (keys7Chunk19.get ⟨16, by decide⟩) = canonicalPose7_624.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_624 (box := canonicalBox7_624) (k := keys7Chunk19.get ⟨16, by decide⟩) (canonicalMatch7_624) (canonicalDecode7_624)

def canonicalPose7_625 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, true, false, false], ![2, 1, 1, 2, 2, 0, 2]⟩
def canonicalBox7_625 : BoxKey 7 :=
  ⟨![255360, 60480, 53760, 275520, 268800, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 53375, 274960, 268310, 114688, 376880], true⟩

theorem canonicalMatch7_625 :
    canonicalPose7_625.boxKey 188160 (referenceBox7 (!canonicalBox7_625.bump)) = canonicalBox7_625 := by decide +kernel

theorem canonicalDecode7_625 : canonicalBox7_625.toKeyData 188160 = keys7Chunk19.get ⟨17, by decide⟩ := by
  change canonicalBox7_625.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (2 / 7), (41 / 28), (10 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_625 : keySolid (keys7Chunk19.get ⟨17, by decide⟩) = canonicalPose7_625.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_625 (box := canonicalBox7_625) (k := keys7Chunk19.get ⟨17, by decide⟩) (canonicalMatch7_625) (canonicalDecode7_625)

def canonicalPose7_626 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, false, true, true, false, true, false], ![2, 0, 1, 2, 1, 2, 0]⟩
def canonicalBox7_626 : BoxKey 7 :=
  ⟨![376320, 114240, 67200, 248640, 322560, 275520, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![376880, 114688, 66780, 248240, 322945, 274960, 108010], true⟩

theorem canonicalMatch7_626 :
    canonicalPose7_626.boxKey 188160 (referenceBox7 (!canonicalBox7_626.bump)) = canonicalBox7_626 := by decide +kernel

theorem canonicalDecode7_626 : canonicalBox7_626.toKeyData 188160 = keys7Chunk19.get ⟨18, by decide⟩ := by
  change canonicalBox7_626.toKeyData 188160 = ⟨![2, (17 / 28), (5 / 14), (37 / 28), (12 / 7), (41 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(673 / 336), (64 / 105), (159 / 448), (3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_626 : keySolid (keys7Chunk19.get ⟨18, by decide⟩) = canonicalPose7_626.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_626 (box := canonicalBox7_626) (k := keys7Chunk19.get ⟨18, by decide⟩) (canonicalMatch7_626) (canonicalDecode7_626)

def canonicalPose7_627 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, false, false, true, true, false], ![2, 0, 0, 1, 2, 2, 0]⟩
def canonicalBox7_627 : BoxKey 7 :=
  ⟨![262080, 0, 120960, 315840, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 560, 121380, 316240, 241535, 274960, 108010], false⟩

theorem canonicalMatch7_627 :
    canonicalPose7_627.boxKey 188160 (referenceBox7 (!canonicalBox7_627.bump)) = canonicalBox7_627 := by decide +kernel

theorem canonicalDecode7_627 : canonicalBox7_627.toKeyData 188160 = keys7Chunk19.get ⟨19, by decide⟩ := by
  change canonicalBox7_627.toKeyData 188160 = ⟨![(39 / 28), 0, (9 / 14), (47 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (1 / 336), (289 / 448), (3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_627 : keySolid (keys7Chunk19.get ⟨19, by decide⟩) = canonicalPose7_627.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_627 (box := canonicalBox7_627) (k := keys7Chunk19.get ⟨19, by decide⟩) (canonicalMatch7_627) (canonicalDecode7_627)

def canonicalPose7_628 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, false, true, true, true, true], ![1, 0, 0, 2, 2, 2, 1]⟩
def canonicalBox7_628 : BoxKey 7 :=
  ⟨![315840, 120960, 0, 262080, 268800, 275520, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 560, 261632, 268310, 274960, 53375], false⟩

theorem canonicalMatch7_628 :
    canonicalPose7_628.boxKey 188160 (referenceBox7 (!canonicalBox7_628.bump)) = canonicalBox7_628 := by decide +kernel

theorem canonicalDecode7_628 : canonicalBox7_628.toKeyData 188160 = keys7Chunk19.get ⟨20, by decide⟩ := by
  change canonicalBox7_628.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 0, (39 / 28), (10 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (1 / 336), (146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_628 : keySolid (keys7Chunk19.get ⟨20, by decide⟩) = canonicalPose7_628.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_628 (box := canonicalBox7_628) (k := keys7Chunk19.get ⟨20, by decide⟩) (canonicalMatch7_628) (canonicalDecode7_628)

def canonicalPose7_629 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, false, false, true, false], ![2, 0, 1, 2, 1, 2, 0]⟩
def canonicalBox7_629 : BoxKey 7 :=
  ⟨![275520, 107520, 73920, 376320, 309120, 248640, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 73472, 376880, 309540, 248240, 134785], true⟩

theorem canonicalMatch7_629 :
    canonicalPose7_629.boxKey 188160 (referenceBox7 (!canonicalBox7_629.bump)) = canonicalBox7_629 := by decide +kernel

theorem canonicalDecode7_629 : canonicalBox7_629.toKeyData 188160 = keys7Chunk19.get ⟨21, by decide⟩ := by
  change canonicalBox7_629.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (11 / 28), 2, (23 / 14), (37 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (41 / 105), (673 / 336), (737 / 448), (3103 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_629 : keySolid (keys7Chunk19.get ⟨21, by decide⟩) = canonicalPose7_629.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_629 (box := canonicalBox7_629) (k := keys7Chunk19.get ⟨21, by decide⟩) (canonicalMatch7_629) (canonicalDecode7_629)

def canonicalPose7_630 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, true, true, false, true, false], ![2, 0, 1, 2, 1, 2, 0]⟩
def canonicalBox7_630 : BoxKey 7 :=
  ⟨![241920, 127680, 67200, 376320, 302400, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 128080, 66780, 375760, 302848, 268310, 101360], false⟩

theorem canonicalMatch7_630 :
    canonicalPose7_630.boxKey 188160 (referenceBox7 (!canonicalBox7_630.bump)) = canonicalBox7_630 := by decide +kernel

theorem canonicalDecode7_630 : canonicalBox7_630.toKeyData 188160 = keys7Chunk19.get ⟨22, by decide⟩ := by
  change canonicalBox7_630.toKeyData 188160 = ⟨![(9 / 7), (19 / 28), (5 / 14), 2, (45 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (1601 / 2352), (159 / 448), (671 / 336), (169 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_630 : keySolid (keys7Chunk19.get ⟨22, by decide⟩) = canonicalPose7_630.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_630 (box := canonicalBox7_630) (k := keys7Chunk19.get ⟨22, by decide⟩) (canonicalMatch7_630) (canonicalDecode7_630)

def canonicalPose7_631 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, true, false, true, true], ![1, 0, 0, 2, 2, 2, 1]⟩
def canonicalBox7_631 : BoxKey 7 :=
  ⟨![322560, 100800, 107520, 262080, 376320, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 101360, 108010, 261632, 376880, 254940, 60080], true⟩

theorem canonicalMatch7_631 :
    canonicalPose7_631.boxKey 188160 (referenceBox7 (!canonicalBox7_631.bump)) = canonicalBox7_631 := by decide +kernel

theorem canonicalDecode7_631 : canonicalBox7_631.toKeyData 188160 = keys7Chunk19.get ⟨23, by decide⟩ := by
  change canonicalBox7_631.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (4 / 7), (39 / 28), 2, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (673 / 336), (607 / 448), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_631 : keySolid (keys7Chunk19.get ⟨23, by decide⟩) = canonicalPose7_631.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_631 (box := canonicalBox7_631) (k := keys7Chunk19.get ⟨23, by decide⟩) (canonicalMatch7_631) (canonicalDecode7_631)

def canonicalPose7_632 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, false, true, false, false], ![2, 0, 0, 1, 2, 2, 0]⟩
def canonicalBox7_632 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 315840, 255360, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 316240, 254940, 376880, 114688], true⟩

theorem canonicalMatch7_632 :
    canonicalPose7_632.boxKey 188160 (referenceBox7 (!canonicalBox7_632.bump)) = canonicalBox7_632 := by decide +kernel

theorem canonicalDecode7_632 : canonicalBox7_632.toKeyData 188160 = keys7Chunk19.get ⟨24, by decide⟩ := by
  change canonicalBox7_632.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (47 / 28), (19 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (607 / 448), (673 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_632 : keySolid (keys7Chunk19.get ⟨24, by decide⟩) = canonicalPose7_632.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_632 (box := canonicalBox7_632) (k := keys7Chunk19.get ⟨24, by decide⟩) (canonicalMatch7_632) (canonicalDecode7_632)

def canonicalPose7_633 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, false, true, true, false, true, false], ![2, 0, 1, 2, 1, 2, 0]⟩
def canonicalBox7_633 : BoxKey 7 :=
  ⟨![268800, 100800, 53760, 248640, 309120, 262080, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 101360, 53375, 248240, 309540, 261632, 560], false⟩

theorem canonicalMatch7_633 :
    canonicalPose7_633.boxKey 188160 (referenceBox7 (!canonicalBox7_633.bump)) = canonicalBox7_633 := by decide +kernel

theorem canonicalDecode7_633 : canonicalBox7_633.toKeyData 188160 = keys7Chunk19.get ⟨25, by decide⟩ := by
  change canonicalBox7_633.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (2 / 7), (37 / 28), (23 / 14), (39 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (737 / 448), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_633 : keySolid (keys7Chunk19.get ⟨25, by decide⟩) = canonicalPose7_633.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_633 (box := canonicalBox7_633) (k := keys7Chunk19.get ⟨25, by decide⟩) (canonicalMatch7_633) (canonicalDecode7_633)

def canonicalPose7_634 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, false, true, true, false, true], ![2, 0, 0, 2, 2, 1, 2]⟩
def canonicalBox7_634 : BoxKey 7 :=
  ⟨![376320, 114240, 107520, 275520, 241920, 315840, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 114688, 108010, 274960, 241535, 316240, 254940], false⟩

theorem canonicalMatch7_634 :
    canonicalPose7_634.boxKey 188160 (referenceBox7 (!canonicalBox7_634.bump)) = canonicalBox7_634 := by decide +kernel

theorem canonicalDecode7_634 : canonicalBox7_634.toKeyData 188160 = keys7Chunk19.get ⟨26, by decide⟩ := by
  change canonicalBox7_634.toKeyData 188160 = ⟨![2, (17 / 28), (4 / 7), (41 / 28), (9 / 7), (47 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_634 : keySolid (keys7Chunk19.get ⟨26, by decide⟩) = canonicalPose7_634.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_634 (box := canonicalBox7_634) (k := keys7Chunk19.get ⟨26, by decide⟩) (canonicalMatch7_634) (canonicalDecode7_634)

def canonicalPose7_635 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, true, false, true, false, true, false], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_635 : BoxKey 7 :=
  ⟨![262080, 0, 107520, 275520, 322560, 248640, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, -560, 108010, 274960, 322945, 248240, 309540], true⟩

theorem canonicalMatch7_635 :
    canonicalPose7_635.boxKey 188160 (referenceBox7 (!canonicalBox7_635.bump)) = canonicalBox7_635 := by decide +kernel

theorem canonicalDecode7_635 : canonicalBox7_635.toKeyData 188160 = keys7Chunk19.get ⟨27, by decide⟩ := by
  change canonicalBox7_635.toKeyData 188160 = ⟨![(39 / 28), 0, (4 / 7), (41 / 28), (12 / 7), (37 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (-1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_635 : keySolid (keys7Chunk19.get ⟨27, by decide⟩) = canonicalPose7_635.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_635 (box := canonicalBox7_635) (k := keys7Chunk19.get ⟨27, by decide⟩) (canonicalMatch7_635) (canonicalDecode7_635)

def canonicalPose7_636 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, false, false, true, false, true, false], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_636 : BoxKey 7 :=
  ⟨![275520, 107520, 0, 262080, 309120, 248640, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 108010, 560, 261632, 309540, 248240, 322945], false⟩

theorem canonicalMatch7_636 :
    canonicalPose7_636.boxKey 188160 (referenceBox7 (!canonicalBox7_636.bump)) = canonicalBox7_636 := by decide +kernel

theorem canonicalDecode7_636 : canonicalBox7_636.toKeyData 188160 = keys7Chunk19.get ⟨28, by decide⟩ := by
  change canonicalBox7_636.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), 0, (39 / 28), (23 / 14), (37 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (1 / 336), (146 / 105), (737 / 448), (3103 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_636 : keySolid (keys7Chunk19.get ⟨28, by decide⟩) = canonicalPose7_636.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_636 (box := canonicalBox7_636) (k := keys7Chunk19.get ⟨28, by decide⟩) (canonicalMatch7_636) (canonicalDecode7_636)

def canonicalPose7_637 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, false, true, false, true], ![2, 0, 0, 2, 2, 1, 2]⟩
def canonicalBox7_637 : BoxKey 7 :=
  ⟨![275520, 107520, 114240, 376320, 255360, 315840, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 114688, 376880, 254940, 316240, 241535], true⟩

theorem canonicalMatch7_637 :
    canonicalPose7_637.boxKey 188160 (referenceBox7 (!canonicalBox7_637.bump)) = canonicalBox7_637 := by decide +kernel

theorem canonicalDecode7_637 : canonicalBox7_637.toKeyData 188160 = keys7Chunk19.get ⟨29, by decide⟩ := by
  change canonicalBox7_637.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (17 / 28), 2, (19 / 14), (47 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (64 / 105), (673 / 336), (607 / 448), (3953 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_637 : keySolid (keys7Chunk19.get ⟨29, by decide⟩) = canonicalPose7_637.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_637 (box := canonicalBox7_637) (k := keys7Chunk19.get ⟨29, by decide⟩) (canonicalMatch7_637) (canonicalDecode7_637)

def canonicalPose7_638 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, false, true, true], ![2, 1, 1, 2, 2, 2, 2]⟩
def canonicalBox7_638 : BoxKey 7 :=
  ⟨![275520, 53760, 60480, 255360, 376320, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 53375, 60080, 254940, 376880, 261632, 268310], true⟩

theorem canonicalMatch7_638 :
    canonicalPose7_638.boxKey 188160 (referenceBox7 (!canonicalBox7_638.bump)) = canonicalBox7_638 := by decide +kernel

theorem canonicalDecode7_638 : canonicalBox7_638.toKeyData 188160 = keys7Chunk19.get ⟨30, by decide⟩ := by
  change canonicalBox7_638.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (9 / 28), (19 / 14), 2, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (673 / 336), (146 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_638 : keySolid (keys7Chunk19.get ⟨30, by decide⟩) = canonicalPose7_638.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_638 (box := canonicalBox7_638) (k := keys7Chunk19.get ⟨30, by decide⟩) (canonicalMatch7_638) (canonicalDecode7_638)

def canonicalPose7_639 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, true, false, false, false], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_639 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 248640, 309120, 376320, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 248240, 309540, 376880, 302848], true⟩

theorem canonicalMatch7_639 :
    canonicalPose7_639.boxKey 188160 (referenceBox7 (!canonicalBox7_639.bump)) = canonicalBox7_639 := by decide +kernel

theorem canonicalDecode7_639 : canonicalBox7_639.toKeyData 188160 = keys7Chunk19.get ⟨31, by decide⟩ := by
  change canonicalBox7_639.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (37 / 28), (23 / 14), 2, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (673 / 336), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_639 : keySolid (keys7Chunk19.get ⟨31, by decide⟩) = canonicalPose7_639.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_639 (box := canonicalBox7_639) (k := keys7Chunk19.get ⟨31, by decide⟩) (canonicalMatch7_639) (canonicalDecode7_639)

theorem keys7Chunk19_canonical : ∀ k ∈ keys7Chunk19,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk19, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_608, canonicalSolid7_608⟩
  · exact ⟨canonicalPose7_609, canonicalSolid7_609⟩
  · exact ⟨canonicalPose7_610, canonicalSolid7_610⟩
  · exact ⟨canonicalPose7_611, canonicalSolid7_611⟩
  · exact ⟨canonicalPose7_612, canonicalSolid7_612⟩
  · exact ⟨canonicalPose7_613, canonicalSolid7_613⟩
  · exact ⟨canonicalPose7_614, canonicalSolid7_614⟩
  · exact ⟨canonicalPose7_615, canonicalSolid7_615⟩
  · exact ⟨canonicalPose7_616, canonicalSolid7_616⟩
  · exact ⟨canonicalPose7_617, canonicalSolid7_617⟩
  · exact ⟨canonicalPose7_618, canonicalSolid7_618⟩
  · exact ⟨canonicalPose7_619, canonicalSolid7_619⟩
  · exact ⟨canonicalPose7_620, canonicalSolid7_620⟩
  · exact ⟨canonicalPose7_621, canonicalSolid7_621⟩
  · exact ⟨canonicalPose7_622, canonicalSolid7_622⟩
  · exact ⟨canonicalPose7_623, canonicalSolid7_623⟩
  · exact ⟨canonicalPose7_624, canonicalSolid7_624⟩
  · exact ⟨canonicalPose7_625, canonicalSolid7_625⟩
  · exact ⟨canonicalPose7_626, canonicalSolid7_626⟩
  · exact ⟨canonicalPose7_627, canonicalSolid7_627⟩
  · exact ⟨canonicalPose7_628, canonicalSolid7_628⟩
  · exact ⟨canonicalPose7_629, canonicalSolid7_629⟩
  · exact ⟨canonicalPose7_630, canonicalSolid7_630⟩
  · exact ⟨canonicalPose7_631, canonicalSolid7_631⟩
  · exact ⟨canonicalPose7_632, canonicalSolid7_632⟩
  · exact ⟨canonicalPose7_633, canonicalSolid7_633⟩
  · exact ⟨canonicalPose7_634, canonicalSolid7_634⟩
  · exact ⟨canonicalPose7_635, canonicalSolid7_635⟩
  · exact ⟨canonicalPose7_636, canonicalSolid7_636⟩
  · exact ⟨canonicalPose7_637, canonicalSolid7_637⟩
  · exact ⟨canonicalPose7_638, canonicalSolid7_638⟩
  · exact ⟨canonicalPose7_639, canonicalSolid7_639⟩

#print axioms keys7Chunk19_canonical

end SparseMonotiles.Canonical
