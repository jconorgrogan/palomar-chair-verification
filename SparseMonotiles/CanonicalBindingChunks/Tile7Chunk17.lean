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

def canonicalPose7_544 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, false, false, false, false], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_544 : BoxKey 7 :=
  ⟨![302400, 107520, 100800, 134400, 127680, 309120, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 108010, 101360, 134785, 128080, 309540, 376880], true⟩

theorem canonicalMatch7_544 :
    canonicalPose7_544.boxKey 188160 (referenceBox7 (!canonicalBox7_544.bump)) = canonicalBox7_544 := by decide +kernel

theorem canonicalDecode7_544 : canonicalBox7_544.toKeyData 188160 = keys7Chunk17.get ⟨0, by decide⟩ := by
  change canonicalBox7_544.toKeyData 188160 = ⟨![(45 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28), (23 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_544 : keySolid (keys7Chunk17.get ⟨0, by decide⟩) = canonicalPose7_544.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_544 (box := canonicalBox7_544) (k := keys7Chunk17.get ⟨0, by decide⟩) (canonicalMatch7_544) (canonicalDecode7_544)

def canonicalPose7_545 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, false, false, true], ![1, 0, 0, 0, 0, 1, 2]⟩
def canonicalBox7_545 : BoxKey 7 :=
  ⟨![309120, 127680, 134400, 100800, 107520, 302400, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 128080, 134785, 101360, 108010, 302848, 375760], false⟩

theorem canonicalMatch7_545 :
    canonicalPose7_545.boxKey 188160 (referenceBox7 (!canonicalBox7_545.bump)) = canonicalBox7_545 := by decide +kernel

theorem canonicalDecode7_545 : canonicalBox7_545.toKeyData 188160 = keys7Chunk17.get ⟨1, by decide⟩ := by
  change canonicalBox7_545.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7), (45 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_545 : keySolid (keys7Chunk17.get ⟨1, by decide⟩) = canonicalPose7_545.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_545 (box := canonicalBox7_545) (k := keys7Chunk17.get ⟨1, by decide⟩) (canonicalMatch7_545) (canonicalDecode7_545)

def canonicalPose7_546 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, true, false, true, false, false], ![2, 0, 1, 0, 2, 0, 0]⟩
def canonicalBox7_546 : BoxKey 7 :=
  ⟨![376320, 120960, 60480, 134400, 275520, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 121380, 60080, 134785, 274960, 108010, 114688], false⟩

theorem canonicalMatch7_546 :
    canonicalPose7_546.boxKey 188160 (referenceBox7 (!canonicalBox7_546.bump)) = canonicalBox7_546 := by decide +kernel

theorem canonicalDecode7_546 : canonicalBox7_546.toKeyData 188160 = keys7Chunk17.get ⟨2, by decide⟩ := by
  change canonicalBox7_546.toKeyData 188160 = ⟨![2, (9 / 14), (9 / 28), (5 / 7), (41 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_546 : keySolid (keys7Chunk17.get ⟨2, by decide⟩) = canonicalPose7_546.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_546 (box := canonicalBox7_546) (k := keys7Chunk17.get ⟨2, by decide⟩) (canonicalMatch7_546) (canonicalDecode7_546)

def canonicalPose7_547 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, false, false, true, true, true], ![2, 0, 0, 0, 2, 1, 1]⟩
def canonicalBox7_547 : BoxKey 7 :=
  ⟨![255360, 0, 114240, 107520, 275520, 53760, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 560, 114688, 108010, 274960, 53375, 60080], false⟩

theorem canonicalMatch7_547 :
    canonicalPose7_547.boxKey 188160 (referenceBox7 (!canonicalBox7_547.bump)) = canonicalBox7_547 := by decide +kernel

theorem canonicalDecode7_547 : canonicalBox7_547.toKeyData 188160 = keys7Chunk17.get ⟨3, by decide⟩ := by
  change canonicalBox7_547.toKeyData 188160 = ⟨![(19 / 14), 0, (17 / 28), (4 / 7), (41 / 28), (2 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_547 : keySolid (keys7Chunk17.get ⟨3, by decide⟩) = canonicalPose7_547.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_547 (box := canonicalBox7_547) (k := keys7Chunk17.get ⟨3, by decide⟩) (canonicalMatch7_547) (canonicalDecode7_547)

def canonicalPose7_548 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, true, true, false, false], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_548 : BoxKey 7 :=
  ⟨![268800, 73920, 0, 67200, 248640, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 73472, -560, 66780, 248240, 134785, 101360], true⟩

theorem canonicalMatch7_548 :
    canonicalPose7_548.boxKey 188160 (referenceBox7 (!canonicalBox7_548.bump)) = canonicalBox7_548 := by decide +kernel

theorem canonicalDecode7_548 : canonicalBox7_548.toKeyData 188160 = keys7Chunk17.get ⟨4, by decide⟩ := by
  change canonicalBox7_548.toKeyData 188160 = ⟨![(10 / 7), (11 / 28), 0, (5 / 14), (37 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (41 / 105), (-1 / 336), (159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_548 : keySolid (keys7Chunk17.get ⟨4, by decide⟩) = canonicalPose7_548.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_548 (box := canonicalBox7_548) (k := keys7Chunk17.get ⟨4, by decide⟩) (canonicalMatch7_548) (canonicalDecode7_548)

def canonicalPose7_549 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, true, true, false, false], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_549 : BoxKey 7 :=
  ⟨![248640, 67200, 0, 73920, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 66780, 560, 73472, 268310, 101360, 134785], false⟩

theorem canonicalMatch7_549 :
    canonicalPose7_549.boxKey 188160 (referenceBox7 (!canonicalBox7_549.bump)) = canonicalBox7_549 := by decide +kernel

theorem canonicalDecode7_549 : canonicalBox7_549.toKeyData 188160 = keys7Chunk17.get ⟨5, by decide⟩ := by
  change canonicalBox7_549.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), 0, (11 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (1 / 336), (41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_549 : keySolid (keys7Chunk17.get ⟨5, by decide⟩) = canonicalPose7_549.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_549 (box := canonicalBox7_549) (k := keys7Chunk17.get ⟨5, by decide⟩) (canonicalMatch7_549) (canonicalDecode7_549)

def canonicalPose7_550 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, true, true, true, true], ![2, 0, 0, 0, 2, 1, 1]⟩
def canonicalBox7_550 : BoxKey 7 :=
  ⟨![275520, 107520, 114240, 0, 255360, 60480, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 114688, -560, 254940, 60080, 53375], true⟩

theorem canonicalMatch7_550 :
    canonicalPose7_550.boxKey 188160 (referenceBox7 (!canonicalBox7_550.bump)) = canonicalBox7_550 := by decide +kernel

theorem canonicalDecode7_550 : canonicalBox7_550.toKeyData 188160 = keys7Chunk17.get ⟨6, by decide⟩ := by
  change canonicalBox7_550.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (9 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (751 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_550 : keySolid (keys7Chunk17.get ⟨6, by decide⟩) = canonicalPose7_550.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_550 (box := canonicalBox7_550) (k := keys7Chunk17.get ⟨6, by decide⟩) (canonicalMatch7_550) (canonicalDecode7_550)

def canonicalPose7_551 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, true, false, false, false, false], ![2, 0, 1, 0, 2, 0, 0]⟩
def canonicalBox7_551 : BoxKey 7 :=
  ⟨![275520, 134400, 60480, 120960, 376320, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 134785, 60080, 121380, 376880, 114688, 108010], true⟩

theorem canonicalMatch7_551 :
    canonicalPose7_551.boxKey 188160 (referenceBox7 (!canonicalBox7_551.bump)) = canonicalBox7_551 := by decide +kernel

theorem canonicalDecode7_551 : canonicalBox7_551.toKeyData 188160 = keys7Chunk17.get ⟨7, by decide⟩ := by
  change canonicalBox7_551.toKeyData 188160 = ⟨![(41 / 28), (5 / 7), (9 / 28), (9 / 14), 2, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (673 / 336), (64 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_551 : keySolid (keys7Chunk17.get ⟨7, by decide⟩) = canonicalPose7_551.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_551 (box := canonicalBox7_551) (k := keys7Chunk17.get ⟨7, by decide⟩) (canonicalMatch7_551) (canonicalDecode7_551)

def canonicalPose7_552 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, true, false, true, true, false, false], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_552 : BoxKey 7 :=
  ⟨![275520, 53760, 127680, 67200, 262080, 0, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 53375, 128080, 66780, 261632, 560, 108010], false⟩

theorem canonicalMatch7_552 :
    canonicalPose7_552.boxKey 188160 (referenceBox7 (!canonicalBox7_552.bump)) = canonicalBox7_552 := by decide +kernel

theorem canonicalDecode7_552 : canonicalBox7_552.toKeyData 188160 = keys7Chunk17.get ⟨8, by decide⟩ := by
  change canonicalBox7_552.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (19 / 28), (5 / 14), (39 / 28), 0, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105), (1 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_552 : keySolid (keys7Chunk17.get ⟨8, by decide⟩) = canonicalPose7_552.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_552 (box := canonicalBox7_552) (k := keys7Chunk17.get ⟨8, by decide⟩) (canonicalMatch7_552) (canonicalDecode7_552)

def canonicalPose7_553 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, true, false, true, true, false, true], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_553 : BoxKey 7 :=
  ⟨![262080, 67200, 127680, 53760, 275520, 107520, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 66780, 128080, 53375, 274960, 108010, -560], true⟩

theorem canonicalMatch7_553 :
    canonicalPose7_553.boxKey 188160 (referenceBox7 (!canonicalBox7_553.bump)) = canonicalBox7_553 := by decide +kernel

theorem canonicalDecode7_553 : canonicalBox7_553.toKeyData 188160 = keys7Chunk17.get ⟨9, by decide⟩ := by
  change canonicalBox7_553.toKeyData 188160 = ⟨![(39 / 28), (5 / 14), (19 / 28), (2 / 7), (41 / 28), (4 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_553 : keySolid (keys7Chunk17.get ⟨9, by decide⟩) = canonicalPose7_553.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_553 (box := canonicalBox7_553) (k := keys7Chunk17.get ⟨9, by decide⟩) (canonicalMatch7_553) (canonicalDecode7_553)

def canonicalPose7_554 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, false, false, true, true], ![2, 0, 0, 0, 1, 1, 2]⟩
def canonicalBox7_554 : BoxKey 7 :=
  ⟨![376320, 114240, 107520, 100800, 322560, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 114688, 108010, 101360, 322945, 60080, 254940], true⟩

theorem canonicalMatch7_554 :
    canonicalPose7_554.boxKey 188160 (referenceBox7 (!canonicalBox7_554.bump)) = canonicalBox7_554 := by decide +kernel

theorem canonicalDecode7_554 : canonicalBox7_554.toKeyData 188160 = keys7Chunk17.get ⟨10, by decide⟩ := by
  change canonicalBox7_554.toKeyData 188160 = ⟨![2, (17 / 28), (4 / 7), (15 / 28), (12 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_554 : keySolid (keys7Chunk17.get ⟨10, by decide⟩) = canonicalPose7_554.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_554 (box := canonicalBox7_554) (k := keys7Chunk17.get ⟨10, by decide⟩) (canonicalMatch7_554) (canonicalDecode7_554)

def canonicalPose7_555 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, true, false, true, false, true], ![1, 0, 1, 0, 2, 0, 2]⟩
def canonicalBox7_555 : BoxKey 7 :=
  ⟨![302400, 0, 67200, 127680, 241920, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, 560, 66780, 128080, 241535, 101360, 268310], false⟩

theorem canonicalMatch7_555 :
    canonicalPose7_555.boxKey 188160 (referenceBox7 (!canonicalBox7_555.bump)) = canonicalBox7_555 := by decide +kernel

theorem canonicalDecode7_555 : canonicalBox7_555.toKeyData 188160 = keys7Chunk17.get ⟨11, by decide⟩ := by
  change canonicalBox7_555.toKeyData 188160 = ⟨![(45 / 28), 0, (5 / 14), (19 / 28), (9 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_555 : keySolid (keys7Chunk17.get ⟨11, by decide⟩) = canonicalPose7_555.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_555 (box := canonicalBox7_555) (k := keys7Chunk17.get ⟨11, by decide⟩) (canonicalMatch7_555) (canonicalDecode7_555)

def canonicalPose7_556 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, true, false, true, false, true], ![1, 0, 1, 0, 2, 0, 2]⟩
def canonicalBox7_556 : BoxKey 7 :=
  ⟨![309120, 0, 73920, 107520, 275520, 134400, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, -560, 73472, 108010, 274960, 134785, 248240], true⟩

theorem canonicalMatch7_556 :
    canonicalPose7_556.boxKey 188160 (referenceBox7 (!canonicalBox7_556.bump)) = canonicalBox7_556 := by decide +kernel

theorem canonicalDecode7_556 : canonicalBox7_556.toKeyData 188160 = keys7Chunk17.get ⟨12, by decide⟩ := by
  change canonicalBox7_556.toKeyData 188160 = ⟨![(23 / 14), 0, (11 / 28), (4 / 7), (41 / 28), (5 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (-1 / 336), (41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_556 : keySolid (keys7Chunk17.get ⟨12, by decide⟩) = canonicalPose7_556.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_556 (box := canonicalBox7_556) (k := keys7Chunk17.get ⟨12, by decide⟩) (canonicalMatch7_556) (canonicalDecode7_556)

def canonicalPose7_557 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, false, false, true, true], ![2, 0, 0, 0, 1, 1, 2]⟩
def canonicalBox7_557 : BoxKey 7 :=
  ⟨![268800, 114240, 0, 120960, 315840, 53760, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 114688, 560, 121380, 316240, 53375, 274960], false⟩

theorem canonicalMatch7_557 :
    canonicalPose7_557.boxKey 188160 (referenceBox7 (!canonicalBox7_557.bump)) = canonicalBox7_557 := by decide +kernel

theorem canonicalDecode7_557 : canonicalBox7_557.toKeyData 188160 = keys7Chunk17.get ⟨13, by decide⟩ := by
  change canonicalBox7_557.toKeyData 188160 = ⟨![(10 / 7), (17 / 28), 0, (9 / 14), (47 / 28), (2 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (64 / 105), (1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_557 : keySolid (keys7Chunk17.get ⟨13, by decide⟩) = canonicalPose7_557.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_557 (box := canonicalBox7_557) (k := keys7Chunk17.get ⟨13, by decide⟩) (canonicalMatch7_557) (canonicalDecode7_557)

def canonicalPose7_558 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, false, false, true, false, true], ![2, 1, 0, 0, 2, 0, 2]⟩
def canonicalBox7_558 : BoxKey 7 :=
  ⟨![241920, 60480, 120960, 0, 262080, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 60080, 121380, 560, 261632, 108010, 274960], false⟩

theorem canonicalMatch7_558 :
    canonicalPose7_558.boxKey 188160 (referenceBox7 (!canonicalBox7_558.bump)) = canonicalBox7_558 := by decide +kernel

theorem canonicalDecode7_558 : canonicalBox7_558.toKeyData 188160 = keys7Chunk17.get ⟨14, by decide⟩ := by
  change canonicalBox7_558.toKeyData 188160 = ⟨![(9 / 7), (9 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (751 / 2352), (289 / 448), (1 / 336), (146 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_558 : keySolid (keys7Chunk17.get ⟨14, by decide⟩) = canonicalPose7_558.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_558 (box := canonicalBox7_558) (k := keys7Chunk17.get ⟨14, by decide⟩) (canonicalMatch7_558) (canonicalDecode7_558)

def canonicalPose7_559 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, false, true, false, false, false, true], ![1, 0, 1, 0, 2, 0, 2]⟩
def canonicalBox7_559 : BoxKey 7 :=
  ⟨![322560, 127680, 67200, 114240, 376320, 107520, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 128080, 66780, 114688, 376880, 108010, 274960], true⟩

theorem canonicalMatch7_559 :
    canonicalPose7_559.boxKey 188160 (referenceBox7 (!canonicalBox7_559.bump)) = canonicalBox7_559 := by decide +kernel

theorem canonicalDecode7_559 : canonicalBox7_559.toKeyData 188160 = keys7Chunk17.get ⟨15, by decide⟩ := by
  change canonicalBox7_559.toKeyData 188160 = ⟨![(12 / 7), (19 / 28), (5 / 14), (17 / 28), 2, (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (1601 / 2352), (159 / 448), (64 / 105), (673 / 336), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_559 : keySolid (keys7Chunk17.get ⟨15, by decide⟩) = canonicalPose7_559.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_559 (box := canonicalBox7_559) (k := keys7Chunk17.get ⟨15, by decide⟩) (canonicalMatch7_559) (canonicalDecode7_559)

def canonicalPose7_560 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, false, true, false, true, false, true], ![1, 0, 1, 0, 2, 0, 2]⟩
def canonicalBox7_560 : BoxKey 7 :=
  ⟨![309120, 127680, 53760, 100800, 268800, 0, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 128080, 53375, 101360, 268310, 560, 261632], false⟩

theorem canonicalMatch7_560 :
    canonicalPose7_560.boxKey 188160 (referenceBox7 (!canonicalBox7_560.bump)) = canonicalBox7_560 := by decide +kernel

theorem canonicalDecode7_560 : canonicalBox7_560.toKeyData 188160 = keys7Chunk17.get ⟨16, by decide⟩ := by
  change canonicalBox7_560.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (2 / 7), (15 / 28), (10 / 7), 0, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (1 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_560 : keySolid (keys7Chunk17.get ⟨16, by decide⟩) = canonicalPose7_560.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_560 (box := canonicalBox7_560) (k := keys7Chunk17.get ⟨16, by decide⟩) (canonicalMatch7_560) (canonicalDecode7_560)

def canonicalPose7_561 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, false, false, true, false, false], ![2, 1, 0, 0, 2, 0, 2]⟩
def canonicalBox7_561 : BoxKey 7 :=
  ⟨![255360, 60480, 134400, 100800, 268800, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 134785, 101360, 268310, 114688, 376880], true⟩

theorem canonicalMatch7_561 :
    canonicalPose7_561.boxKey 188160 (referenceBox7 (!canonicalBox7_561.bump)) = canonicalBox7_561 := by decide +kernel

theorem canonicalDecode7_561 : canonicalBox7_561.toKeyData 188160 = keys7Chunk17.get ⟨17, by decide⟩ := by
  change canonicalBox7_561.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (5 / 7), (15 / 28), (10 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_561 : keySolid (keys7Chunk17.get ⟨17, by decide⟩) = canonicalPose7_561.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_561 (box := canonicalBox7_561) (k := keys7Chunk17.get ⟨17, by decide⟩) (canonicalMatch7_561) (canonicalDecode7_561)

def canonicalPose7_562 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, false, true, false, false, true, false], ![2, 0, 1, 0, 1, 2, 0]⟩
def canonicalBox7_562 : BoxKey 7 :=
  ⟨![376320, 114240, 67200, 127680, 322560, 275520, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![375760, 114688, 66780, 128080, 322945, 274960, 108010], false⟩

theorem canonicalMatch7_562 :
    canonicalPose7_562.boxKey 188160 (referenceBox7 (!canonicalBox7_562.bump)) = canonicalBox7_562 := by decide +kernel

theorem canonicalDecode7_562 : canonicalBox7_562.toKeyData 188160 = keys7Chunk17.get ⟨18, by decide⟩ := by
  change canonicalBox7_562.toKeyData 188160 = ⟨![2, (17 / 28), (5 / 14), (19 / 28), (12 / 7), (41 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(671 / 336), (64 / 105), (159 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_562 : keySolid (keys7Chunk17.get ⟨18, by decide⟩) = canonicalPose7_562.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_562 (box := canonicalBox7_562) (k := keys7Chunk17.get ⟨18, by decide⟩) (canonicalMatch7_562) (canonicalDecode7_562)

def canonicalPose7_563 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, false, true, true, true, false], ![2, 0, 0, 1, 2, 2, 0]⟩
def canonicalBox7_563 : BoxKey 7 :=
  ⟨![262080, 0, 120960, 60480, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, -560, 121380, 60080, 241535, 274960, 108010], true⟩

theorem canonicalMatch7_563 :
    canonicalPose7_563.boxKey 188160 (referenceBox7 (!canonicalBox7_563.bump)) = canonicalBox7_563 := by decide +kernel

theorem canonicalDecode7_563 : canonicalBox7_563.toKeyData 188160 = keys7Chunk17.get ⟨19, by decide⟩ := by
  change canonicalBox7_563.toKeyData 188160 = ⟨![(39 / 28), 0, (9 / 14), (9 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (-1 / 336), (289 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_563 : keySolid (keys7Chunk17.get ⟨19, by decide⟩) = canonicalPose7_563.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_563 (box := canonicalBox7_563) (k := keys7Chunk17.get ⟨19, by decide⟩) (canonicalMatch7_563) (canonicalDecode7_563)

def canonicalPose7_564 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, true, false, true, true, true], ![1, 0, 0, 0, 2, 2, 1]⟩
def canonicalBox7_564 : BoxKey 7 :=
  ⟨![315840, 120960, 0, 114240, 268800, 275520, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, -560, 114688, 268310, 274960, 53375], true⟩

theorem canonicalMatch7_564 :
    canonicalPose7_564.boxKey 188160 (referenceBox7 (!canonicalBox7_564.bump)) = canonicalBox7_564 := by decide +kernel

theorem canonicalDecode7_564 : canonicalBox7_564.toKeyData 188160 = keys7Chunk17.get ⟨20, by decide⟩ := by
  change canonicalBox7_564.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 0, (17 / 28), (10 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (-1 / 336), (64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_564 : keySolid (keys7Chunk17.get ⟨20, by decide⟩) = canonicalPose7_564.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_564 (box := canonicalBox7_564) (k := keys7Chunk17.get ⟨20, by decide⟩) (canonicalMatch7_564) (canonicalDecode7_564)

def canonicalPose7_565 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, false, false, true, false], ![2, 0, 1, 0, 1, 2, 0]⟩
def canonicalBox7_565 : BoxKey 7 :=
  ⟨![275520, 107520, 73920, 0, 309120, 248640, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 73472, 560, 309540, 248240, 134785], false⟩

theorem canonicalMatch7_565 :
    canonicalPose7_565.boxKey 188160 (referenceBox7 (!canonicalBox7_565.bump)) = canonicalBox7_565 := by decide +kernel

theorem canonicalDecode7_565 : canonicalBox7_565.toKeyData 188160 = keys7Chunk17.get ⟨21, by decide⟩ := by
  change canonicalBox7_565.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (11 / 28), 0, (23 / 14), (37 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (41 / 105), (1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_565 : keySolid (keys7Chunk17.get ⟨21, by decide⟩) = canonicalPose7_565.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_565 (box := canonicalBox7_565) (k := keys7Chunk17.get ⟨21, by decide⟩) (canonicalMatch7_565) (canonicalDecode7_565)

def canonicalPose7_566 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, true, true, false, true, false], ![2, 0, 1, 0, 1, 2, 0]⟩
def canonicalBox7_566 : BoxKey 7 :=
  ⟨![241920, 127680, 67200, 0, 302400, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 128080, 66780, -560, 302848, 268310, 101360], true⟩

theorem canonicalMatch7_566 :
    canonicalPose7_566.boxKey 188160 (referenceBox7 (!canonicalBox7_566.bump)) = canonicalBox7_566 := by decide +kernel

theorem canonicalDecode7_566 : canonicalBox7_566.toKeyData 188160 = keys7Chunk17.get ⟨22, by decide⟩ := by
  change canonicalBox7_566.toKeyData 188160 = ⟨![(9 / 7), (19 / 28), (5 / 14), 0, (45 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (1601 / 2352), (159 / 448), (-1 / 336), (169 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_566 : keySolid (keys7Chunk17.get ⟨22, by decide⟩) = canonicalPose7_566.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_566 (box := canonicalBox7_566) (k := keys7Chunk17.get ⟨22, by decide⟩) (canonicalMatch7_566) (canonicalDecode7_566)

def canonicalPose7_567 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, false, true, true, true], ![1, 0, 0, 0, 2, 2, 1]⟩
def canonicalBox7_567 : BoxKey 7 :=
  ⟨![322560, 100800, 107520, 114240, 376320, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 101360, 108010, 114688, 375760, 254940, 60080], false⟩

theorem canonicalMatch7_567 :
    canonicalPose7_567.boxKey 188160 (referenceBox7 (!canonicalBox7_567.bump)) = canonicalBox7_567 := by decide +kernel

theorem canonicalDecode7_567 : canonicalBox7_567.toKeyData 188160 = keys7Chunk17.get ⟨23, by decide⟩ := by
  change canonicalBox7_567.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (4 / 7), (17 / 28), 2, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (671 / 336), (607 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_567 : keySolid (keys7Chunk17.get ⟨23, by decide⟩) = canonicalPose7_567.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_567 (box := canonicalBox7_567) (k := keys7Chunk17.get ⟨23, by decide⟩) (canonicalMatch7_567) (canonicalDecode7_567)

def canonicalPose7_568 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, true, true, true, false], ![2, 0, 0, 1, 2, 2, 0]⟩
def canonicalBox7_568 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 60480, 255360, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 60080, 254940, 375760, 114688], false⟩

theorem canonicalMatch7_568 :
    canonicalPose7_568.boxKey 188160 (referenceBox7 (!canonicalBox7_568.bump)) = canonicalBox7_568 := by decide +kernel

theorem canonicalDecode7_568 : canonicalBox7_568.toKeyData 188160 = keys7Chunk17.get ⟨24, by decide⟩ := by
  change canonicalBox7_568.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (9 / 28), (19 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352), (607 / 448), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_568 : keySolid (keys7Chunk17.get ⟨24, by decide⟩) = canonicalPose7_568.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_568 (box := canonicalBox7_568) (k := keys7Chunk17.get ⟨24, by decide⟩) (canonicalMatch7_568) (canonicalDecode7_568)

def canonicalPose7_569 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, false, true, false, false, true, true], ![2, 0, 1, 0, 1, 2, 0]⟩
def canonicalBox7_569 : BoxKey 7 :=
  ⟨![268800, 100800, 53760, 127680, 309120, 262080, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 101360, 53375, 128080, 309540, 261632, -560], true⟩

theorem canonicalMatch7_569 :
    canonicalPose7_569.boxKey 188160 (referenceBox7 (!canonicalBox7_569.bump)) = canonicalBox7_569 := by decide +kernel

theorem canonicalDecode7_569 : canonicalBox7_569.toKeyData 188160 = keys7Chunk17.get ⟨25, by decide⟩ := by
  change canonicalBox7_569.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (2 / 7), (19 / 28), (23 / 14), (39 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_569 : keySolid (keys7Chunk17.get ⟨25, by decide⟩) = canonicalPose7_569.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_569 (box := canonicalBox7_569) (k := keys7Chunk17.get ⟨25, by decide⟩) (canonicalMatch7_569) (canonicalDecode7_569)

def canonicalPose7_570 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, true, false, true, true, true], ![2, 0, 1, 0, 2, 2, 2]⟩
def canonicalBox7_570 : BoxKey 7 :=
  ⟨![376320, 120960, 60480, 134400, 275520, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 121380, 60080, 134785, 274960, 268310, 261632], false⟩

theorem canonicalMatch7_570 :
    canonicalPose7_570.boxKey 188160 (referenceBox7 (!canonicalBox7_570.bump)) = canonicalBox7_570 := by decide +kernel

theorem canonicalDecode7_570 : canonicalBox7_570.toKeyData 188160 = keys7Chunk17.get ⟨26, by decide⟩ := by
  change canonicalBox7_570.toKeyData 188160 = ⟨![2, (9 / 14), (9 / 28), (5 / 7), (41 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_570 : keySolid (keys7Chunk17.get ⟨26, by decide⟩) = canonicalPose7_570.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_570 (box := canonicalBox7_570) (k := keys7Chunk17.get ⟨26, by decide⟩) (canonicalMatch7_570) (canonicalDecode7_570)

def canonicalPose7_571 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, false, false, true, false, false], ![2, 0, 0, 0, 2, 1, 1]⟩
def canonicalBox7_571 : BoxKey 7 :=
  ⟨![255360, 0, 114240, 107520, 275520, 322560, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 560, 114688, 108010, 274960, 322945, 316240], false⟩

theorem canonicalMatch7_571 :
    canonicalPose7_571.boxKey 188160 (referenceBox7 (!canonicalBox7_571.bump)) = canonicalBox7_571 := by decide +kernel

theorem canonicalDecode7_571 : canonicalBox7_571.toKeyData 188160 = keys7Chunk17.get ⟨27, by decide⟩ := by
  change canonicalBox7_571.toKeyData 188160 = ⟨![(19 / 14), 0, (17 / 28), (4 / 7), (41 / 28), (12 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_571 : keySolid (keys7Chunk17.get ⟨27, by decide⟩) = canonicalPose7_571.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_571 (box := canonicalBox7_571) (k := keys7Chunk17.get ⟨27, by decide⟩) (canonicalMatch7_571) (canonicalDecode7_571)

def canonicalPose7_572 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, true, true, true, true], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_572 : BoxKey 7 :=
  ⟨![268800, 73920, 0, 67200, 248640, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 73472, -560, 66780, 248240, 241535, 274960], true⟩

theorem canonicalMatch7_572 :
    canonicalPose7_572.boxKey 188160 (referenceBox7 (!canonicalBox7_572.bump)) = canonicalBox7_572 := by decide +kernel

theorem canonicalDecode7_572 : canonicalBox7_572.toKeyData 188160 = keys7Chunk17.get ⟨28, by decide⟩ := by
  change canonicalBox7_572.toKeyData 188160 = ⟨![(10 / 7), (11 / 28), 0, (5 / 14), (37 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (41 / 105), (-1 / 336), (159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_572 : keySolid (keys7Chunk17.get ⟨28, by decide⟩) = canonicalPose7_572.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_572 (box := canonicalBox7_572) (k := keys7Chunk17.get ⟨28, by decide⟩) (canonicalMatch7_572) (canonicalDecode7_572)

def canonicalPose7_573 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, true, true, true, true], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_573 : BoxKey 7 :=
  ⟨![248640, 67200, 0, 73920, 268800, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 66780, 560, 73472, 268310, 274960, 241535], false⟩

theorem canonicalMatch7_573 :
    canonicalPose7_573.boxKey 188160 (referenceBox7 (!canonicalBox7_573.bump)) = canonicalBox7_573 := by decide +kernel

theorem canonicalDecode7_573 : canonicalBox7_573.toKeyData 188160 = keys7Chunk17.get ⟨29, by decide⟩ := by
  change canonicalBox7_573.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), 0, (11 / 28), (10 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (1 / 336), (41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_573 : keySolid (keys7Chunk17.get ⟨29, by decide⟩) = canonicalPose7_573.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_573 (box := canonicalBox7_573) (k := keys7Chunk17.get ⟨29, by decide⟩) (canonicalMatch7_573) (canonicalDecode7_573)

def canonicalPose7_574 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, true, true, false, false], ![2, 0, 0, 0, 2, 1, 1]⟩
def canonicalBox7_574 : BoxKey 7 :=
  ⟨![275520, 107520, 114240, 0, 255360, 315840, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 114688, -560, 254940, 316240, 322945], true⟩

theorem canonicalMatch7_574 :
    canonicalPose7_574.boxKey 188160 (referenceBox7 (!canonicalBox7_574.bump)) = canonicalBox7_574 := by decide +kernel

theorem canonicalDecode7_574 : canonicalBox7_574.toKeyData 188160 = keys7Chunk17.get ⟨30, by decide⟩ := by
  change canonicalBox7_574.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (47 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_574 : keySolid (keys7Chunk17.get ⟨30, by decide⟩) = canonicalPose7_574.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_574 (box := canonicalBox7_574) (k := keys7Chunk17.get ⟨30, by decide⟩) (canonicalMatch7_574) (canonicalDecode7_574)

def canonicalPose7_575 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, true, false, false, true, true], ![2, 0, 1, 0, 2, 2, 2]⟩
def canonicalBox7_575 : BoxKey 7 :=
  ⟨![275520, 134400, 60480, 120960, 376320, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 134785, 60080, 121380, 376880, 261632, 268310], true⟩

theorem canonicalMatch7_575 :
    canonicalPose7_575.boxKey 188160 (referenceBox7 (!canonicalBox7_575.bump)) = canonicalBox7_575 := by decide +kernel

theorem canonicalDecode7_575 : canonicalBox7_575.toKeyData 188160 = keys7Chunk17.get ⟨31, by decide⟩ := by
  change canonicalBox7_575.toKeyData 188160 = ⟨![(41 / 28), (5 / 7), (9 / 28), (9 / 14), 2, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_575 : keySolid (keys7Chunk17.get ⟨31, by decide⟩) = canonicalPose7_575.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_575 (box := canonicalBox7_575) (k := keys7Chunk17.get ⟨31, by decide⟩) (canonicalMatch7_575) (canonicalDecode7_575)

theorem keys7Chunk17_canonical : ∀ k ∈ keys7Chunk17,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk17, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_544, canonicalSolid7_544⟩
  · exact ⟨canonicalPose7_545, canonicalSolid7_545⟩
  · exact ⟨canonicalPose7_546, canonicalSolid7_546⟩
  · exact ⟨canonicalPose7_547, canonicalSolid7_547⟩
  · exact ⟨canonicalPose7_548, canonicalSolid7_548⟩
  · exact ⟨canonicalPose7_549, canonicalSolid7_549⟩
  · exact ⟨canonicalPose7_550, canonicalSolid7_550⟩
  · exact ⟨canonicalPose7_551, canonicalSolid7_551⟩
  · exact ⟨canonicalPose7_552, canonicalSolid7_552⟩
  · exact ⟨canonicalPose7_553, canonicalSolid7_553⟩
  · exact ⟨canonicalPose7_554, canonicalSolid7_554⟩
  · exact ⟨canonicalPose7_555, canonicalSolid7_555⟩
  · exact ⟨canonicalPose7_556, canonicalSolid7_556⟩
  · exact ⟨canonicalPose7_557, canonicalSolid7_557⟩
  · exact ⟨canonicalPose7_558, canonicalSolid7_558⟩
  · exact ⟨canonicalPose7_559, canonicalSolid7_559⟩
  · exact ⟨canonicalPose7_560, canonicalSolid7_560⟩
  · exact ⟨canonicalPose7_561, canonicalSolid7_561⟩
  · exact ⟨canonicalPose7_562, canonicalSolid7_562⟩
  · exact ⟨canonicalPose7_563, canonicalSolid7_563⟩
  · exact ⟨canonicalPose7_564, canonicalSolid7_564⟩
  · exact ⟨canonicalPose7_565, canonicalSolid7_565⟩
  · exact ⟨canonicalPose7_566, canonicalSolid7_566⟩
  · exact ⟨canonicalPose7_567, canonicalSolid7_567⟩
  · exact ⟨canonicalPose7_568, canonicalSolid7_568⟩
  · exact ⟨canonicalPose7_569, canonicalSolid7_569⟩
  · exact ⟨canonicalPose7_570, canonicalSolid7_570⟩
  · exact ⟨canonicalPose7_571, canonicalSolid7_571⟩
  · exact ⟨canonicalPose7_572, canonicalSolid7_572⟩
  · exact ⟨canonicalPose7_573, canonicalSolid7_573⟩
  · exact ⟨canonicalPose7_574, canonicalSolid7_574⟩
  · exact ⟨canonicalPose7_575, canonicalSolid7_575⟩

#print axioms keys7Chunk17_canonical

end SparseMonotiles.Canonical
