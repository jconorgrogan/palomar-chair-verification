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

def canonicalPose7_576 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, true, false, true, true, true, true], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_576 : BoxKey 7 :=
  ⟨![275520, 53760, 127680, 67200, 262080, 376320, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 53375, 128080, 66780, 261632, 375760, 268310], false⟩

theorem canonicalMatch7_576 :
    canonicalPose7_576.boxKey 188160 (referenceBox7 (!canonicalBox7_576.bump)) = canonicalBox7_576 := by decide +kernel

theorem canonicalDecode7_576 : canonicalBox7_576.toKeyData 188160 = keys7Chunk18.get ⟨0, by decide⟩ := by
  change canonicalBox7_576.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (19 / 28), (5 / 14), (39 / 28), 2, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105), (671 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_576 : keySolid (keys7Chunk18.get ⟨0, by decide⟩) = canonicalPose7_576.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_576 (box := canonicalBox7_576) (k := keys7Chunk18.get ⟨0, by decide⟩) (canonicalMatch7_576) (canonicalDecode7_576)

def canonicalPose7_577 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, true, false, true, true, true, false], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_577 : BoxKey 7 :=
  ⟨![262080, 67200, 127680, 53760, 275520, 268800, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 66780, 128080, 53375, 274960, 268310, 376880], true⟩

theorem canonicalMatch7_577 :
    canonicalPose7_577.boxKey 188160 (referenceBox7 (!canonicalBox7_577.bump)) = canonicalBox7_577 := by decide +kernel

theorem canonicalDecode7_577 : canonicalBox7_577.toKeyData 188160 = keys7Chunk18.get ⟨1, by decide⟩ := by
  change canonicalBox7_577.toKeyData 188160 = ⟨![(39 / 28), (5 / 14), (19 / 28), (2 / 7), (41 / 28), (10 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_577 : keySolid (keys7Chunk18.get ⟨1, by decide⟩) = canonicalPose7_577.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_577 (box := canonicalBox7_577) (k := keys7Chunk18.get ⟨1, by decide⟩) (canonicalMatch7_577) (canonicalDecode7_577)

def canonicalPose7_578 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, true, false, true, false], ![2, 0, 0, 2, 0, 1, 0]⟩
def canonicalBox7_578 : BoxKey 7 :=
  ⟨![376320, 114240, 107520, 275520, 134400, 60480, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 114688, 108010, 274960, 134785, 60080, 121380], true⟩

theorem canonicalMatch7_578 :
    canonicalPose7_578.boxKey 188160 (referenceBox7 (!canonicalBox7_578.bump)) = canonicalBox7_578 := by decide +kernel

theorem canonicalDecode7_578 : canonicalBox7_578.toKeyData 188160 = keys7Chunk18.get ⟨2, by decide⟩ := by
  change canonicalBox7_578.toKeyData 188160 = ⟨![2, (17 / 28), (4 / 7), (41 / 28), (5 / 7), (9 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (751 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_578 : keySolid (keys7Chunk18.get ⟨2, by decide⟩) = canonicalPose7_578.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_578 (box := canonicalBox7_578) (k := keys7Chunk18.get ⟨2, by decide⟩) (canonicalMatch7_578) (canonicalDecode7_578)

def canonicalPose7_579 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, false, false, true, true, false, true], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_579 : BoxKey 7 :=
  ⟨![262080, 0, 107520, 275520, 53760, 127680, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, 560, 108010, 274960, 53375, 128080, 66780], false⟩

theorem canonicalMatch7_579 :
    canonicalPose7_579.boxKey 188160 (referenceBox7 (!canonicalBox7_579.bump)) = canonicalBox7_579 := by decide +kernel

theorem canonicalDecode7_579 : canonicalBox7_579.toKeyData 188160 = keys7Chunk18.get ⟨3, by decide⟩ := by
  change canonicalBox7_579.toKeyData 188160 = ⟨![(39 / 28), 0, (4 / 7), (41 / 28), (2 / 7), (19 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_579 : keySolid (keys7Chunk18.get ⟨3, by decide⟩) = canonicalPose7_579.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_579 (box := canonicalBox7_579) (k := keys7Chunk18.get ⟨3, by decide⟩) (canonicalMatch7_579) (canonicalDecode7_579)

def canonicalPose7_580 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, false, true, true, true, false, true], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_580 : BoxKey 7 :=
  ⟨![275520, 107520, 0, 262080, 67200, 127680, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 108010, -560, 261632, 66780, 128080, 53375], true⟩

theorem canonicalMatch7_580 :
    canonicalPose7_580.boxKey 188160 (referenceBox7 (!canonicalBox7_580.bump)) = canonicalBox7_580 := by decide +kernel

theorem canonicalDecode7_580 : canonicalBox7_580.toKeyData 188160 = keys7Chunk18.get ⟨4, by decide⟩ := by
  change canonicalBox7_580.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), 0, (39 / 28), (5 / 14), (19 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (-1 / 336), (146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_580 : keySolid (keys7Chunk18.get ⟨4, by decide⟩) = canonicalPose7_580.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_580 (box := canonicalBox7_580) (k := keys7Chunk18.get ⟨4, by decide⟩) (canonicalMatch7_580) (canonicalDecode7_580)

def canonicalPose7_581 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, true, false, true, false], ![2, 0, 0, 2, 0, 1, 0]⟩
def canonicalBox7_581 : BoxKey 7 :=
  ⟨![275520, 107520, 114240, 376320, 120960, 60480, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 114688, 375760, 121380, 60080, 134785], false⟩

theorem canonicalMatch7_581 :
    canonicalPose7_581.boxKey 188160 (referenceBox7 (!canonicalBox7_581.bump)) = canonicalBox7_581 := by decide +kernel

theorem canonicalDecode7_581 : canonicalBox7_581.toKeyData 188160 = keys7Chunk18.get ⟨5, by decide⟩ := by
  change canonicalBox7_581.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (17 / 28), 2, (9 / 14), (9 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (64 / 105), (671 / 336), (289 / 448), (751 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_581 : keySolid (keys7Chunk18.get ⟨5, by decide⟩) = canonicalPose7_581.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_581 (box := canonicalBox7_581) (k := keys7Chunk18.get ⟨5, by decide⟩) (canonicalMatch7_581) (canonicalDecode7_581)

def canonicalPose7_582 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, false, false, false], ![2, 1, 1, 2, 0, 0, 0]⟩
def canonicalBox7_582 : BoxKey 7 :=
  ⟨![275520, 53760, 60480, 255360, 0, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 53375, 60080, 254940, 560, 114688, 108010], false⟩

theorem canonicalMatch7_582 :
    canonicalPose7_582.boxKey 188160 (referenceBox7 (!canonicalBox7_582.bump)) = canonicalBox7_582 := by decide +kernel

theorem canonicalDecode7_582 : canonicalBox7_582.toKeyData 188160 = keys7Chunk18.get ⟨6, by decide⟩ := by
  change canonicalBox7_582.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (9 / 28), (19 / 14), 0, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_582 : keySolid (keys7Chunk18.get ⟨6, by decide⟩) = canonicalPose7_582.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_582 (box := canonicalBox7_582) (k := keys7Chunk18.get ⟨6, by decide⟩) (canonicalMatch7_582) (canonicalDecode7_582)

def canonicalPose7_583 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, true, true, false, true], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_583 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 248640, 67200, 0, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 248240, 66780, 560, 73472], false⟩

theorem canonicalMatch7_583 :
    canonicalPose7_583.boxKey 188160 (referenceBox7 (!canonicalBox7_583.bump)) = canonicalBox7_583 := by decide +kernel

theorem canonicalDecode7_583 : canonicalBox7_583.toKeyData 188160 = keys7Chunk18.get ⟨7, by decide⟩ := by
  change canonicalBox7_583.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (37 / 28), (5 / 14), 0, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448), (1 / 336), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_583 : keySolid (keys7Chunk18.get ⟨7, by decide⟩) = canonicalPose7_583.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_583 (box := canonicalBox7_583) (k := keys7Chunk18.get ⟨7, by decide⟩) (canonicalMatch7_583) (canonicalDecode7_583)

def canonicalPose7_584 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, true, true, true, true], ![2, 0, 0, 2, 1, 0, 1]⟩
def canonicalBox7_584 : BoxKey 7 :=
  ⟨![248640, 134400, 100800, 268800, 73920, 0, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 134785, 101360, 268310, 73472, -560, 66780], true⟩

theorem canonicalMatch7_584 :
    canonicalPose7_584.boxKey 188160 (referenceBox7 (!canonicalBox7_584.bump)) = canonicalBox7_584 := by decide +kernel

theorem canonicalDecode7_584 : canonicalBox7_584.toKeyData 188160 = keys7Chunk18.get ⟨8, by decide⟩ := by
  change canonicalBox7_584.toKeyData 188160 = ⟨![(37 / 28), (5 / 7), (15 / 28), (10 / 7), (11 / 28), 0, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105), (-1 / 336), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_584 : keySolid (keys7Chunk18.get ⟨8, by decide⟩) = canonicalPose7_584.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_584 (box := canonicalBox7_584) (k := keys7Chunk18.get ⟨8, by decide⟩) (canonicalMatch7_584) (canonicalDecode7_584)

def canonicalPose7_585 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, false, false, true], ![2, 1, 1, 2, 0, 0, 0]⟩
def canonicalBox7_585 : BoxKey 7 :=
  ⟨![255360, 60480, 53760, 275520, 107520, 114240, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 53375, 274960, 108010, 114688, -560], true⟩

theorem canonicalMatch7_585 :
    canonicalPose7_585.boxKey 188160 (referenceBox7 (!canonicalBox7_585.bump)) = canonicalBox7_585 := by decide +kernel

theorem canonicalDecode7_585 : canonicalBox7_585.toKeyData 188160 = keys7Chunk18.get ⟨9, by decide⟩ := by
  change canonicalBox7_585.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (2 / 7), (41 / 28), (4 / 7), (17 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_585 : keySolid (keys7Chunk18.get ⟨9, by decide⟩) = canonicalPose7_585.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_585 (box := canonicalBox7_585) (k := keys7Chunk18.get ⟨9, by decide⟩) (canonicalMatch7_585) (canonicalDecode7_585)

def canonicalPose7_586 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, false, true, true, true, false, true], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_586 : BoxKey 7 :=
  ⟨![376320, 114240, 67200, 248640, 53760, 100800, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![375760, 114688, 66780, 248240, 53375, 101360, 268310], false⟩

theorem canonicalMatch7_586 :
    canonicalPose7_586.boxKey 188160 (referenceBox7 (!canonicalBox7_586.bump)) = canonicalBox7_586 := by decide +kernel

theorem canonicalDecode7_586 : canonicalBox7_586.toKeyData 188160 = keys7Chunk18.get ⟨10, by decide⟩ := by
  change canonicalBox7_586.toKeyData 188160 = ⟨![2, (17 / 28), (5 / 14), (37 / 28), (2 / 7), (15 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(671 / 336), (64 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_586 : keySolid (keys7Chunk18.get ⟨10, by decide⟩) = canonicalPose7_586.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_586 (box := canonicalBox7_586) (k := keys7Chunk18.get ⟨10, by decide⟩) (canonicalMatch7_586) (canonicalDecode7_586)

def canonicalPose7_587 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, false, false, false, false, true], ![2, 0, 0, 1, 0, 0, 2]⟩
def canonicalBox7_587 : BoxKey 7 :=
  ⟨![262080, 0, 120960, 315840, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, -560, 121380, 316240, 134785, 101360, 268310], true⟩

theorem canonicalMatch7_587 :
    canonicalPose7_587.boxKey 188160 (referenceBox7 (!canonicalBox7_587.bump)) = canonicalBox7_587 := by decide +kernel

theorem canonicalDecode7_587 : canonicalBox7_587.toKeyData 188160 = keys7Chunk18.get ⟨11, by decide⟩ := by
  change canonicalBox7_587.toKeyData 188160 = ⟨![(39 / 28), 0, (9 / 14), (47 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_587 : keySolid (keys7Chunk18.get ⟨11, by decide⟩) = canonicalPose7_587.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_587 (box := canonicalBox7_587) (k := keys7Chunk18.get ⟨11, by decide⟩) (canonicalMatch7_587) (canonicalDecode7_587)

def canonicalPose7_588 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, true, true, false, false, false], ![1, 0, 0, 2, 0, 0, 1]⟩
def canonicalBox7_588 : BoxKey 7 :=
  ⟨![315840, 120960, 0, 262080, 107520, 100800, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, -560, 261632, 108010, 101360, 322945], true⟩

theorem canonicalMatch7_588 :
    canonicalPose7_588.boxKey 188160 (referenceBox7 (!canonicalBox7_588.bump)) = canonicalBox7_588 := by decide +kernel

theorem canonicalDecode7_588 : canonicalBox7_588.toKeyData 188160 = keys7Chunk18.get ⟨12, by decide⟩ := by
  change canonicalBox7_588.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_588 : keySolid (keys7Chunk18.get ⟨12, by decide⟩) = canonicalPose7_588.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_588 (box := canonicalBox7_588) (k := keys7Chunk18.get ⟨12, by decide⟩) (canonicalMatch7_588) (canonicalDecode7_588)

def canonicalPose7_589 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, true, true, false, true], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_589 : BoxKey 7 :=
  ⟨![275520, 107520, 73920, 376320, 67200, 127680, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 73472, 375760, 66780, 128080, 241535], false⟩

theorem canonicalMatch7_589 :
    canonicalPose7_589.boxKey 188160 (referenceBox7 (!canonicalBox7_589.bump)) = canonicalBox7_589 := by decide +kernel

theorem canonicalDecode7_589 : canonicalBox7_589.toKeyData 188160 = keys7Chunk18.get ⟨13, by decide⟩ := by
  change canonicalBox7_589.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (11 / 28), 2, (5 / 14), (19 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (41 / 105), (671 / 336), (159 / 448), (1601 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_589 : keySolid (keys7Chunk18.get ⟨13, by decide⟩) = canonicalPose7_589.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_589 (box := canonicalBox7_589) (k := keys7Chunk18.get ⟨13, by decide⟩) (canonicalMatch7_589) (canonicalDecode7_589)

def canonicalPose7_590 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, true, false, true, false, true], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_590 : BoxKey 7 :=
  ⟨![241920, 127680, 67200, 376320, 73920, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 128080, 66780, 376880, 73472, 108010, 274960], true⟩

theorem canonicalMatch7_590 :
    canonicalPose7_590.boxKey 188160 (referenceBox7 (!canonicalBox7_590.bump)) = canonicalBox7_590 := by decide +kernel

theorem canonicalDecode7_590 : canonicalBox7_590.toKeyData 188160 = keys7Chunk18.get ⟨14, by decide⟩ := by
  change canonicalBox7_590.toKeyData 188160 = ⟨![(9 / 7), (19 / 28), (5 / 14), 2, (11 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (1601 / 2352), (159 / 448), (673 / 336), (41 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_590 : keySolid (keys7Chunk18.get ⟨14, by decide⟩) = canonicalPose7_590.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_590 (box := canonicalBox7_590) (k := keys7Chunk18.get ⟨14, by decide⟩) (canonicalMatch7_590) (canonicalDecode7_590)

def canonicalPose7_591 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, false, true, false, false, false], ![1, 0, 0, 2, 0, 0, 1]⟩
def canonicalBox7_591 : BoxKey 7 :=
  ⟨![322560, 100800, 107520, 262080, 0, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 101360, 108010, 261632, 560, 121380, 316240], false⟩

theorem canonicalMatch7_591 :
    canonicalPose7_591.boxKey 188160 (referenceBox7 (!canonicalBox7_591.bump)) = canonicalBox7_591 := by decide +kernel

theorem canonicalDecode7_591 : canonicalBox7_591.toKeyData 188160 = keys7Chunk18.get ⟨15, by decide⟩ := by
  change canonicalBox7_591.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_591 : keySolid (keys7Chunk18.get ⟨15, by decide⟩) = canonicalPose7_591.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_591 (box := canonicalBox7_591) (k := keys7Chunk18.get ⟨15, by decide⟩) (canonicalMatch7_591) (canonicalDecode7_591)

def canonicalPose7_592 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, false, false, false, true], ![2, 0, 0, 1, 0, 0, 2]⟩
def canonicalBox7_592 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 315840, 120960, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 316240, 121380, 560, 261632], false⟩

theorem canonicalMatch7_592 :
    canonicalPose7_592.boxKey 188160 (referenceBox7 (!canonicalBox7_592.bump)) = canonicalBox7_592 := by decide +kernel

theorem canonicalDecode7_592 : canonicalBox7_592.toKeyData 188160 = keys7Chunk18.get ⟨16, by decide⟩ := by
  change canonicalBox7_592.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (47 / 28), (9 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_592 : keySolid (keys7Chunk18.get ⟨16, by decide⟩) = canonicalPose7_592.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_592 (box := canonicalBox7_592) (k := keys7Chunk18.get ⟨16, by decide⟩) (canonicalMatch7_592) (canonicalDecode7_592)

def canonicalPose7_593 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, false, true, true, true, false, false], ![2, 0, 1, 2, 1, 0, 2]⟩
def canonicalBox7_593 : BoxKey 7 :=
  ⟨![268800, 100800, 53760, 248640, 67200, 114240, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 101360, 53375, 248240, 66780, 114688, 376880], true⟩

theorem canonicalMatch7_593 :
    canonicalPose7_593.boxKey 188160 (referenceBox7 (!canonicalBox7_593.bump)) = canonicalBox7_593 := by decide +kernel

theorem canonicalDecode7_593 : canonicalBox7_593.toKeyData 188160 = keys7Chunk18.get ⟨17, by decide⟩ := by
  change canonicalBox7_593.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (2 / 7), (37 / 28), (5 / 14), (17 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_593 : keySolid (keys7Chunk18.get ⟨17, by decide⟩) = canonicalPose7_593.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_593 (box := canonicalBox7_593) (k := keys7Chunk18.get ⟨17, by decide⟩) (canonicalMatch7_593) (canonicalDecode7_593)

def canonicalPose7_594 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, false, true, false, false, false], ![2, 0, 0, 2, 0, 1, 0]⟩
def canonicalBox7_594 : BoxKey 7 :=
  ⟨![376320, 114240, 107520, 275520, 134400, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 114688, 108010, 274960, 134785, 316240, 121380], false⟩

theorem canonicalMatch7_594 :
    canonicalPose7_594.boxKey 188160 (referenceBox7 (!canonicalBox7_594.bump)) = canonicalBox7_594 := by decide +kernel

theorem canonicalDecode7_594 : canonicalBox7_594.toKeyData 188160 = keys7Chunk18.get ⟨18, by decide⟩ := by
  change canonicalBox7_594.toKeyData 188160 = ⟨![2, (17 / 28), (4 / 7), (41 / 28), (5 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_594 : keySolid (keys7Chunk18.get ⟨18, by decide⟩) = canonicalPose7_594.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_594 (box := canonicalBox7_594) (k := keys7Chunk18.get ⟨18, by decide⟩) (canonicalMatch7_594) (canonicalDecode7_594)

def canonicalPose7_595 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, true, false, true, true, true, true], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_595 : BoxKey 7 :=
  ⟨![262080, 0, 107520, 275520, 53760, 248640, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, -560, 108010, 274960, 53375, 248240, 66780], true⟩

theorem canonicalMatch7_595 :
    canonicalPose7_595.boxKey 188160 (referenceBox7 (!canonicalBox7_595.bump)) = canonicalBox7_595 := by decide +kernel

theorem canonicalDecode7_595 : canonicalBox7_595.toKeyData 188160 = keys7Chunk18.get ⟨19, by decide⟩ := by
  change canonicalBox7_595.toKeyData 188160 = ⟨![(39 / 28), 0, (4 / 7), (41 / 28), (2 / 7), (37 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (-1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_595 : keySolid (keys7Chunk18.get ⟨19, by decide⟩) = canonicalPose7_595.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_595 (box := canonicalBox7_595) (k := keys7Chunk18.get ⟨19, by decide⟩) (canonicalMatch7_595) (canonicalDecode7_595)

def canonicalPose7_596 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, false, false, true, true, true, true], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_596 : BoxKey 7 :=
  ⟨![275520, 107520, 0, 262080, 67200, 248640, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 108010, 560, 261632, 66780, 248240, 53375], false⟩

theorem canonicalMatch7_596 :
    canonicalPose7_596.boxKey 188160 (referenceBox7 (!canonicalBox7_596.bump)) = canonicalBox7_596 := by decide +kernel

theorem canonicalDecode7_596 : canonicalBox7_596.toKeyData 188160 = keys7Chunk18.get ⟨20, by decide⟩ := by
  change canonicalBox7_596.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), 0, (39 / 28), (5 / 14), (37 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (1 / 336), (146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_596 : keySolid (keys7Chunk18.get ⟨20, by decide⟩) = canonicalPose7_596.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_596 (box := canonicalBox7_596) (k := keys7Chunk18.get ⟨20, by decide⟩) (canonicalMatch7_596) (canonicalDecode7_596)

def canonicalPose7_597 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, false, false, false, false], ![2, 0, 0, 2, 0, 1, 0]⟩
def canonicalBox7_597 : BoxKey 7 :=
  ⟨![275520, 107520, 114240, 376320, 120960, 315840, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 114688, 376880, 121380, 316240, 134785], true⟩

theorem canonicalMatch7_597 :
    canonicalPose7_597.boxKey 188160 (referenceBox7 (!canonicalBox7_597.bump)) = canonicalBox7_597 := by decide +kernel

theorem canonicalDecode7_597 : canonicalBox7_597.toKeyData 188160 = keys7Chunk18.get ⟨21, by decide⟩ := by
  change canonicalBox7_597.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (17 / 28), 2, (9 / 14), (47 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (64 / 105), (673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_597 : keySolid (keys7Chunk18.get ⟨21, by decide⟩) = canonicalPose7_597.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_597 (box := canonicalBox7_597) (k := keys7Chunk18.get ⟨21, by decide⟩) (canonicalMatch7_597) (canonicalDecode7_597)

def canonicalPose7_598 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, true, true, false], ![2, 1, 1, 2, 0, 2, 0]⟩
def canonicalBox7_598 : BoxKey 7 :=
  ⟨![275520, 53760, 60480, 255360, 0, 262080, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 53375, 60080, 254940, -560, 261632, 108010], true⟩

theorem canonicalMatch7_598 :
    canonicalPose7_598.boxKey 188160 (referenceBox7 (!canonicalBox7_598.bump)) = canonicalBox7_598 := by decide +kernel

theorem canonicalDecode7_598 : canonicalBox7_598.toKeyData 188160 = keys7Chunk18.get ⟨22, by decide⟩ := by
  change canonicalBox7_598.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (9 / 28), (19 / 14), 0, (39 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (146 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_598 : keySolid (keys7Chunk18.get ⟨22, by decide⟩) = canonicalPose7_598.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_598 (box := canonicalBox7_598) (k := keys7Chunk18.get ⟨22, by decide⟩) (canonicalMatch7_598) (canonicalDecode7_598)

def canonicalPose7_599 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, true, true, false, true], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_599 : BoxKey 7 :=
  ⟨![268800, 100800, 134400, 248640, 67200, 376320, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 134785, 248240, 66780, 376880, 73472], true⟩

theorem canonicalMatch7_599 :
    canonicalPose7_599.boxKey 188160 (referenceBox7 (!canonicalBox7_599.bump)) = canonicalBox7_599 := by decide +kernel

theorem canonicalDecode7_599 : canonicalBox7_599.toKeyData 188160 = keys7Chunk18.get ⟨23, by decide⟩ := by
  change canonicalBox7_599.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (5 / 7), (37 / 28), (5 / 14), 2, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448), (673 / 336), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_599 : keySolid (keys7Chunk18.get ⟨23, by decide⟩) = canonicalPose7_599.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_599 (box := canonicalBox7_599) (k := keys7Chunk18.get ⟨23, by decide⟩) (canonicalMatch7_599) (canonicalDecode7_599)

def canonicalPose7_600 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, true, true, true, true], ![2, 0, 0, 2, 1, 2, 1]⟩
def canonicalBox7_600 : BoxKey 7 :=
  ⟨![248640, 134400, 100800, 268800, 73920, 376320, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 134785, 101360, 268310, 73472, 375760, 66780], false⟩

theorem canonicalMatch7_600 :
    canonicalPose7_600.boxKey 188160 (referenceBox7 (!canonicalBox7_600.bump)) = canonicalBox7_600 := by decide +kernel

theorem canonicalDecode7_600 : canonicalBox7_600.toKeyData 188160 = keys7Chunk18.get ⟨24, by decide⟩ := by
  change canonicalBox7_600.toKeyData 188160 = ⟨![(37 / 28), (5 / 7), (15 / 28), (10 / 7), (11 / 28), 2, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105), (671 / 336), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_600 : keySolid (keys7Chunk18.get ⟨24, by decide⟩) = canonicalPose7_600.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_600 (box := canonicalBox7_600) (k := keys7Chunk18.get ⟨24, by decide⟩) (canonicalMatch7_600) (canonicalDecode7_600)

def canonicalPose7_601 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, false, true, false], ![2, 1, 1, 2, 0, 2, 0]⟩
def canonicalBox7_601 : BoxKey 7 :=
  ⟨![255360, 60480, 53760, 275520, 107520, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 53375, 274960, 108010, 261632, 560], false⟩

theorem canonicalMatch7_601 :
    canonicalPose7_601.boxKey 188160 (referenceBox7 (!canonicalBox7_601.bump)) = canonicalBox7_601 := by decide +kernel

theorem canonicalDecode7_601 : canonicalBox7_601.toKeyData 188160 = keys7Chunk18.get ⟨25, by decide⟩ := by
  change canonicalBox7_601.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (2 / 7), (41 / 28), (4 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_601 : keySolid (keys7Chunk18.get ⟨25, by decide⟩) = canonicalPose7_601.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_601 (box := canonicalBox7_601) (k := keys7Chunk18.get ⟨25, by decide⟩) (canonicalMatch7_601) (canonicalDecode7_601)

def canonicalPose7_602 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, true, false, true, false], ![2, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_602 : BoxKey 7 :=
  ⟨![376320, 73920, 107520, 275520, 134400, 248640, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 73472, 108010, 274960, 134785, 248240, 309540], false⟩

theorem canonicalMatch7_602 :
    canonicalPose7_602.boxKey 188160 (referenceBox7 (!canonicalBox7_602.bump)) = canonicalBox7_602 := by decide +kernel

theorem canonicalDecode7_602 : canonicalBox7_602.toKeyData 188160 = keys7Chunk18.get ⟨26, by decide⟩ := by
  change canonicalBox7_602.toKeyData 188160 = ⟨![2, (11 / 28), (4 / 7), (41 / 28), (5 / 7), (37 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_602 : keySolid (keys7Chunk18.get ⟨26, by decide⟩) = canonicalPose7_602.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_602 (box := canonicalBox7_602) (k := keys7Chunk18.get ⟨26, by decide⟩) (canonicalMatch7_602) (canonicalDecode7_602)

def canonicalPose7_603 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, false, true, false, true, false], ![2, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_603 : BoxKey 7 :=
  ⟨![376320, 67200, 127680, 241920, 100800, 268800, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 66780, 128080, 241535, 101360, 268310, 302848], true⟩

theorem canonicalMatch7_603 :
    canonicalPose7_603.boxKey 188160 (referenceBox7 (!canonicalBox7_603.bump)) = canonicalBox7_603 := by decide +kernel

theorem canonicalDecode7_603 : canonicalBox7_603.toKeyData 188160 = keys7Chunk18.get ⟨27, by decide⟩ := by
  change canonicalBox7_603.toKeyData 188160 = ⟨![2, (5 / 14), (19 / 28), (9 / 7), (15 / 28), (10 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_603 : keySolid (keys7Chunk18.get ⟨27, by decide⟩) = canonicalPose7_603.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_603 (box := canonicalBox7_603) (k := keys7Chunk18.get ⟨27, by decide⟩) (canonicalMatch7_603) (canonicalDecode7_603)

def canonicalPose7_604 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, false, false, true, true, true], ![2, 0, 0, 1, 1, 2, 2]⟩
def canonicalBox7_604 : BoxKey 7 :=
  ⟨![262080, 0, 120960, 315840, 53760, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, -560, 121380, 316240, 53375, 274960, 268310], true⟩

theorem canonicalMatch7_604 :
    canonicalPose7_604.boxKey 188160 (referenceBox7 (!canonicalBox7_604.bump)) = canonicalBox7_604 := by decide +kernel

theorem canonicalDecode7_604 : canonicalBox7_604.toKeyData 188160 = keys7Chunk18.get ⟨28, by decide⟩ := by
  change canonicalBox7_604.toKeyData 188160 = ⟨![(39 / 28), 0, (9 / 14), (47 / 28), (2 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_604 : keySolid (keys7Chunk18.get ⟨28, by decide⟩) = canonicalPose7_604.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_604 (box := canonicalBox7_604) (k := keys7Chunk18.get ⟨28, by decide⟩) (canonicalMatch7_604) (canonicalDecode7_604)

def canonicalPose7_605 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, true, true, false, true, true], ![1, 0, 0, 2, 0, 2, 2]⟩
def canonicalBox7_605 : BoxKey 7 :=
  ⟨![315840, 120960, 0, 262080, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, -560, 261632, 108010, 274960, 241535], true⟩

theorem canonicalMatch7_605 :
    canonicalPose7_605.boxKey 188160 (referenceBox7 (!canonicalBox7_605.bump)) = canonicalBox7_605 := by decide +kernel

theorem canonicalDecode7_605 : canonicalBox7_605.toKeyData 188160 = keys7Chunk18.get ⟨29, by decide⟩ := by
  change canonicalBox7_605.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_605 : keySolid (keys7Chunk18.get ⟨29, by decide⟩) = canonicalPose7_605.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_605 (box := canonicalBox7_605) (k := keys7Chunk18.get ⟨29, by decide⟩) (canonicalMatch7_605) (canonicalDecode7_605)

def canonicalPose7_606 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, true, false, true, false, true, false], ![2, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_606 : BoxKey 7 :=
  ⟨![248640, 67200, 114240, 376320, 107520, 275520, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 66780, 114688, 375760, 108010, 274960, 322945], false⟩

theorem canonicalMatch7_606 :
    canonicalPose7_606.boxKey 188160 (referenceBox7 (!canonicalBox7_606.bump)) = canonicalBox7_606 := by decide +kernel

theorem canonicalDecode7_606 : canonicalBox7_606.toKeyData 188160 = keys7Chunk18.get ⟨30, by decide⟩ := by
  change canonicalBox7_606.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), (17 / 28), 2, (4 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (64 / 105), (671 / 336), (1543 / 2688), (491 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_606 : keySolid (keys7Chunk18.get ⟨30, by decide⟩) = canonicalPose7_606.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_606 (box := canonicalBox7_606) (k := keys7Chunk18.get ⟨30, by decide⟩) (canonicalMatch7_606) (canonicalDecode7_606)

def canonicalPose7_607 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, true, false, true, true, true, false], ![2, 1, 0, 2, 0, 2, 1]⟩
def canonicalBox7_607 : BoxKey 7 :=
  ⟨![248640, 53760, 100800, 268800, 0, 262080, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 53375, 101360, 268310, -560, 261632, 309540], true⟩

theorem canonicalMatch7_607 :
    canonicalPose7_607.boxKey 188160 (referenceBox7 (!canonicalBox7_607.bump)) = canonicalBox7_607 := by decide +kernel

theorem canonicalDecode7_607 : canonicalBox7_607.toKeyData 188160 = keys7Chunk18.get ⟨31, by decide⟩ := by
  change canonicalBox7_607.toKeyData 188160 = ⟨![(37 / 28), (2 / 7), (15 / 28), (10 / 7), 0, (39 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (-1 / 336), (146 / 105), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_607 : keySolid (keys7Chunk18.get ⟨31, by decide⟩) = canonicalPose7_607.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_607 (box := canonicalBox7_607) (k := keys7Chunk18.get ⟨31, by decide⟩) (canonicalMatch7_607) (canonicalDecode7_607)

theorem keys7Chunk18_canonical : ∀ k ∈ keys7Chunk18,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk18, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_576, canonicalSolid7_576⟩
  · exact ⟨canonicalPose7_577, canonicalSolid7_577⟩
  · exact ⟨canonicalPose7_578, canonicalSolid7_578⟩
  · exact ⟨canonicalPose7_579, canonicalSolid7_579⟩
  · exact ⟨canonicalPose7_580, canonicalSolid7_580⟩
  · exact ⟨canonicalPose7_581, canonicalSolid7_581⟩
  · exact ⟨canonicalPose7_582, canonicalSolid7_582⟩
  · exact ⟨canonicalPose7_583, canonicalSolid7_583⟩
  · exact ⟨canonicalPose7_584, canonicalSolid7_584⟩
  · exact ⟨canonicalPose7_585, canonicalSolid7_585⟩
  · exact ⟨canonicalPose7_586, canonicalSolid7_586⟩
  · exact ⟨canonicalPose7_587, canonicalSolid7_587⟩
  · exact ⟨canonicalPose7_588, canonicalSolid7_588⟩
  · exact ⟨canonicalPose7_589, canonicalSolid7_589⟩
  · exact ⟨canonicalPose7_590, canonicalSolid7_590⟩
  · exact ⟨canonicalPose7_591, canonicalSolid7_591⟩
  · exact ⟨canonicalPose7_592, canonicalSolid7_592⟩
  · exact ⟨canonicalPose7_593, canonicalSolid7_593⟩
  · exact ⟨canonicalPose7_594, canonicalSolid7_594⟩
  · exact ⟨canonicalPose7_595, canonicalSolid7_595⟩
  · exact ⟨canonicalPose7_596, canonicalSolid7_596⟩
  · exact ⟨canonicalPose7_597, canonicalSolid7_597⟩
  · exact ⟨canonicalPose7_598, canonicalSolid7_598⟩
  · exact ⟨canonicalPose7_599, canonicalSolid7_599⟩
  · exact ⟨canonicalPose7_600, canonicalSolid7_600⟩
  · exact ⟨canonicalPose7_601, canonicalSolid7_601⟩
  · exact ⟨canonicalPose7_602, canonicalSolid7_602⟩
  · exact ⟨canonicalPose7_603, canonicalSolid7_603⟩
  · exact ⟨canonicalPose7_604, canonicalSolid7_604⟩
  · exact ⟨canonicalPose7_605, canonicalSolid7_605⟩
  · exact ⟨canonicalPose7_606, canonicalSolid7_606⟩
  · exact ⟨canonicalPose7_607, canonicalSolid7_607⟩

#print axioms keys7Chunk18_canonical

end SparseMonotiles.Canonical
