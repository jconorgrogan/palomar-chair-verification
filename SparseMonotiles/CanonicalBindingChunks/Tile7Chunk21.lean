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

def canonicalPose7_672 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, true, false, true, false, false], ![2, 0, 2, 0, 1, 2, 1]⟩
def canonicalBox7_672 : BoxKey 7 :=
  ⟨![248640, 134400, 275520, 107520, 73920, 376320, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 134785, 274960, 108010, 73472, 376880, 309540], true⟩

theorem canonicalMatch7_672 :
    canonicalPose7_672.boxKey 188160 (referenceBox7 (!canonicalBox7_672.bump)) = canonicalBox7_672 := by decide +kernel

theorem canonicalDecode7_672 : canonicalBox7_672.toKeyData 188160 = keys7Chunk21.get ⟨0, by decide⟩ := by
  change canonicalBox7_672.toKeyData 188160 = ⟨![(37 / 28), (5 / 7), (41 / 28), (4 / 7), (11 / 28), 2, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (673 / 336), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_672 : keySolid (keys7Chunk21.get ⟨0, by decide⟩) = canonicalPose7_672.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_672 (box := canonicalBox7_672) (k := keys7Chunk21.get ⟨0, by decide⟩) (canonicalMatch7_672) (canonicalDecode7_672)

def canonicalPose7_673 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, false, false, false, true, false], ![2, 1, 1, 0, 0, 2, 2]⟩
def canonicalBox7_673 : BoxKey 7 :=
  ⟨![255360, 60480, 322560, 100800, 107520, 262080, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 322945, 101360, 108010, 261632, 376880], true⟩

theorem canonicalMatch7_673 :
    canonicalPose7_673.boxKey 188160 (referenceBox7 (!canonicalBox7_673.bump)) = canonicalBox7_673 := by decide +kernel

theorem canonicalDecode7_673 : canonicalBox7_673.toKeyData 188160 = keys7Chunk21.get ⟨1, by decide⟩ := by
  change canonicalBox7_673.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (12 / 7), (15 / 28), (4 / 7), (39 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_673 : keySolid (keys7Chunk21.get ⟨1, by decide⟩) = canonicalPose7_673.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_673 (box := canonicalBox7_673) (k := keys7Chunk21.get ⟨1, by decide⟩) (canonicalMatch7_673) (canonicalDecode7_673)

def canonicalPose7_674 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, false, false, true, false, false], ![2, 0, 1, 0, 2, 0, 0]⟩
def canonicalBox7_674 : BoxKey 7 :=
  ⟨![376320, 120960, 315840, 134400, 275520, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 121380, 316240, 134785, 274960, 108010, 114688], true⟩

theorem canonicalMatch7_674 :
    canonicalPose7_674.boxKey 188160 (referenceBox7 (!canonicalBox7_674.bump)) = canonicalBox7_674 := by decide +kernel

theorem canonicalDecode7_674 : canonicalBox7_674.toKeyData 188160 = keys7Chunk21.get ⟨2, by decide⟩ := by
  change canonicalBox7_674.toKeyData 188160 = ⟨![2, (9 / 14), (47 / 28), (5 / 7), (41 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_674 : keySolid (keys7Chunk21.get ⟨2, by decide⟩) = canonicalPose7_674.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_674 (box := canonicalBox7_674) (k := keys7Chunk21.get ⟨2, by decide⟩) (canonicalMatch7_674) (canonicalDecode7_674)

def canonicalPose7_675 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, true, false, true, true, true], ![2, 0, 2, 0, 2, 1, 1]⟩
def canonicalBox7_675 : BoxKey 7 :=
  ⟨![255360, 0, 262080, 107520, 275520, 53760, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, -560, 261632, 108010, 274960, 53375, 60080], true⟩

theorem canonicalMatch7_675 :
    canonicalPose7_675.boxKey 188160 (referenceBox7 (!canonicalBox7_675.bump)) = canonicalBox7_675 := by decide +kernel

theorem canonicalDecode7_675 : canonicalBox7_675.toKeyData 188160 = keys7Chunk21.get ⟨3, by decide⟩ := by
  change canonicalBox7_675.toKeyData 188160 = ⟨![(19 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (2 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_675 : keySolid (keys7Chunk21.get ⟨3, by decide⟩) = canonicalPose7_675.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_675 (box := canonicalBox7_675) (k := keys7Chunk21.get ⟨3, by decide⟩) (canonicalMatch7_675) (canonicalDecode7_675)

def canonicalPose7_676 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, true, true, false, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_676 : BoxKey 7 :=
  ⟨![268800, 73920, 376320, 67200, 248640, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 73472, 375760, 66780, 248240, 134785, 101360], false⟩

theorem canonicalMatch7_676 :
    canonicalPose7_676.boxKey 188160 (referenceBox7 (!canonicalBox7_676.bump)) = canonicalBox7_676 := by decide +kernel

theorem canonicalDecode7_676 : canonicalBox7_676.toKeyData 188160 = keys7Chunk21.get ⟨4, by decide⟩ := by
  change canonicalBox7_676.toKeyData 188160 = ⟨![(10 / 7), (11 / 28), 2, (5 / 14), (37 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (41 / 105), (671 / 336), (159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_676 : keySolid (keys7Chunk21.get ⟨4, by decide⟩) = canonicalPose7_676.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_676 (box := canonicalBox7_676) (k := keys7Chunk21.get ⟨4, by decide⟩) (canonicalMatch7_676) (canonicalDecode7_676)

def canonicalPose7_677 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, true, true, false, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_677 : BoxKey 7 :=
  ⟨![248640, 67200, 376320, 73920, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 66780, 376880, 73472, 268310, 101360, 134785], true⟩

theorem canonicalMatch7_677 :
    canonicalPose7_677.boxKey 188160 (referenceBox7 (!canonicalBox7_677.bump)) = canonicalBox7_677 := by decide +kernel

theorem canonicalDecode7_677 : canonicalBox7_677.toKeyData 188160 = keys7Chunk21.get ⟨5, by decide⟩ := by
  change canonicalBox7_677.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), 2, (11 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (673 / 336), (41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_677 : keySolid (keys7Chunk21.get ⟨5, by decide⟩) = canonicalPose7_677.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_677 (box := canonicalBox7_677) (k := keys7Chunk21.get ⟨5, by decide⟩) (canonicalMatch7_677) (canonicalDecode7_677)

def canonicalPose7_678 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, false, true, true, true], ![2, 0, 2, 0, 2, 1, 1]⟩
def canonicalBox7_678 : BoxKey 7 :=
  ⟨![275520, 107520, 262080, 0, 255360, 60480, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 261632, 560, 254940, 60080, 53375], false⟩

theorem canonicalMatch7_678 :
    canonicalPose7_678.boxKey 188160 (referenceBox7 (!canonicalBox7_678.bump)) = canonicalBox7_678 := by decide +kernel

theorem canonicalDecode7_678 : canonicalBox7_678.toKeyData 188160 = keys7Chunk21.get ⟨6, by decide⟩ := by
  change canonicalBox7_678.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (39 / 28), 0, (19 / 14), (9 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (607 / 448), (751 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_678 : keySolid (keys7Chunk21.get ⟨6, by decide⟩) = canonicalPose7_678.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_678 (box := canonicalBox7_678) (k := keys7Chunk21.get ⟨6, by decide⟩) (canonicalMatch7_678) (canonicalDecode7_678)

def canonicalPose7_679 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, false, false, true, false, false], ![2, 0, 1, 0, 2, 0, 0]⟩
def canonicalBox7_679 : BoxKey 7 :=
  ⟨![275520, 134400, 315840, 120960, 376320, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 134785, 316240, 121380, 375760, 114688, 108010], false⟩

theorem canonicalMatch7_679 :
    canonicalPose7_679.boxKey 188160 (referenceBox7 (!canonicalBox7_679.bump)) = canonicalBox7_679 := by decide +kernel

theorem canonicalDecode7_679 : canonicalBox7_679.toKeyData 188160 = keys7Chunk21.get ⟨7, by decide⟩ := by
  change canonicalBox7_679.toKeyData 188160 = ⟨![(41 / 28), (5 / 7), (47 / 28), (9 / 14), 2, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (64 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_679 : keySolid (keys7Chunk21.get ⟨7, by decide⟩) = canonicalPose7_679.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_679 (box := canonicalBox7_679) (k := keys7Chunk21.get ⟨7, by decide⟩) (canonicalMatch7_679) (canonicalDecode7_679)

def canonicalPose7_680 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, true, true, true, true, true, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_680 : BoxKey 7 :=
  ⟨![275520, 53760, 248640, 67200, 262080, 0, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 53375, 248240, 66780, 261632, -560, 108010], true⟩

theorem canonicalMatch7_680 :
    canonicalPose7_680.boxKey 188160 (referenceBox7 (!canonicalBox7_680.bump)) = canonicalBox7_680 := by decide +kernel

theorem canonicalDecode7_680 : canonicalBox7_680.toKeyData 188160 = keys7Chunk21.get ⟨8, by decide⟩ := by
  change canonicalBox7_680.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (37 / 28), (5 / 14), (39 / 28), 0, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105), (-1 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_680 : keySolid (keys7Chunk21.get ⟨8, by decide⟩) = canonicalPose7_680.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_680 (box := canonicalBox7_680) (k := keys7Chunk21.get ⟨8, by decide⟩) (canonicalMatch7_680) (canonicalDecode7_680)

def canonicalPose7_681 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, true, true, true, true, false, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_681 : BoxKey 7 :=
  ⟨![262080, 67200, 248640, 53760, 275520, 107520, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 66780, 248240, 53375, 274960, 108010, 560], false⟩

theorem canonicalMatch7_681 :
    canonicalPose7_681.boxKey 188160 (referenceBox7 (!canonicalBox7_681.bump)) = canonicalBox7_681 := by decide +kernel

theorem canonicalDecode7_681 : canonicalBox7_681.toKeyData 188160 = keys7Chunk21.get ⟨9, by decide⟩ := by
  change canonicalBox7_681.toKeyData 188160 = ⟨![(39 / 28), (5 / 14), (37 / 28), (2 / 7), (41 / 28), (4 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_681 : keySolid (keys7Chunk21.get ⟨9, by decide⟩) = canonicalPose7_681.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_681 (box := canonicalBox7_681) (k := keys7Chunk21.get ⟨9, by decide⟩) (canonicalMatch7_681) (canonicalDecode7_681)

def canonicalPose7_682 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, false, false, false, false, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_682 : BoxKey 7 :=
  ⟨![376320, 114240, 309120, 127680, 322560, 100800, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![376880, 114688, 309540, 128080, 322945, 101360, 268310], true⟩

theorem canonicalMatch7_682 :
    canonicalPose7_682.boxKey 188160 (referenceBox7 (!canonicalBox7_682.bump)) = canonicalBox7_682 := by decide +kernel

theorem canonicalDecode7_682 : canonicalBox7_682.toKeyData 188160 = keys7Chunk21.get ⟨10, by decide⟩ := by
  change canonicalBox7_682.toKeyData 188160 = ⟨![2, (17 / 28), (23 / 14), (19 / 28), (12 / 7), (15 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(673 / 336), (64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_682 : keySolid (keys7Chunk21.get ⟨10, by decide⟩) = canonicalPose7_682.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_682 (box := canonicalBox7_682) (k := keys7Chunk21.get ⟨10, by decide⟩) (canonicalMatch7_682) (canonicalDecode7_682)

def canonicalPose7_683 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, true, true, true, false, true], ![2, 0, 2, 1, 2, 0, 2]⟩
def canonicalBox7_683 : BoxKey 7 :=
  ⟨![262080, 0, 255360, 60480, 241920, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 560, 254940, 60080, 241535, 101360, 268310], false⟩

theorem canonicalMatch7_683 :
    canonicalPose7_683.boxKey 188160 (referenceBox7 (!canonicalBox7_683.bump)) = canonicalBox7_683 := by decide +kernel

theorem canonicalDecode7_683 : canonicalBox7_683.toKeyData 188160 = keys7Chunk21.get ⟨11, by decide⟩ := by
  change canonicalBox7_683.toKeyData 188160 = ⟨![(39 / 28), 0, (19 / 14), (9 / 28), (9 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (1 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_683 : keySolid (keys7Chunk21.get ⟨11, by decide⟩) = canonicalPose7_683.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_683 (box := canonicalBox7_683) (k := keys7Chunk21.get ⟨11, by decide⟩) (canonicalMatch7_683) (canonicalDecode7_683)

def canonicalPose7_684 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, false, true, false, true, false, false], ![1, 0, 2, 0, 2, 0, 1]⟩
def canonicalBox7_684 : BoxKey 7 :=
  ⟨![315840, 120960, 376320, 114240, 268800, 100800, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 121380, 375760, 114688, 268310, 101360, 322945], false⟩

theorem canonicalMatch7_684 :
    canonicalPose7_684.boxKey 188160 (referenceBox7 (!canonicalBox7_684.bump)) = canonicalBox7_684 := by decide +kernel

theorem canonicalDecode7_684 : canonicalBox7_684.toKeyData 188160 = keys7Chunk21.get ⟨12, by decide⟩ := by
  change canonicalBox7_684.toKeyData 188160 = ⟨![(47 / 28), (9 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (289 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_684 : keySolid (keys7Chunk21.get ⟨12, by decide⟩) = canonicalPose7_684.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_684 (box := canonicalBox7_684) (k := keys7Chunk21.get ⟨12, by decide⟩) (canonicalMatch7_684) (canonicalDecode7_684)

def canonicalPose7_685 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, false, true, false, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_685 : BoxKey 7 :=
  ⟨![275520, 107520, 302400, 0, 309120, 127680, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 302848, -560, 309540, 128080, 241535], true⟩

theorem canonicalMatch7_685 :
    canonicalPose7_685.boxKey 188160 (referenceBox7 (!canonicalBox7_685.bump)) = canonicalBox7_685 := by decide +kernel

theorem canonicalDecode7_685 : canonicalBox7_685.toKeyData 188160 = keys7Chunk21.get ⟨13, by decide⟩ := by
  change canonicalBox7_685.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (45 / 28), 0, (23 / 14), (19 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (169 / 105), (-1 / 336), (737 / 448), (1601 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_685 : keySolid (keys7Chunk21.get ⟨13, by decide⟩) = canonicalPose7_685.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_685 (box := canonicalBox7_685) (k := keys7Chunk21.get ⟨13, by decide⟩) (canonicalMatch7_685) (canonicalDecode7_685)

def canonicalPose7_686 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, false, false, false, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_686 : BoxKey 7 :=
  ⟨![241920, 127680, 309120, 0, 302400, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 128080, 309540, 560, 302848, 108010, 274960], false⟩

theorem canonicalMatch7_686 :
    canonicalPose7_686.boxKey 188160 (referenceBox7 (!canonicalBox7_686.bump)) = canonicalBox7_686 := by decide +kernel

theorem canonicalDecode7_686 : canonicalBox7_686.toKeyData 188160 = keys7Chunk21.get ⟨14, by decide⟩ := by
  change canonicalBox7_686.toKeyData 188160 = ⟨![(9 / 7), (19 / 28), (23 / 14), 0, (45 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (1601 / 2352), (737 / 448), (1 / 336), (169 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_686 : keySolid (keys7Chunk21.get ⟨14, by decide⟩) = canonicalPose7_686.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_686 (box := canonicalBox7_686) (k := keys7Chunk21.get ⟨14, by decide⟩) (canonicalMatch7_686) (canonicalDecode7_686)

def canonicalPose7_687 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, false, false, false, false], ![1, 0, 2, 0, 2, 0, 1]⟩
def canonicalBox7_687 : BoxKey 7 :=
  ⟨![322560, 100800, 268800, 114240, 376320, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 101360, 268310, 114688, 376880, 121380, 316240], true⟩

theorem canonicalMatch7_687 :
    canonicalPose7_687.boxKey 188160 (referenceBox7 (!canonicalBox7_687.bump)) = canonicalBox7_687 := by decide +kernel

theorem canonicalDecode7_687 : canonicalBox7_687.toKeyData 188160 = keys7Chunk21.get ⟨15, by decide⟩ := by
  change canonicalBox7_687.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (289 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_687 : keySolid (keys7Chunk21.get ⟨15, by decide⟩) = canonicalPose7_687.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_687 (box := canonicalBox7_687) (k := keys7Chunk21.get ⟨15, by decide⟩) (canonicalMatch7_687) (canonicalDecode7_687)

def canonicalPose7_688 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, true, true, true, true, true], ![2, 0, 2, 1, 2, 0, 2]⟩
def canonicalBox7_688 : BoxKey 7 :=
  ⟨![268800, 100800, 241920, 60480, 255360, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 241535, 60080, 254940, -560, 261632], true⟩

theorem canonicalMatch7_688 :
    canonicalPose7_688.boxKey 188160 (referenceBox7 (!canonicalBox7_688.bump)) = canonicalBox7_688 := by decide +kernel

theorem canonicalDecode7_688 : canonicalBox7_688.toKeyData 188160 = keys7Chunk21.get ⟨16, by decide⟩ := by
  change canonicalBox7_688.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (9 / 7), (9 / 28), (19 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_688 : keySolid (keys7Chunk21.get ⟨16, by decide⟩) = canonicalPose7_688.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_688 (box := canonicalBox7_688) (k := keys7Chunk21.get ⟨16, by decide⟩) (canonicalMatch7_688) (canonicalDecode7_688)

def canonicalPose7_689 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, false, false, false, false, false, true], ![2, 0, 1, 0, 1, 0, 2]⟩
def canonicalBox7_689 : BoxKey 7 :=
  ⟨![268800, 100800, 322560, 127680, 309120, 114240, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 101360, 322945, 128080, 309540, 114688, 375760], false⟩

theorem canonicalMatch7_689 :
    canonicalPose7_689.boxKey 188160 (referenceBox7 (!canonicalBox7_689.bump)) = canonicalBox7_689 := by decide +kernel

theorem canonicalDecode7_689 : canonicalBox7_689.toKeyData 188160 = keys7Chunk21.get ⟨17, by decide⟩ := by
  change canonicalBox7_689.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (12 / 7), (19 / 28), (23 / 14), (17 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_689 : keySolid (keys7Chunk21.get ⟨17, by decide⟩) = canonicalPose7_689.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_689 (box := canonicalBox7_689) (k := keys7Chunk21.get ⟨17, by decide⟩) (canonicalMatch7_689) (canonicalDecode7_689)

def canonicalPose7_690 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, false, false, false, false], ![2, 0, 2, 0, 1, 1, 0]⟩
def canonicalBox7_690 : BoxKey 7 :=
  ⟨![376320, 114240, 268800, 100800, 322560, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 114688, 268310, 101360, 322945, 316240, 121380], false⟩

theorem canonicalMatch7_690 :
    canonicalPose7_690.boxKey 188160 (referenceBox7 (!canonicalBox7_690.bump)) = canonicalBox7_690 := by decide +kernel

theorem canonicalDecode7_690 : canonicalBox7_690.toKeyData 188160 = keys7Chunk21.get ⟨18, by decide⟩ := by
  change canonicalBox7_690.toKeyData 188160 = ⟨![2, (17 / 28), (10 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_690 : keySolid (keys7Chunk21.get ⟨18, by decide⟩) = canonicalPose7_690.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_690 (box := canonicalBox7_690) (k := keys7Chunk21.get ⟨18, by decide⟩) (canonicalMatch7_690) (canonicalDecode7_690)

def canonicalPose7_691 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, false, true, true, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_691 : BoxKey 7 :=
  ⟨![302400, 0, 309120, 127680, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, -560, 309540, 128080, 241535, 274960, 108010], true⟩

theorem canonicalMatch7_691 :
    canonicalPose7_691.boxKey 188160 (referenceBox7 (!canonicalBox7_691.bump)) = canonicalBox7_691 := by decide +kernel

theorem canonicalDecode7_691 : canonicalBox7_691.toKeyData 188160 = keys7Chunk21.get ⟨19, by decide⟩ := by
  change canonicalBox7_691.toKeyData 188160 = ⟨![(45 / 28), 0, (23 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (-1 / 336), (737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_691 : keySolid (keys7Chunk21.get ⟨19, by decide⟩) = canonicalPose7_691.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_691 (box := canonicalBox7_691) (k := keys7Chunk21.get ⟨19, by decide⟩) (canonicalMatch7_691) (canonicalDecode7_691)

def canonicalPose7_692 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, false, true, true, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_692 : BoxKey 7 :=
  ⟨![309120, 0, 302400, 107520, 275520, 241920, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 560, 302848, 108010, 274960, 241535, 128080], false⟩

theorem canonicalMatch7_692 :
    canonicalPose7_692.boxKey 188160 (referenceBox7 (!canonicalBox7_692.bump)) = canonicalBox7_692 := by decide +kernel

theorem canonicalDecode7_692 : canonicalBox7_692.toKeyData 188160 = keys7Chunk21.get ⟨20, by decide⟩ := by
  change canonicalBox7_692.toKeyData 188160 = ⟨![(23 / 14), 0, (45 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (1 / 336), (169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_692 : keySolid (keys7Chunk21.get ⟨20, by decide⟩) = canonicalPose7_692.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_692 (box := canonicalBox7_692) (k := keys7Chunk21.get ⟨20, by decide⟩) (canonicalMatch7_692) (canonicalDecode7_692)

def canonicalPose7_693 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, false, false, false, false], ![2, 0, 2, 0, 1, 1, 0]⟩
def canonicalBox7_693 : BoxKey 7 :=
  ⟨![268800, 114240, 376320, 120960, 315840, 322560, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 114688, 376880, 121380, 316240, 322945, 101360], true⟩

theorem canonicalMatch7_693 :
    canonicalPose7_693.boxKey 188160 (referenceBox7 (!canonicalBox7_693.bump)) = canonicalBox7_693 := by decide +kernel

theorem canonicalDecode7_693 : canonicalBox7_693.toKeyData 188160 = keys7Chunk21.get ⟨21, by decide⟩ := by
  change canonicalBox7_693.toKeyData 188160 = ⟨![(10 / 7), (17 / 28), 2, (9 / 14), (47 / 28), (12 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (64 / 105), (673 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_693 : keySolid (keys7Chunk21.get ⟨21, by decide⟩) = canonicalPose7_693.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_693 (box := canonicalBox7_693) (k := keys7Chunk21.get ⟨21, by decide⟩) (canonicalMatch7_693) (canonicalDecode7_693)

def canonicalPose7_694 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, true, true, true, false], ![2, 1, 2, 0, 2, 2, 0]⟩
def canonicalBox7_694 : BoxKey 7 :=
  ⟨![241920, 60480, 255360, 0, 262080, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 60080, 254940, -560, 261632, 268310, 101360], true⟩

theorem canonicalMatch7_694 :
    canonicalPose7_694.boxKey 188160 (referenceBox7 (!canonicalBox7_694.bump)) = canonicalBox7_694 := by decide +kernel

theorem canonicalDecode7_694 : canonicalBox7_694.toKeyData 188160 = keys7Chunk21.get ⟨22, by decide⟩ := by
  change canonicalBox7_694.toKeyData 188160 = ⟨![(9 / 7), (9 / 28), (19 / 14), 0, (39 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (146 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_694 : keySolid (keys7Chunk21.get ⟨22, by decide⟩) = canonicalPose7_694.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_694 (box := canonicalBox7_694) (k := keys7Chunk21.get ⟨22, by decide⟩) (canonicalMatch7_694) (canonicalDecode7_694)

def canonicalPose7_695 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, false, false, false, true, true, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_695 : BoxKey 7 :=
  ⟨![322560, 127680, 309120, 114240, 376320, 268800, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 128080, 309540, 114688, 375760, 268310, 101360], false⟩

theorem canonicalMatch7_695 :
    canonicalPose7_695.boxKey 188160 (referenceBox7 (!canonicalBox7_695.bump)) = canonicalBox7_695 := by decide +kernel

theorem canonicalDecode7_695 : canonicalBox7_695.toKeyData 188160 = keys7Chunk21.get ⟨23, by decide⟩ := by
  change canonicalBox7_695.toKeyData 188160 = ⟨![(12 / 7), (19 / 28), (23 / 14), (17 / 28), 2, (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105), (671 / 336), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_695 : keySolid (keys7Chunk21.get ⟨23, by decide⟩) = canonicalPose7_695.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_695 (box := canonicalBox7_695) (k := keys7Chunk21.get ⟨23, by decide⟩) (canonicalMatch7_695) (canonicalDecode7_695)

def canonicalPose7_696 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, false, false, false, true, false, false], ![1, 0, 1, 0, 2, 2, 0]⟩
def canonicalBox7_696 : BoxKey 7 :=
  ⟨![309120, 127680, 322560, 100800, 268800, 376320, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 128080, 322945, 101360, 268310, 376880, 114688], true⟩

theorem canonicalMatch7_696 :
    canonicalPose7_696.boxKey 188160 (referenceBox7 (!canonicalBox7_696.bump)) = canonicalBox7_696 := by decide +kernel

theorem canonicalDecode7_696 : canonicalBox7_696.toKeyData 188160 = keys7Chunk21.get ⟨24, by decide⟩ := by
  change canonicalBox7_696.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (12 / 7), (15 / 28), (10 / 7), 2, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (673 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_696 : keySolid (keys7Chunk21.get ⟨24, by decide⟩) = canonicalPose7_696.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_696 (box := canonicalBox7_696) (k := keys7Chunk21.get ⟨24, by decide⟩) (canonicalMatch7_696) (canonicalDecode7_696)

def canonicalPose7_697 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, false, true, true, false], ![2, 1, 2, 0, 2, 2, 0]⟩
def canonicalBox7_697 : BoxKey 7 :=
  ⟨![255360, 60480, 241920, 100800, 268800, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 241535, 101360, 268310, 261632, 560], false⟩

theorem canonicalMatch7_697 :
    canonicalPose7_697.boxKey 188160 (referenceBox7 (!canonicalBox7_697.bump)) = canonicalBox7_697 := by decide +kernel

theorem canonicalDecode7_697 : canonicalBox7_697.toKeyData 188160 = keys7Chunk21.get ⟨25, by decide⟩ := by
  change canonicalBox7_697.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (9 / 7), (15 / 28), (10 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_697 : keySolid (keys7Chunk21.get ⟨25, by decide⟩) = canonicalPose7_697.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_697 (box := canonicalBox7_697) (k := keys7Chunk21.get ⟨25, by decide⟩) (canonicalMatch7_697) (canonicalDecode7_697)

def canonicalPose7_698 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, false, false, true, true, true], ![2, 0, 1, 0, 2, 2, 2]⟩
def canonicalBox7_698 : BoxKey 7 :=
  ⟨![376320, 120960, 315840, 134400, 275520, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 121380, 316240, 134785, 274960, 268310, 261632], true⟩

theorem canonicalMatch7_698 :
    canonicalPose7_698.boxKey 188160 (referenceBox7 (!canonicalBox7_698.bump)) = canonicalBox7_698 := by decide +kernel

theorem canonicalDecode7_698 : canonicalBox7_698.toKeyData 188160 = keys7Chunk21.get ⟨26, by decide⟩ := by
  change canonicalBox7_698.toKeyData 188160 = ⟨![2, (9 / 14), (47 / 28), (5 / 7), (41 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_698 : keySolid (keys7Chunk21.get ⟨26, by decide⟩) = canonicalPose7_698.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_698 (box := canonicalBox7_698) (k := keys7Chunk21.get ⟨26, by decide⟩) (canonicalMatch7_698) (canonicalDecode7_698)

def canonicalPose7_699 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, true, false, true, false, false], ![2, 0, 2, 0, 2, 1, 1]⟩
def canonicalBox7_699 : BoxKey 7 :=
  ⟨![255360, 0, 262080, 107520, 275520, 322560, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, -560, 261632, 108010, 274960, 322945, 316240], true⟩

theorem canonicalMatch7_699 :
    canonicalPose7_699.boxKey 188160 (referenceBox7 (!canonicalBox7_699.bump)) = canonicalBox7_699 := by decide +kernel

theorem canonicalDecode7_699 : canonicalBox7_699.toKeyData 188160 = keys7Chunk21.get ⟨27, by decide⟩ := by
  change canonicalBox7_699.toKeyData 188160 = ⟨![(19 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (12 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_699 : keySolid (keys7Chunk21.get ⟨27, by decide⟩) = canonicalPose7_699.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_699 (box := canonicalBox7_699) (k := keys7Chunk21.get ⟨27, by decide⟩) (canonicalMatch7_699) (canonicalDecode7_699)

def canonicalPose7_700 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, true, true, true, true], ![2, 1, 2, 1, 2, 2, 2]⟩
def canonicalBox7_700 : BoxKey 7 :=
  ⟨![268800, 73920, 376320, 67200, 248640, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 73472, 375760, 66780, 248240, 241535, 274960], false⟩

theorem canonicalMatch7_700 :
    canonicalPose7_700.boxKey 188160 (referenceBox7 (!canonicalBox7_700.bump)) = canonicalBox7_700 := by decide +kernel

theorem canonicalDecode7_700 : canonicalBox7_700.toKeyData 188160 = keys7Chunk21.get ⟨28, by decide⟩ := by
  change canonicalBox7_700.toKeyData 188160 = ⟨![(10 / 7), (11 / 28), 2, (5 / 14), (37 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (41 / 105), (671 / 336), (159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_700 : keySolid (keys7Chunk21.get ⟨28, by decide⟩) = canonicalPose7_700.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_700 (box := canonicalBox7_700) (k := keys7Chunk21.get ⟨28, by decide⟩) (canonicalMatch7_700) (canonicalDecode7_700)

def canonicalPose7_701 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, true, true, true, true], ![2, 1, 2, 1, 2, 2, 2]⟩
def canonicalBox7_701 : BoxKey 7 :=
  ⟨![248640, 67200, 376320, 73920, 268800, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 66780, 376880, 73472, 268310, 274960, 241535], true⟩

theorem canonicalMatch7_701 :
    canonicalPose7_701.boxKey 188160 (referenceBox7 (!canonicalBox7_701.bump)) = canonicalBox7_701 := by decide +kernel

theorem canonicalDecode7_701 : canonicalBox7_701.toKeyData 188160 = keys7Chunk21.get ⟨29, by decide⟩ := by
  change canonicalBox7_701.toKeyData 188160 = ⟨![(37 / 28), (5 / 14), 2, (11 / 28), (10 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (159 / 448), (673 / 336), (41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_701 : keySolid (keys7Chunk21.get ⟨29, by decide⟩) = canonicalPose7_701.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_701 (box := canonicalBox7_701) (k := keys7Chunk21.get ⟨29, by decide⟩) (canonicalMatch7_701) (canonicalDecode7_701)

def canonicalPose7_702 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, false, true, false, true, false, false], ![2, 0, 2, 0, 2, 1, 1]⟩
def canonicalBox7_702 : BoxKey 7 :=
  ⟨![275520, 107520, 262080, 0, 255360, 315840, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 108010, 261632, 560, 254940, 316240, 322945], false⟩

theorem canonicalMatch7_702 :
    canonicalPose7_702.boxKey 188160 (referenceBox7 (!canonicalBox7_702.bump)) = canonicalBox7_702 := by decide +kernel

theorem canonicalDecode7_702 : canonicalBox7_702.toKeyData 188160 = keys7Chunk21.get ⟨30, by decide⟩ := by
  change canonicalBox7_702.toKeyData 188160 = ⟨![(41 / 28), (4 / 7), (39 / 28), 0, (19 / 14), (47 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_702 : keySolid (keys7Chunk21.get ⟨30, by decide⟩) = canonicalPose7_702.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_702 (box := canonicalBox7_702) (k := keys7Chunk21.get ⟨30, by decide⟩) (canonicalMatch7_702) (canonicalDecode7_702)

def canonicalPose7_703 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, false, false, true, true, true], ![2, 0, 1, 0, 2, 2, 2]⟩
def canonicalBox7_703 : BoxKey 7 :=
  ⟨![275520, 134400, 315840, 120960, 376320, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 134785, 316240, 121380, 375760, 261632, 268310], false⟩

theorem canonicalMatch7_703 :
    canonicalPose7_703.boxKey 188160 (referenceBox7 (!canonicalBox7_703.bump)) = canonicalBox7_703 := by decide +kernel

theorem canonicalDecode7_703 : canonicalBox7_703.toKeyData 188160 = keys7Chunk21.get ⟨31, by decide⟩ := by
  change canonicalBox7_703.toKeyData 188160 = ⟨![(41 / 28), (5 / 7), (47 / 28), (9 / 14), 2, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (146 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_703 : keySolid (keys7Chunk21.get ⟨31, by decide⟩) = canonicalPose7_703.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_703 (box := canonicalBox7_703) (k := keys7Chunk21.get ⟨31, by decide⟩) (canonicalMatch7_703) (canonicalDecode7_703)

theorem keys7Chunk21_canonical : ∀ k ∈ keys7Chunk21,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk21, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_672, canonicalSolid7_672⟩
  · exact ⟨canonicalPose7_673, canonicalSolid7_673⟩
  · exact ⟨canonicalPose7_674, canonicalSolid7_674⟩
  · exact ⟨canonicalPose7_675, canonicalSolid7_675⟩
  · exact ⟨canonicalPose7_676, canonicalSolid7_676⟩
  · exact ⟨canonicalPose7_677, canonicalSolid7_677⟩
  · exact ⟨canonicalPose7_678, canonicalSolid7_678⟩
  · exact ⟨canonicalPose7_679, canonicalSolid7_679⟩
  · exact ⟨canonicalPose7_680, canonicalSolid7_680⟩
  · exact ⟨canonicalPose7_681, canonicalSolid7_681⟩
  · exact ⟨canonicalPose7_682, canonicalSolid7_682⟩
  · exact ⟨canonicalPose7_683, canonicalSolid7_683⟩
  · exact ⟨canonicalPose7_684, canonicalSolid7_684⟩
  · exact ⟨canonicalPose7_685, canonicalSolid7_685⟩
  · exact ⟨canonicalPose7_686, canonicalSolid7_686⟩
  · exact ⟨canonicalPose7_687, canonicalSolid7_687⟩
  · exact ⟨canonicalPose7_688, canonicalSolid7_688⟩
  · exact ⟨canonicalPose7_689, canonicalSolid7_689⟩
  · exact ⟨canonicalPose7_690, canonicalSolid7_690⟩
  · exact ⟨canonicalPose7_691, canonicalSolid7_691⟩
  · exact ⟨canonicalPose7_692, canonicalSolid7_692⟩
  · exact ⟨canonicalPose7_693, canonicalSolid7_693⟩
  · exact ⟨canonicalPose7_694, canonicalSolid7_694⟩
  · exact ⟨canonicalPose7_695, canonicalSolid7_695⟩
  · exact ⟨canonicalPose7_696, canonicalSolid7_696⟩
  · exact ⟨canonicalPose7_697, canonicalSolid7_697⟩
  · exact ⟨canonicalPose7_698, canonicalSolid7_698⟩
  · exact ⟨canonicalPose7_699, canonicalSolid7_699⟩
  · exact ⟨canonicalPose7_700, canonicalSolid7_700⟩
  · exact ⟨canonicalPose7_701, canonicalSolid7_701⟩
  · exact ⟨canonicalPose7_702, canonicalSolid7_702⟩
  · exact ⟨canonicalPose7_703, canonicalSolid7_703⟩

#print axioms keys7Chunk21_canonical

end SparseMonotiles.Canonical
