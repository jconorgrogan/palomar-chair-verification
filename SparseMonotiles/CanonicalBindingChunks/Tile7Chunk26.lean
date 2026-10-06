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

def canonicalPose7_832 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, true, true, false, true], ![2, 2, 1, 1, 2, 2, 2]⟩
def canonicalBox7_832 : BoxKey 7 :=
  ⟨![268800, 275520, 53760, 60480, 255360, 376320, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 53375, 60080, 254940, 376880, 261632], true⟩

theorem canonicalMatch7_832 :
    canonicalPose7_832.boxKey 188160 (referenceBox7 (!canonicalBox7_832.bump)) = canonicalBox7_832 := by decide +kernel

theorem canonicalDecode7_832 : canonicalBox7_832.toKeyData 188160 = keys7Chunk26.get ⟨0, by decide⟩ := by
  change canonicalBox7_832.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 2, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (673 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_832 : keySolid (keys7Chunk26.get ⟨0, by decide⟩) = canonicalPose7_832.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_832 (box := canonicalBox7_832) (k := keys7Chunk26.get ⟨0, by decide⟩) (canonicalMatch7_832) (canonicalDecode7_832)

def canonicalPose7_833 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, false, true, false, false], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_833 : BoxKey 7 :=
  ⟨![302400, 268800, 100800, 134400, 248640, 309120, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 268310, 101360, 134785, 248240, 309540, 376880], true⟩

theorem canonicalMatch7_833 :
    canonicalPose7_833.boxKey 188160 (referenceBox7 (!canonicalBox7_833.bump)) = canonicalBox7_833 := by decide +kernel

theorem canonicalDecode7_833 : canonicalBox7_833.toKeyData 188160 = keys7Chunk26.get ⟨1, by decide⟩ := by
  change canonicalBox7_833.toKeyData 188160 = ⟨![(45 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (23 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_833 : keySolid (keys7Chunk26.get ⟨1, by decide⟩) = canonicalPose7_833.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_833 (box := canonicalBox7_833) (k := keys7Chunk26.get ⟨1, by decide⟩) (canonicalMatch7_833) (canonicalDecode7_833)

def canonicalPose7_834 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, false, false, true, false, true], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_834 : BoxKey 7 :=
  ⟨![309120, 248640, 134400, 100800, 268800, 302400, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 248240, 134785, 101360, 268310, 302848, 375760], false⟩

theorem canonicalMatch7_834 :
    canonicalPose7_834.boxKey 188160 (referenceBox7 (!canonicalBox7_834.bump)) = canonicalBox7_834 := by decide +kernel

theorem canonicalDecode7_834 : canonicalBox7_834.toKeyData 188160 = keys7Chunk26.get ⟨2, by decide⟩ := by
  change canonicalBox7_834.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (45 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_834 : keySolid (keys7Chunk26.get ⟨2, by decide⟩) = canonicalPose7_834.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_834 (box := canonicalBox7_834) (k := keys7Chunk26.get ⟨2, by decide⟩) (canonicalMatch7_834) (canonicalDecode7_834)

def canonicalPose7_835 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, false, false, false, false], ![2, 2, 1, 1, 0, 0, 0]⟩
def canonicalBox7_835 : BoxKey 7 :=
  ⟨![376320, 255360, 60480, 322560, 100800, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 254940, 60080, 322945, 101360, 108010, 114688], false⟩

theorem canonicalMatch7_835 :
    canonicalPose7_835.boxKey 188160 (referenceBox7 (!canonicalBox7_835.bump)) = canonicalBox7_835 := by decide +kernel

theorem canonicalDecode7_835 : canonicalBox7_835.toKeyData 188160 = keys7Chunk26.get ⟨3, by decide⟩ := by
  change canonicalBox7_835.toKeyData 188160 = ⟨![2, (19 / 14), (9 / 28), (12 / 7), (15 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (607 / 448), (751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_835 : keySolid (keys7Chunk26.get ⟨3, by decide⟩) = canonicalPose7_835.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_835 (box := canonicalBox7_835) (k := keys7Chunk26.get ⟨3, by decide⟩) (canonicalMatch7_835) (canonicalDecode7_835)

def canonicalPose7_836 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, false, true, false, false, true], ![2, 2, 0, 2, 0, 0, 1]⟩
def canonicalBox7_836 : BoxKey 7 :=
  ⟨![255360, 376320, 114240, 268800, 100800, 134400, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 375760, 114688, 268310, 101360, 134785, 60080], false⟩

theorem canonicalMatch7_836 :
    canonicalPose7_836.boxKey 188160 (referenceBox7 (!canonicalBox7_836.bump)) = canonicalBox7_836 := by decide +kernel

theorem canonicalDecode7_836 : canonicalBox7_836.toKeyData 188160 = keys7Chunk26.get ⟨4, by decide⟩ := by
  change canonicalBox7_836.toKeyData 188160 = ⟨![(19 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (5 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_836 : keySolid (keys7Chunk26.get ⟨4, by decide⟩) = canonicalPose7_836.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_836 (box := canonicalBox7_836) (k := keys7Chunk26.get ⟨4, by decide⟩) (canonicalMatch7_836) (canonicalDecode7_836)

def canonicalPose7_837 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, true, true, true, false, true, false], ![1, 2, 0, 2, 0, 1, 0]⟩
def canonicalBox7_837 : BoxKey 7 :=
  ⟨![309120, 262080, 0, 268800, 100800, 53760, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 261632, -560, 268310, 101360, 53375, 128080], true⟩

theorem canonicalMatch7_837 :
    canonicalPose7_837.boxKey 188160 (referenceBox7 (!canonicalBox7_837.bump)) = canonicalBox7_837 := by decide +kernel

theorem canonicalDecode7_837 : canonicalBox7_837.toKeyData 188160 = keys7Chunk26.get ⟨5, by decide⟩ := by
  change canonicalBox7_837.toKeyData 188160 = ⟨![(23 / 14), (39 / 28), 0, (10 / 7), (15 / 28), (2 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (146 / 105), (-1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_837 : keySolid (keys7Chunk26.get ⟨5, by decide⟩) = canonicalPose7_837.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_837 (box := canonicalBox7_837) (k := keys7Chunk26.get ⟨5, by decide⟩) (canonicalMatch7_837) (canonicalDecode7_837)

def canonicalPose7_838 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, true, false, true, false, true, false], ![1, 2, 0, 2, 0, 1, 0]⟩
def canonicalBox7_838 : BoxKey 7 :=
  ⟨![322560, 275520, 107520, 376320, 114240, 67200, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 274960, 108010, 375760, 114688, 66780, 128080], false⟩

theorem canonicalMatch7_838 :
    canonicalPose7_838.boxKey 188160 (referenceBox7 (!canonicalBox7_838.bump)) = canonicalBox7_838 := by decide +kernel

theorem canonicalDecode7_838 : canonicalBox7_838.toKeyData 188160 = keys7Chunk26.get ⟨6, by decide⟩ := by
  change canonicalBox7_838.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (4 / 7), 2, (17 / 28), (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (1543 / 2688), (671 / 336), (64 / 105), (159 / 448), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_838 : keySolid (keys7Chunk26.get ⟨6, by decide⟩) = canonicalPose7_838.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_838 (box := canonicalBox7_838) (k := keys7Chunk26.get ⟨6, by decide⟩) (canonicalMatch7_838) (canonicalDecode7_838)

def canonicalPose7_839 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, true, true, false, true], ![2, 2, 0, 2, 0, 0, 1]⟩
def canonicalBox7_839 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 262080, 0, 120960, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 261632, -560, 121380, 60080], true⟩

theorem canonicalMatch7_839 :
    canonicalPose7_839.boxKey 188160 (referenceBox7 (!canonicalBox7_839.bump)) = canonicalBox7_839 := by decide +kernel

theorem canonicalDecode7_839 : canonicalBox7_839.toKeyData 188160 = keys7Chunk26.get ⟨7, by decide⟩ := by
  change canonicalBox7_839.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (-1 / 336), (289 / 448), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_839 : keySolid (keys7Chunk26.get ⟨7, by decide⟩) = canonicalPose7_839.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_839 (box := canonicalBox7_839) (k := keys7Chunk26.get ⟨7, by decide⟩) (canonicalMatch7_839) (canonicalDecode7_839)

def canonicalPose7_840 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, false, false, true, false], ![2, 2, 1, 1, 0, 0, 0]⟩
def canonicalBox7_840 : BoxKey 7 :=
  ⟨![268800, 275520, 53760, 315840, 120960, 0, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 53375, 316240, 121380, -560, 114688], true⟩

theorem canonicalMatch7_840 :
    canonicalPose7_840.boxKey 188160 (referenceBox7 (!canonicalBox7_840.bump)) = canonicalBox7_840 := by decide +kernel

theorem canonicalDecode7_840 : canonicalBox7_840.toKeyData 188160 = keys7Chunk26.get ⟨8, by decide⟩ := by
  change canonicalBox7_840.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (2 / 7), (47 / 28), (9 / 14), 0, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_840 : keySolid (keys7Chunk26.get ⟨8, by decide⟩) = canonicalPose7_840.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_840 (box := canonicalBox7_840) (k := keys7Chunk26.get ⟨8, by decide⟩) (canonicalMatch7_840) (canonicalDecode7_840)

def canonicalPose7_841 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, true, false, true, true], ![1, 2, 0, 2, 0, 1, 0]⟩
def canonicalBox7_841 : BoxKey 7 :=
  ⟨![302400, 268800, 100800, 241920, 127680, 67200, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 268310, 101360, 241535, 128080, 66780, -560], true⟩

theorem canonicalMatch7_841 :
    canonicalPose7_841.boxKey 188160 (referenceBox7 (!canonicalBox7_841.bump)) = canonicalBox7_841 := by decide +kernel

theorem canonicalDecode7_841 : canonicalBox7_841.toKeyData 188160 = keys7Chunk26.get ⟨9, by decide⟩ := by
  change canonicalBox7_841.toKeyData 188160 = ⟨![(45 / 28), (10 / 7), (15 / 28), (9 / 7), (19 / 28), (5 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_841 : keySolid (keys7Chunk26.get ⟨9, by decide⟩) = canonicalPose7_841.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_841 (box := canonicalBox7_841) (k := keys7Chunk26.get ⟨9, by decide⟩) (canonicalMatch7_841) (canonicalDecode7_841)

def canonicalPose7_842 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, false, true, false, true, false], ![1, 2, 0, 2, 0, 1, 0]⟩
def canonicalBox7_842 : BoxKey 7 :=
  ⟨![309120, 248640, 134400, 275520, 107520, 73920, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 248240, 134785, 274960, 108010, 73472, 560], false⟩

theorem canonicalMatch7_842 :
    canonicalPose7_842.boxKey 188160 (referenceBox7 (!canonicalBox7_842.bump)) = canonicalBox7_842 := by decide +kernel

theorem canonicalDecode7_842 : canonicalBox7_842.toKeyData 188160 = keys7Chunk26.get ⟨10, by decide⟩ := by
  change canonicalBox7_842.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (5 / 7), (41 / 28), (4 / 7), (11 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_842 : keySolid (keys7Chunk26.get ⟨10, by decide⟩) = canonicalPose7_842.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_842 (box := canonicalBox7_842) (k := keys7Chunk26.get ⟨10, by decide⟩) (canonicalMatch7_842) (canonicalDecode7_842)

def canonicalPose7_843 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, true, false, false, false, true], ![2, 2, 1, 1, 0, 0, 2]⟩
def canonicalBox7_843 : BoxKey 7 :=
  ⟨![376320, 255360, 60480, 322560, 100800, 107520, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 254940, 60080, 322945, 101360, 108010, 261632], true⟩

theorem canonicalMatch7_843 :
    canonicalPose7_843.boxKey 188160 (referenceBox7 (!canonicalBox7_843.bump)) = canonicalBox7_843 := by decide +kernel

theorem canonicalDecode7_843 : canonicalBox7_843.toKeyData 188160 = keys7Chunk26.get ⟨11, by decide⟩ := by
  change canonicalBox7_843.toKeyData 188160 = ⟨![2, (19 / 14), (9 / 28), (12 / 7), (15 / 28), (4 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (607 / 448), (751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_843 : keySolid (keys7Chunk26.get ⟨11, by decide⟩) = canonicalPose7_843.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_843 (box := canonicalBox7_843) (k := keys7Chunk26.get ⟨11, by decide⟩) (canonicalMatch7_843) (canonicalDecode7_843)

def canonicalPose7_844 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, false, true, false, false, false], ![2, 2, 0, 2, 0, 0, 1]⟩
def canonicalBox7_844 : BoxKey 7 :=
  ⟨![255360, 376320, 114240, 268800, 100800, 134400, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 376880, 114688, 268310, 101360, 134785, 316240], true⟩

theorem canonicalMatch7_844 :
    canonicalPose7_844.boxKey 188160 (referenceBox7 (!canonicalBox7_844.bump)) = canonicalBox7_844 := by decide +kernel

theorem canonicalDecode7_844 : canonicalBox7_844.toKeyData 188160 = keys7Chunk26.get ⟨12, by decide⟩ := by
  change canonicalBox7_844.toKeyData 188160 = ⟨![(19 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (5 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (673 / 336), (64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_844 : keySolid (keys7Chunk26.get ⟨12, by decide⟩) = canonicalPose7_844.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_844 (box := canonicalBox7_844) (k := keys7Chunk26.get ⟨12, by decide⟩) (canonicalMatch7_844) (canonicalDecode7_844)

def canonicalPose7_845 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, true, false, true, false, true, true], ![1, 2, 0, 2, 0, 1, 2]⟩
def canonicalBox7_845 : BoxKey 7 :=
  ⟨![309120, 262080, 0, 268800, 100800, 53760, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 261632, 560, 268310, 101360, 53375, 248240], false⟩

theorem canonicalMatch7_845 :
    canonicalPose7_845.boxKey 188160 (referenceBox7 (!canonicalBox7_845.bump)) = canonicalBox7_845 := by decide +kernel

theorem canonicalDecode7_845 : canonicalBox7_845.toKeyData 188160 = keys7Chunk26.get ⟨13, by decide⟩ := by
  change canonicalBox7_845.toKeyData 188160 = ⟨![(23 / 14), (39 / 28), 0, (10 / 7), (15 / 28), (2 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (146 / 105), (1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_845 : keySolid (keys7Chunk26.get ⟨13, by decide⟩) = canonicalPose7_845.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_845 (box := canonicalBox7_845) (k := keys7Chunk26.get ⟨13, by decide⟩) (canonicalMatch7_845) (canonicalDecode7_845)

def canonicalPose7_846 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, true, false, false, false, true, true], ![1, 2, 0, 2, 0, 1, 2]⟩
def canonicalBox7_846 : BoxKey 7 :=
  ⟨![322560, 275520, 107520, 376320, 114240, 67200, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 274960, 108010, 376880, 114688, 66780, 248240], true⟩

theorem canonicalMatch7_846 :
    canonicalPose7_846.boxKey 188160 (referenceBox7 (!canonicalBox7_846.bump)) = canonicalBox7_846 := by decide +kernel

theorem canonicalDecode7_846 : canonicalBox7_846.toKeyData 188160 = keys7Chunk26.get ⟨14, by decide⟩ := by
  change canonicalBox7_846.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (4 / 7), 2, (17 / 28), (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (1543 / 2688), (673 / 336), (64 / 105), (159 / 448), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_846 : keySolid (keys7Chunk26.get ⟨14, by decide⟩) = canonicalPose7_846.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_846 (box := canonicalBox7_846) (k := keys7Chunk26.get ⟨14, by decide⟩) (canonicalMatch7_846) (canonicalDecode7_846)

def canonicalPose7_847 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, true, false, false, false], ![2, 2, 0, 2, 0, 0, 1]⟩
def canonicalBox7_847 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 262080, 0, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 261632, 560, 121380, 316240], false⟩

theorem canonicalMatch7_847 :
    canonicalPose7_847.boxKey 188160 (referenceBox7 (!canonicalBox7_847.bump)) = canonicalBox7_847 := by decide +kernel

theorem canonicalDecode7_847 : canonicalBox7_847.toKeyData 188160 = keys7Chunk26.get ⟨15, by decide⟩ := by
  change canonicalBox7_847.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_847 : keySolid (keys7Chunk26.get ⟨15, by decide⟩) = canonicalPose7_847.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_847 (box := canonicalBox7_847) (k := keys7Chunk26.get ⟨15, by decide⟩) (canonicalMatch7_847) (canonicalDecode7_847)

def canonicalPose7_848 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, false, false, false, true], ![2, 2, 1, 1, 0, 0, 2]⟩
def canonicalBox7_848 : BoxKey 7 :=
  ⟨![268800, 275520, 53760, 315840, 120960, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 53375, 316240, 121380, 560, 261632], false⟩

theorem canonicalMatch7_848 :
    canonicalPose7_848.boxKey 188160 (referenceBox7 (!canonicalBox7_848.bump)) = canonicalBox7_848 := by decide +kernel

theorem canonicalDecode7_848 : canonicalBox7_848.toKeyData 188160 = keys7Chunk26.get ⟨16, by decide⟩ := by
  change canonicalBox7_848.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (2 / 7), (47 / 28), (9 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_848 : keySolid (keys7Chunk26.get ⟨16, by decide⟩) = canonicalPose7_848.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_848 (box := canonicalBox7_848) (k := keys7Chunk26.get ⟨16, by decide⟩) (canonicalMatch7_848) (canonicalDecode7_848)

def canonicalPose7_849 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, true, false, true, true], ![1, 2, 0, 2, 0, 1, 2]⟩
def canonicalBox7_849 : BoxKey 7 :=
  ⟨![302400, 268800, 100800, 241920, 127680, 67200, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 268310, 101360, 241535, 128080, 66780, 375760], false⟩

theorem canonicalMatch7_849 :
    canonicalPose7_849.boxKey 188160 (referenceBox7 (!canonicalBox7_849.bump)) = canonicalBox7_849 := by decide +kernel

theorem canonicalDecode7_849 : canonicalBox7_849.toKeyData 188160 = keys7Chunk26.get ⟨17, by decide⟩ := by
  change canonicalBox7_849.toKeyData 188160 = ⟨![(45 / 28), (10 / 7), (15 / 28), (9 / 7), (19 / 28), (5 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_849 : keySolid (keys7Chunk26.get ⟨17, by decide⟩) = canonicalPose7_849.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_849 (box := canonicalBox7_849) (k := keys7Chunk26.get ⟨17, by decide⟩) (canonicalMatch7_849) (canonicalDecode7_849)

def canonicalPose7_850 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, false, true, false, true, false], ![1, 2, 0, 2, 0, 1, 2]⟩
def canonicalBox7_850 : BoxKey 7 :=
  ⟨![309120, 248640, 134400, 275520, 107520, 73920, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 248240, 134785, 274960, 108010, 73472, 376880], true⟩

theorem canonicalMatch7_850 :
    canonicalPose7_850.boxKey 188160 (referenceBox7 (!canonicalBox7_850.bump)) = canonicalBox7_850 := by decide +kernel

theorem canonicalDecode7_850 : canonicalBox7_850.toKeyData 188160 = keys7Chunk26.get ⟨18, by decide⟩ := by
  change canonicalBox7_850.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (5 / 7), (41 / 28), (4 / 7), (11 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_850 : keySolid (keys7Chunk26.get ⟨18, by decide⟩) = canonicalPose7_850.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_850 (box := canonicalBox7_850) (k := keys7Chunk26.get ⟨18, by decide⟩) (canonicalMatch7_850) (canonicalDecode7_850)

def canonicalPose7_851 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, true, false, false, false, false, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_851 : BoxKey 7 :=
  ⟨![376320, 268800, 100800, 322560, 127680, 309120, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![375760, 268310, 101360, 322945, 128080, 309540, 114688], false⟩

theorem canonicalMatch7_851 :
    canonicalPose7_851.boxKey 188160 (referenceBox7 (!canonicalBox7_851.bump)) = canonicalBox7_851 := by decide +kernel

theorem canonicalDecode7_851 : canonicalBox7_851.toKeyData 188160 = keys7Chunk26.get ⟨19, by decide⟩ := by
  change canonicalBox7_851.toKeyData 188160 = ⟨![2, (10 / 7), (15 / 28), (12 / 7), (19 / 28), (23 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(671 / 336), (3833 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_851 : keySolid (keys7Chunk26.get ⟨19, by decide⟩) = canonicalPose7_851.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_851 (box := canonicalBox7_851) (k := keys7Chunk26.get ⟨19, by decide⟩) (canonicalMatch7_851) (canonicalDecode7_851)

def canonicalPose7_852 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, false, false, false, false, false, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_852 : BoxKey 7 :=
  ⟨![268800, 376320, 114240, 309120, 127680, 322560, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 376880, 114688, 309540, 128080, 322945, 101360], true⟩

theorem canonicalMatch7_852 :
    canonicalPose7_852.boxKey 188160 (referenceBox7 (!canonicalBox7_852.bump)) = canonicalBox7_852 := by decide +kernel

theorem canonicalDecode7_852 : canonicalBox7_852.toKeyData 188160 = keys7Chunk26.get ⟨20, by decide⟩ := by
  change canonicalBox7_852.toKeyData 188160 = ⟨![(10 / 7), 2, (17 / 28), (23 / 14), (19 / 28), (12 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (673 / 336), (64 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_852 : keySolid (keys7Chunk26.get ⟨20, by decide⟩) = canonicalPose7_852.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_852 (box := canonicalBox7_852) (k := keys7Chunk26.get ⟨20, by decide⟩) (canonicalMatch7_852) (canonicalDecode7_852)

def canonicalPose7_853 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, false, true, true, true, false], ![2, 2, 0, 2, 1, 2, 0]⟩
def canonicalBox7_853 : BoxKey 7 :=
  ⟨![268800, 262080, 0, 255360, 60480, 241920, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 560, 254940, 60080, 241535, 101360], false⟩

theorem canonicalMatch7_853 :
    canonicalPose7_853.boxKey 188160 (referenceBox7 (!canonicalBox7_853.bump)) = canonicalBox7_853 := by decide +kernel

theorem canonicalDecode7_853 : canonicalBox7_853.toKeyData 188160 = keys7Chunk26.get ⟨21, by decide⟩ := by
  change canonicalBox7_853.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 0, (19 / 14), (9 / 28), (9 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (1 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_853 : keySolid (keys7Chunk26.get ⟨21, by decide⟩) = canonicalPose7_853.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_853 (box := canonicalBox7_853) (k := keys7Chunk26.get ⟨21, by decide⟩) (canonicalMatch7_853) (canonicalDecode7_853)

def canonicalPose7_854 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, true, false, true, false], ![1, 1, 0, 2, 0, 2, 0]⟩
def canonicalBox7_854 : BoxKey 7 :=
  ⟨![322560, 315840, 120960, 376320, 114240, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 316240, 121380, 375760, 114688, 268310, 101360], false⟩

theorem canonicalMatch7_854 :
    canonicalPose7_854.boxKey 188160 (referenceBox7 (!canonicalBox7_854.bump)) = canonicalBox7_854 := by decide +kernel

theorem canonicalDecode7_854 : canonicalBox7_854.toKeyData 188160 = keys7Chunk26.get ⟨22, by decide⟩ := by
  change canonicalBox7_854.toKeyData 188160 = ⟨![(12 / 7), (47 / 28), (9 / 14), 2, (17 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (64 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_854 : keySolid (keys7Chunk26.get ⟨22, by decide⟩) = canonicalPose7_854.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_854 (box := canonicalBox7_854) (k := keys7Chunk26.get ⟨22, by decide⟩) (canonicalMatch7_854) (canonicalDecode7_854)

def canonicalPose7_855 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, false, false, false, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_855 : BoxKey 7 :=
  ⟨![275520, 241920, 127680, 309120, 0, 302400, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 128080, 309540, 560, 302848, 108010], false⟩

theorem canonicalMatch7_855 :
    canonicalPose7_855.boxKey 188160 (referenceBox7 (!canonicalBox7_855.bump)) = canonicalBox7_855 := by decide +kernel

theorem canonicalDecode7_855 : canonicalBox7_855.toKeyData 188160 = keys7Chunk26.get ⟨23, by decide⟩ := by
  change canonicalBox7_855.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (19 / 28), (23 / 14), 0, (45 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448), (1 / 336), (169 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_855 : keySolid (keys7Chunk26.get ⟨23, by decide⟩) = canonicalPose7_855.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_855 (box := canonicalBox7_855) (k := keys7Chunk26.get ⟨23, by decide⟩) (canonicalMatch7_855) (canonicalDecode7_855)

def canonicalPose7_856 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, false, true, false, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_856 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 302400, 0, 309120, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 302848, -560, 309540, 128080], true⟩

theorem canonicalMatch7_856 :
    canonicalPose7_856.boxKey 188160 (referenceBox7 (!canonicalBox7_856.bump)) = canonicalBox7_856 := by decide +kernel

theorem canonicalDecode7_856 : canonicalBox7_856.toKeyData 188160 = keys7Chunk26.get ⟨24, by decide⟩ := by
  change canonicalBox7_856.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (45 / 28), 0, (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105), (-1 / 336), (737 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_856 : keySolid (keys7Chunk26.get ⟨24, by decide⟩) = canonicalPose7_856.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_856 (box := canonicalBox7_856) (k := keys7Chunk26.get ⟨24, by decide⟩) (canonicalMatch7_856) (canonicalDecode7_856)

def canonicalPose7_857 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, true, false, false, false], ![1, 1, 0, 2, 0, 2, 0]⟩
def canonicalBox7_857 : BoxKey 7 :=
  ⟨![315840, 322560, 100800, 268800, 114240, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 322945, 101360, 268310, 114688, 376880, 121380], true⟩

theorem canonicalMatch7_857 :
    canonicalPose7_857.boxKey 188160 (referenceBox7 (!canonicalBox7_857.bump)) = canonicalBox7_857 := by decide +kernel

theorem canonicalDecode7_857 : canonicalBox7_857.toKeyData 188160 = keys7Chunk26.get ⟨25, by decide⟩ := by
  change canonicalBox7_857.toKeyData 188160 = ⟨![(47 / 28), (12 / 7), (15 / 28), (10 / 7), (17 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (64 / 105), (673 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_857 : keySolid (keys7Chunk26.get ⟨25, by decide⟩) = canonicalPose7_857.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_857 (box := canonicalBox7_857) (k := keys7Chunk26.get ⟨25, by decide⟩) (canonicalMatch7_857) (canonicalDecode7_857)

def canonicalPose7_858 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, true, true, true, true], ![2, 2, 0, 2, 1, 2, 0]⟩
def canonicalBox7_858 : BoxKey 7 :=
  ⟨![262080, 268800, 100800, 241920, 60480, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 101360, 241535, 60080, 254940, -560], true⟩

theorem canonicalMatch7_858 :
    canonicalPose7_858.boxKey 188160 (referenceBox7 (!canonicalBox7_858.bump)) = canonicalBox7_858 := by decide +kernel

theorem canonicalDecode7_858 : canonicalBox7_858.toKeyData 188160 = keys7Chunk26.get ⟨26, by decide⟩ := by
  change canonicalBox7_858.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (15 / 28), (9 / 7), (9 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_858 : keySolid (keys7Chunk26.get ⟨26, by decide⟩) = canonicalPose7_858.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_858 (box := canonicalBox7_858) (k := keys7Chunk26.get ⟨26, by decide⟩) (canonicalMatch7_858) (canonicalDecode7_858)

def canonicalPose7_859 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, true, true, true, true, true, true], ![2, 2, 1, 2, 1, 2, 2]⟩
def canonicalBox7_859 : BoxKey 7 :=
  ⟨![376320, 262080, 67200, 248640, 53760, 275520, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![375760, 261632, 66780, 248240, 53375, 274960, 268310], false⟩

theorem canonicalMatch7_859 :
    canonicalPose7_859.boxKey 188160 (referenceBox7 (!canonicalBox7_859.bump)) = canonicalBox7_859 := by decide +kernel

theorem canonicalDecode7_859 : canonicalBox7_859.toKeyData 188160 = keys7Chunk26.get ⟨27, by decide⟩ := by
  change canonicalBox7_859.toKeyData 188160 = ⟨![2, (39 / 28), (5 / 14), (37 / 28), (2 / 7), (41 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(671 / 336), (146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_859 : keySolid (keys7Chunk26.get ⟨27, by decide⟩) = canonicalPose7_859.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_859 (box := canonicalBox7_859) (k := keys7Chunk26.get ⟨27, by decide⟩) (canonicalMatch7_859) (canonicalDecode7_859)

def canonicalPose7_860 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, false, false, false, true, true], ![2, 2, 0, 1, 0, 2, 2]⟩
def canonicalBox7_860 : BoxKey 7 :=
  ⟨![262080, 376320, 120960, 315840, 134400, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 376880, 121380, 316240, 134785, 274960, 268310], true⟩

theorem canonicalMatch7_860 :
    canonicalPose7_860.boxKey 188160 (referenceBox7 (!canonicalBox7_860.bump)) = canonicalBox7_860 := by decide +kernel

theorem canonicalDecode7_860 : canonicalBox7_860.toKeyData 188160 = keys7Chunk26.get ⟨28, by decide⟩ := by
  change canonicalBox7_860.toKeyData 188160 = ⟨![(39 / 28), 2, (9 / 14), (47 / 28), (5 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_860 : keySolid (keys7Chunk26.get ⟨28, by decide⟩) = canonicalPose7_860.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_860 (box := canonicalBox7_860) (k := keys7Chunk26.get ⟨28, by decide⟩) (canonicalMatch7_860) (canonicalDecode7_860)

def canonicalPose7_861 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, true, true, false, true, false], ![1, 2, 0, 2, 0, 2, 1]⟩
def canonicalBox7_861 : BoxKey 7 :=
  ⟨![315840, 255360, 0, 262080, 107520, 275520, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 254940, -560, 261632, 108010, 274960, 322945], true⟩

theorem canonicalMatch7_861 :
    canonicalPose7_861.boxKey 188160 (referenceBox7 (!canonicalBox7_861.bump)) = canonicalBox7_861 := by decide +kernel

theorem canonicalDecode7_861 : canonicalBox7_861.toKeyData 188160 = keys7Chunk26.get ⟨29, by decide⟩ := by
  change canonicalBox7_861.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), 0, (39 / 28), (4 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_861 : keySolid (keys7Chunk26.get ⟨29, by decide⟩) = canonicalPose7_861.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_861 (box := canonicalBox7_861) (k := keys7Chunk26.get ⟨29, by decide⟩) (canonicalMatch7_861) (canonicalDecode7_861)

def canonicalPose7_862 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, true, true, true, true, true], ![2, 2, 1, 2, 1, 2, 2]⟩
def canonicalBox7_862 : BoxKey 7 :=
  ⟨![275520, 268800, 73920, 376320, 67200, 248640, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 73472, 375760, 66780, 248240, 241535], false⟩

theorem canonicalMatch7_862 :
    canonicalPose7_862.boxKey 188160 (referenceBox7 (!canonicalBox7_862.bump)) = canonicalBox7_862 := by decide +kernel

theorem canonicalDecode7_862 : canonicalBox7_862.toKeyData 188160 = keys7Chunk26.get ⟨30, by decide⟩ := by
  change canonicalBox7_862.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (11 / 28), 2, (5 / 14), (37 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (41 / 105), (671 / 336), (159 / 448), (3103 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_862 : keySolid (keys7Chunk26.get ⟨30, by decide⟩) = canonicalPose7_862.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_862 (box := canonicalBox7_862) (k := keys7Chunk26.get ⟨30, by decide⟩) (canonicalMatch7_862) (canonicalDecode7_862)

def canonicalPose7_863 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, false, true, true, true], ![2, 2, 1, 2, 1, 2, 2]⟩
def canonicalBox7_863 : BoxKey 7 :=
  ⟨![241920, 248640, 67200, 376320, 73920, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 248240, 66780, 376880, 73472, 268310, 274960], true⟩

theorem canonicalMatch7_863 :
    canonicalPose7_863.boxKey 188160 (referenceBox7 (!canonicalBox7_863.bump)) = canonicalBox7_863 := by decide +kernel

theorem canonicalDecode7_863 : canonicalBox7_863.toKeyData 188160 = keys7Chunk26.get ⟨31, by decide⟩ := by
  change canonicalBox7_863.toKeyData 188160 = ⟨![(9 / 7), (37 / 28), (5 / 14), 2, (11 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (3103 / 2352), (159 / 448), (673 / 336), (41 / 105), (3833 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_863 : keySolid (keys7Chunk26.get ⟨31, by decide⟩) = canonicalPose7_863.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_863 (box := canonicalBox7_863) (k := keys7Chunk26.get ⟨31, by decide⟩) (canonicalMatch7_863) (canonicalDecode7_863)

theorem keys7Chunk26_canonical : ∀ k ∈ keys7Chunk26,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk26, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_832, canonicalSolid7_832⟩
  · exact ⟨canonicalPose7_833, canonicalSolid7_833⟩
  · exact ⟨canonicalPose7_834, canonicalSolid7_834⟩
  · exact ⟨canonicalPose7_835, canonicalSolid7_835⟩
  · exact ⟨canonicalPose7_836, canonicalSolid7_836⟩
  · exact ⟨canonicalPose7_837, canonicalSolid7_837⟩
  · exact ⟨canonicalPose7_838, canonicalSolid7_838⟩
  · exact ⟨canonicalPose7_839, canonicalSolid7_839⟩
  · exact ⟨canonicalPose7_840, canonicalSolid7_840⟩
  · exact ⟨canonicalPose7_841, canonicalSolid7_841⟩
  · exact ⟨canonicalPose7_842, canonicalSolid7_842⟩
  · exact ⟨canonicalPose7_843, canonicalSolid7_843⟩
  · exact ⟨canonicalPose7_844, canonicalSolid7_844⟩
  · exact ⟨canonicalPose7_845, canonicalSolid7_845⟩
  · exact ⟨canonicalPose7_846, canonicalSolid7_846⟩
  · exact ⟨canonicalPose7_847, canonicalSolid7_847⟩
  · exact ⟨canonicalPose7_848, canonicalSolid7_848⟩
  · exact ⟨canonicalPose7_849, canonicalSolid7_849⟩
  · exact ⟨canonicalPose7_850, canonicalSolid7_850⟩
  · exact ⟨canonicalPose7_851, canonicalSolid7_851⟩
  · exact ⟨canonicalPose7_852, canonicalSolid7_852⟩
  · exact ⟨canonicalPose7_853, canonicalSolid7_853⟩
  · exact ⟨canonicalPose7_854, canonicalSolid7_854⟩
  · exact ⟨canonicalPose7_855, canonicalSolid7_855⟩
  · exact ⟨canonicalPose7_856, canonicalSolid7_856⟩
  · exact ⟨canonicalPose7_857, canonicalSolid7_857⟩
  · exact ⟨canonicalPose7_858, canonicalSolid7_858⟩
  · exact ⟨canonicalPose7_859, canonicalSolid7_859⟩
  · exact ⟨canonicalPose7_860, canonicalSolid7_860⟩
  · exact ⟨canonicalPose7_861, canonicalSolid7_861⟩
  · exact ⟨canonicalPose7_862, canonicalSolid7_862⟩
  · exact ⟨canonicalPose7_863, canonicalSolid7_863⟩

#print axioms keys7Chunk26_canonical

end SparseMonotiles.Canonical
