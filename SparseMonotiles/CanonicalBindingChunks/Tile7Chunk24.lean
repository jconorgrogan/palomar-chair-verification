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

def canonicalPose7_768 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, false, false, true, true, true, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_768 : BoxKey 7 :=
  ⟨![322560, 127680, 309120, 262080, 376320, 268800, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 128080, 309540, 261632, 375760, 268310, 274960], false⟩

theorem canonicalMatch7_768 :
    canonicalPose7_768.boxKey 188160 (referenceBox7 (!canonicalBox7_768.bump)) = canonicalBox7_768 := by decide +kernel

theorem canonicalDecode7_768 : canonicalBox7_768.toKeyData 188160 = keys7Chunk24.get ⟨0, by decide⟩ := by
  change canonicalBox7_768.toKeyData 188160 = ⟨![(12 / 7), (19 / 28), (23 / 14), (39 / 28), 2, (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (671 / 336), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_768 : keySolid (keys7Chunk24.get ⟨0, by decide⟩) = canonicalPose7_768.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_768 (box := canonicalBox7_768) (k := keys7Chunk24.get ⟨0, by decide⟩) (canonicalMatch7_768) (canonicalDecode7_768)

def canonicalPose7_769 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, false, false, true, true, false, true], ![1, 0, 1, 2, 2, 2, 2]⟩
def canonicalBox7_769 : BoxKey 7 :=
  ⟨![309120, 127680, 322560, 275520, 268800, 376320, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 128080, 322945, 274960, 268310, 376880, 261632], true⟩

theorem canonicalMatch7_769 :
    canonicalPose7_769.boxKey 188160 (referenceBox7 (!canonicalBox7_769.bump)) = canonicalBox7_769 := by decide +kernel

theorem canonicalDecode7_769 : canonicalBox7_769.toKeyData 188160 = keys7Chunk24.get ⟨1, by decide⟩ := by
  change canonicalBox7_769.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (12 / 7), (41 / 28), (10 / 7), 2, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688), (673 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_769 : keySolid (keys7Chunk24.get ⟨1, by decide⟩) = canonicalPose7_769.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_769 (box := canonicalBox7_769) (k := keys7Chunk24.get ⟨1, by decide⟩) (canonicalMatch7_769) (canonicalDecode7_769)

def canonicalPose7_770 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, true, true, true], ![2, 1, 2, 2, 2, 2, 2]⟩
def canonicalBox7_770 : BoxKey 7 :=
  ⟨![255360, 60480, 241920, 275520, 268800, 262080, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 241535, 274960, 268310, 261632, 375760], false⟩

theorem canonicalMatch7_770 :
    canonicalPose7_770.boxKey 188160 (referenceBox7 (!canonicalBox7_770.bump)) = canonicalBox7_770 := by decide +kernel

theorem canonicalDecode7_770 : canonicalBox7_770.toKeyData 188160 = keys7Chunk24.get ⟨2, by decide⟩ := by
  change canonicalBox7_770.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (9 / 7), (41 / 28), (10 / 7), (39 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_770 : keySolid (keys7Chunk24.get ⟨2, by decide⟩) = canonicalPose7_770.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_770 (box := canonicalBox7_770) (k := keys7Chunk24.get ⟨2, by decide⟩) (canonicalMatch7_770) (canonicalDecode7_770)

def canonicalPose7_771 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, true, false, true, false, true, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_771 : BoxKey 7 :=
  ⟨![376320, 268800, 100800, 53760, 127680, 67200, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![375760, 268310, 101360, 53375, 128080, 66780, 114688], false⟩

theorem canonicalMatch7_771 :
    canonicalPose7_771.boxKey 188160 (referenceBox7 (!canonicalBox7_771.bump)) = canonicalBox7_771 := by decide +kernel

theorem canonicalDecode7_771 : canonicalBox7_771.toKeyData 188160 = keys7Chunk24.get ⟨3, by decide⟩ := by
  change canonicalBox7_771.toKeyData 188160 = ⟨![2, (10 / 7), (15 / 28), (2 / 7), (19 / 28), (5 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(671 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_771 : keySolid (keys7Chunk24.get ⟨3, by decide⟩) = canonicalPose7_771.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_771 (box := canonicalBox7_771) (k := keys7Chunk24.get ⟨3, by decide⟩) (canonicalMatch7_771) (canonicalDecode7_771)

def canonicalPose7_772 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, false, false, true, false, true, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_772 : BoxKey 7 :=
  ⟨![268800, 376320, 114240, 67200, 127680, 53760, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 376880, 114688, 66780, 128080, 53375, 101360], true⟩

theorem canonicalMatch7_772 :
    canonicalPose7_772.boxKey 188160 (referenceBox7 (!canonicalBox7_772.bump)) = canonicalBox7_772 := by decide +kernel

theorem canonicalDecode7_772 : canonicalBox7_772.toKeyData 188160 = keys7Chunk24.get ⟨4, by decide⟩ := by
  change canonicalBox7_772.toKeyData 188160 = ⟨![(10 / 7), 2, (17 / 28), (5 / 14), (19 / 28), (2 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (673 / 336), (64 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_772 : keySolid (keys7Chunk24.get ⟨4, by decide⟩) = canonicalPose7_772.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_772 (box := canonicalBox7_772) (k := keys7Chunk24.get ⟨4, by decide⟩) (canonicalMatch7_772) (canonicalDecode7_772)

def canonicalPose7_773 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, false, false, true, false, false], ![2, 2, 0, 0, 1, 0, 0]⟩
def canonicalBox7_773 : BoxKey 7 :=
  ⟨![268800, 262080, 0, 120960, 60480, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 560, 121380, 60080, 134785, 101360], false⟩

theorem canonicalMatch7_773 :
    canonicalPose7_773.boxKey 188160 (referenceBox7 (!canonicalBox7_773.bump)) = canonicalBox7_773 := by decide +kernel

theorem canonicalDecode7_773 : canonicalBox7_773.toKeyData 188160 = keys7Chunk24.get ⟨5, by decide⟩ := by
  change canonicalBox7_773.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 0, (9 / 14), (9 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (1 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_773 : keySolid (keys7Chunk24.get ⟨5, by decide⟩) = canonicalPose7_773.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_773 (box := canonicalBox7_773) (k := keys7Chunk24.get ⟨5, by decide⟩) (canonicalMatch7_773) (canonicalDecode7_773)

def canonicalPose7_774 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, false, false, false, false], ![1, 1, 0, 0, 0, 0, 0]⟩
def canonicalBox7_774 : BoxKey 7 :=
  ⟨![322560, 315840, 120960, 0, 114240, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 316240, 121380, 560, 114688, 108010, 101360], false⟩

theorem canonicalMatch7_774 :
    canonicalPose7_774.boxKey 188160 (referenceBox7 (!canonicalBox7_774.bump)) = canonicalBox7_774 := by decide +kernel

theorem canonicalDecode7_774 : canonicalBox7_774.toKeyData 188160 = keys7Chunk24.get ⟨6, by decide⟩ := by
  change canonicalBox7_774.toKeyData 188160 = ⟨![(12 / 7), (47 / 28), (9 / 14), 0, (17 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_774 : keySolid (keys7Chunk24.get ⟨6, by decide⟩) = canonicalPose7_774.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_774 (box := canonicalBox7_774) (k := keys7Chunk24.get ⟨6, by decide⟩) (canonicalMatch7_774) (canonicalDecode7_774)

def canonicalPose7_775 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, true, false, true, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_775 : BoxKey 7 :=
  ⟨![275520, 241920, 127680, 67200, 0, 73920, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 128080, 66780, 560, 73472, 108010], false⟩

theorem canonicalMatch7_775 :
    canonicalPose7_775.boxKey 188160 (referenceBox7 (!canonicalBox7_775.bump)) = canonicalBox7_775 := by decide +kernel

theorem canonicalDecode7_775 : canonicalBox7_775.toKeyData 188160 = keys7Chunk24.get ⟨7, by decide⟩ := by
  change canonicalBox7_775.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (19 / 28), (5 / 14), 0, (11 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (1 / 336), (41 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_775 : keySolid (keys7Chunk24.get ⟨7, by decide⟩) = canonicalPose7_775.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_775 (box := canonicalBox7_775) (k := keys7Chunk24.get ⟨7, by decide⟩) (canonicalMatch7_775) (canonicalDecode7_775)

def canonicalPose7_776 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, true, true, true, false], ![2, 2, 0, 1, 0, 1, 0]⟩
def canonicalBox7_776 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 73920, 0, 67200, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 73472, -560, 66780, 128080], true⟩

theorem canonicalMatch7_776 :
    canonicalPose7_776.boxKey 188160 (referenceBox7 (!canonicalBox7_776.bump)) = canonicalBox7_776 := by decide +kernel

theorem canonicalDecode7_776 : canonicalBox7_776.toKeyData 188160 = keys7Chunk24.get ⟨8, by decide⟩ := by
  change canonicalBox7_776.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (11 / 28), 0, (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (-1 / 336), (159 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_776 : keySolid (keys7Chunk24.get ⟨8, by decide⟩) = canonicalPose7_776.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_776 (box := canonicalBox7_776) (k := keys7Chunk24.get ⟨8, by decide⟩) (canonicalMatch7_776) (canonicalDecode7_776)

def canonicalPose7_777 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, false, false, true, false], ![1, 1, 0, 0, 0, 0, 0]⟩
def canonicalBox7_777 : BoxKey 7 :=
  ⟨![315840, 322560, 100800, 107520, 114240, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 322945, 101360, 108010, 114688, -560, 121380], true⟩

theorem canonicalMatch7_777 :
    canonicalPose7_777.boxKey 188160 (referenceBox7 (!canonicalBox7_777.bump)) = canonicalBox7_777 := by decide +kernel

theorem canonicalDecode7_777 : canonicalBox7_777.toKeyData 188160 = keys7Chunk24.get ⟨9, by decide⟩ := by
  change canonicalBox7_777.toKeyData 188160 = ⟨![(47 / 28), (12 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_777 : keySolid (keys7Chunk24.get ⟨9, by decide⟩) = canonicalPose7_777.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_777 (box := canonicalBox7_777) (k := keys7Chunk24.get ⟨9, by decide⟩) (canonicalMatch7_777) (canonicalDecode7_777)

def canonicalPose7_778 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, false, true, false, true], ![2, 2, 0, 0, 1, 0, 0]⟩
def canonicalBox7_778 : BoxKey 7 :=
  ⟨![262080, 268800, 100800, 134400, 60480, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 101360, 134785, 60080, 121380, -560], true⟩

theorem canonicalMatch7_778 :
    canonicalPose7_778.boxKey 188160 (referenceBox7 (!canonicalBox7_778.bump)) = canonicalBox7_778 := by decide +kernel

theorem canonicalDecode7_778 : canonicalBox7_778.toKeyData 188160 = keys7Chunk24.get ⟨10, by decide⟩ := by
  change canonicalBox7_778.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (15 / 28), (5 / 7), (9 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_778 : keySolid (keys7Chunk24.get ⟨10, by decide⟩) = canonicalPose7_778.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_778 (box := canonicalBox7_778) (k := keys7Chunk24.get ⟨10, by decide⟩) (canonicalMatch7_778) (canonicalDecode7_778)

def canonicalPose7_779 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, false, false, false, false], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_779 : BoxKey 7 :=
  ⟨![376320, 302400, 107520, 100800, 134400, 127680, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 302848, 108010, 101360, 134785, 128080, 309540], true⟩

theorem canonicalMatch7_779 :
    canonicalPose7_779.boxKey 188160 (referenceBox7 (!canonicalBox7_779.bump)) = canonicalBox7_779 := by decide +kernel

theorem canonicalDecode7_779 : canonicalBox7_779.toKeyData 188160 = keys7Chunk24.get ⟨11, by decide⟩ := by
  change canonicalBox7_779.toKeyData 188160 = ⟨![2, (45 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_779 : keySolid (keys7Chunk24.get ⟨11, by decide⟩) = canonicalPose7_779.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_779 (box := canonicalBox7_779) (k := keys7Chunk24.get ⟨11, by decide⟩) (canonicalMatch7_779) (canonicalDecode7_779)

def canonicalPose7_780 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, false, false, false, false], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_780 : BoxKey 7 :=
  ⟨![376320, 309120, 127680, 134400, 100800, 107520, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 309540, 128080, 134785, 101360, 108010, 302848], false⟩

theorem canonicalMatch7_780 :
    canonicalPose7_780.boxKey 188160 (referenceBox7 (!canonicalBox7_780.bump)) = canonicalBox7_780 := by decide +kernel

theorem canonicalDecode7_780 : canonicalBox7_780.toKeyData 188160 = keys7Chunk24.get ⟨12, by decide⟩ := by
  change canonicalBox7_780.toKeyData 188160 = ⟨![2, (23 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_780 : keySolid (keys7Chunk24.get ⟨12, by decide⟩) = canonicalPose7_780.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_780 (box := canonicalBox7_780) (k := keys7Chunk24.get ⟨12, by decide⟩) (canonicalMatch7_780) (canonicalDecode7_780)

def canonicalPose7_781 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, false, true, true, false, true], ![2, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_781 : BoxKey 7 :=
  ⟨![262080, 376320, 120960, 60480, 53760, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 375760, 121380, 60080, 53375, 101360, 268310], false⟩

theorem canonicalMatch7_781 :
    canonicalPose7_781.boxKey 188160 (referenceBox7 (!canonicalBox7_781.bump)) = canonicalBox7_781 := by decide +kernel

theorem canonicalDecode7_781 : canonicalBox7_781.toKeyData 188160 = keys7Chunk24.get ⟨13, by decide⟩ := by
  change canonicalBox7_781.toKeyData 188160 = ⟨![(39 / 28), 2, (9 / 14), (9 / 28), (2 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (671 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_781 : keySolid (keys7Chunk24.get ⟨13, by decide⟩) = canonicalPose7_781.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_781 (box := canonicalBox7_781) (k := keys7Chunk24.get ⟨13, by decide⟩) (canonicalMatch7_781) (canonicalDecode7_781)

def canonicalPose7_782 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, false, false, false, false, true], ![1, 2, 0, 0, 0, 0, 2]⟩
def canonicalBox7_782 : BoxKey 7 :=
  ⟨![315840, 255360, 0, 114240, 107520, 100800, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 254940, 560, 114688, 108010, 101360, 241535], false⟩

theorem canonicalMatch7_782 :
    canonicalPose7_782.boxKey 188160 (referenceBox7 (!canonicalBox7_782.bump)) = canonicalBox7_782 := by decide +kernel

theorem canonicalDecode7_782 : canonicalBox7_782.toKeyData 188160 = keys7Chunk24.get ⟨14, by decide⟩ := by
  change canonicalBox7_782.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_782 : keySolid (keys7Chunk24.get ⟨14, by decide⟩) = canonicalPose7_782.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_782 (box := canonicalBox7_782) (k := keys7Chunk24.get ⟨14, by decide⟩) (canonicalMatch7_782) (canonicalDecode7_782)

def canonicalPose7_783 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, false, false, true, false, false, false], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_783 : BoxKey 7 :=
  ⟨![248640, 309120, 114240, 0, 107520, 100800, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 309540, 114688, -560, 108010, 101360, 322945], true⟩

theorem canonicalMatch7_783 :
    canonicalPose7_783.boxKey 188160 (referenceBox7 (!canonicalBox7_783.bump)) = canonicalBox7_783 := by decide +kernel

theorem canonicalDecode7_783 : canonicalBox7_783.toKeyData 188160 = keys7Chunk24.get ⟨15, by decide⟩ := by
  change canonicalBox7_783.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), (17 / 28), 0, (4 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (64 / 105), (-1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_783 : keySolid (keys7Chunk24.get ⟨15, by decide⟩) = canonicalPose7_783.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_783 (box := canonicalBox7_783) (k := keys7Chunk24.get ⟨15, by decide⟩) (canonicalMatch7_783) (canonicalDecode7_783)

def canonicalPose7_784 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, false, false, false, false, false, false], ![2, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_784 : BoxKey 7 :=
  ⟨![248640, 322560, 100800, 107520, 0, 114240, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 322945, 101360, 108010, 560, 114688, 309540], false⟩

theorem canonicalMatch7_784 :
    canonicalPose7_784.boxKey 188160 (referenceBox7 (!canonicalBox7_784.bump)) = canonicalBox7_784 := by decide +kernel

theorem canonicalDecode7_784 : canonicalBox7_784.toKeyData 188160 = keys7Chunk24.get ⟨16, by decide⟩ := by
  change canonicalBox7_784.toKeyData 188160 = ⟨![(37 / 28), (12 / 7), (15 / 28), (4 / 7), 0, (17 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (1 / 336), (64 / 105), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_784 : keySolid (keys7Chunk24.get ⟨16, by decide⟩) = canonicalPose7_784.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_784 (box := canonicalBox7_784) (k := keys7Chunk24.get ⟨16, by decide⟩) (canonicalMatch7_784) (canonicalDecode7_784)

def canonicalPose7_785 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, false, false, false, true, true], ![1, 2, 0, 0, 0, 0, 2]⟩
def canonicalBox7_785 : BoxKey 7 :=
  ⟨![315840, 241920, 100800, 107520, 114240, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 241535, 101360, 108010, 114688, -560, 254940], true⟩

theorem canonicalMatch7_785 :
    canonicalPose7_785.boxKey 188160 (referenceBox7 (!canonicalBox7_785.bump)) = canonicalBox7_785 := by decide +kernel

theorem canonicalDecode7_785 : canonicalBox7_785.toKeyData 188160 = keys7Chunk24.get ⟨17, by decide⟩ := by
  change canonicalBox7_785.toKeyData 188160 = ⟨![(47 / 28), (9 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_785 : keySolid (keys7Chunk24.get ⟨17, by decide⟩) = canonicalPose7_785.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_785 (box := canonicalBox7_785) (k := keys7Chunk24.get ⟨17, by decide⟩) (canonicalMatch7_785) (canonicalDecode7_785)

def canonicalPose7_786 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, true, true, false, false], ![2, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_786 : BoxKey 7 :=
  ⟨![262080, 268800, 100800, 53760, 60480, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 101360, 53375, 60080, 121380, 376880], true⟩

theorem canonicalMatch7_786 :
    canonicalPose7_786.boxKey 188160 (referenceBox7 (!canonicalBox7_786.bump)) = canonicalBox7_786 := by decide +kernel

theorem canonicalDecode7_786 : canonicalBox7_786.toKeyData 188160 = keys7Chunk24.get ⟨18, by decide⟩ := by
  change canonicalBox7_786.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_786 : keySolid (keys7Chunk24.get ⟨18, by decide⟩) = canonicalPose7_786.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_786 (box := canonicalBox7_786) (k := keys7Chunk24.get ⟨18, by decide⟩) (canonicalMatch7_786) (canonicalDecode7_786)

def canonicalPose7_787 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, true, false, false, true, false], ![2, 2, 1, 0, 0, 2, 0]⟩
def canonicalBox7_787 : BoxKey 7 :=
  ⟨![376320, 255360, 60480, 134400, 100800, 268800, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 254940, 60080, 134785, 101360, 268310, 114688], true⟩

theorem canonicalMatch7_787 :
    canonicalPose7_787.boxKey 188160 (referenceBox7 (!canonicalBox7_787.bump)) = canonicalBox7_787 := by decide +kernel

theorem canonicalDecode7_787 : canonicalBox7_787.toKeyData 188160 = keys7Chunk24.get ⟨19, by decide⟩ := by
  change canonicalBox7_787.toKeyData 188160 = ⟨![2, (19 / 14), (9 / 28), (5 / 7), (15 / 28), (10 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (607 / 448), (751 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_787 : keySolid (keys7Chunk24.get ⟨19, by decide⟩) = canonicalPose7_787.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_787 (box := canonicalBox7_787) (k := keys7Chunk24.get ⟨19, by decide⟩) (canonicalMatch7_787) (canonicalDecode7_787)

def canonicalPose7_788 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, false, false, false, false, true], ![2, 2, 0, 0, 0, 1, 1]⟩
def canonicalBox7_788 : BoxKey 7 :=
  ⟨![255360, 376320, 114240, 107520, 100800, 322560, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 376880, 114688, 108010, 101360, 322945, 60080], true⟩

theorem canonicalMatch7_788 :
    canonicalPose7_788.boxKey 188160 (referenceBox7 (!canonicalBox7_788.bump)) = canonicalBox7_788 := by decide +kernel

theorem canonicalDecode7_788 : canonicalBox7_788.toKeyData 188160 = keys7Chunk24.get ⟨20, by decide⟩ := by
  change canonicalBox7_788.toKeyData 188160 = ⟨![(19 / 14), 2, (17 / 28), (4 / 7), (15 / 28), (12 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (673 / 336), (64 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_788 : keySolid (keys7Chunk24.get ⟨20, by decide⟩) = canonicalPose7_788.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_788 (box := canonicalBox7_788) (k := keys7Chunk24.get ⟨20, by decide⟩) (canonicalMatch7_788) (canonicalDecode7_788)

def canonicalPose7_789 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, true, false, true, false], ![2, 1, 0, 1, 0, 2, 0]⟩
def canonicalBox7_789 : BoxKey 7 :=
  ⟨![268800, 302400, 0, 67200, 127680, 241920, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 302848, 560, 66780, 128080, 241535, 101360], false⟩

theorem canonicalMatch7_789 :
    canonicalPose7_789.boxKey 188160 (referenceBox7 (!canonicalBox7_789.bump)) = canonicalBox7_789 := by decide +kernel

theorem canonicalDecode7_789 : canonicalBox7_789.toKeyData 188160 = keys7Chunk24.get ⟨21, by decide⟩ := by
  change canonicalBox7_789.toKeyData 188160 = ⟨![(10 / 7), (45 / 28), 0, (5 / 14), (19 / 28), (9 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (169 / 105), (1 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_789 : keySolid (keys7Chunk24.get ⟨21, by decide⟩) = canonicalPose7_789.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_789 (box := canonicalBox7_789) (k := keys7Chunk24.get ⟨21, by decide⟩) (canonicalMatch7_789) (canonicalDecode7_789)

def canonicalPose7_790 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, true, true, false, true, false], ![2, 1, 0, 1, 0, 2, 0]⟩
def canonicalBox7_790 : BoxKey 7 :=
  ⟨![248640, 309120, 0, 73920, 107520, 275520, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 309540, -560, 73472, 108010, 274960, 134785], true⟩

theorem canonicalMatch7_790 :
    canonicalPose7_790.boxKey 188160 (referenceBox7 (!canonicalBox7_790.bump)) = canonicalBox7_790 := by decide +kernel

theorem canonicalDecode7_790 : canonicalBox7_790.toKeyData 188160 = keys7Chunk24.get ⟨22, by decide⟩ := by
  change canonicalBox7_790.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), 0, (11 / 28), (4 / 7), (41 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (-1 / 336), (41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_790 : keySolid (keys7Chunk24.get ⟨22, by decide⟩) = canonicalPose7_790.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_790 (box := canonicalBox7_790) (k := keys7Chunk24.get ⟨22, by decide⟩) (canonicalMatch7_790) (canonicalDecode7_790)

def canonicalPose7_791 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, false, false, false, false, true], ![2, 2, 0, 0, 0, 1, 1]⟩
def canonicalBox7_791 : BoxKey 7 :=
  ⟨![275520, 268800, 114240, 0, 120960, 315840, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 114688, 560, 121380, 316240, 53375], false⟩

theorem canonicalMatch7_791 :
    canonicalPose7_791.boxKey 188160 (referenceBox7 (!canonicalBox7_791.bump)) = canonicalBox7_791 := by decide +kernel

theorem canonicalDecode7_791 : canonicalBox7_791.toKeyData 188160 = keys7Chunk24.get ⟨23, by decide⟩ := by
  change canonicalBox7_791.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (17 / 28), 0, (9 / 14), (47 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (64 / 105), (1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_791 : keySolid (keys7Chunk24.get ⟨23, by decide⟩) = canonicalPose7_791.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_791 (box := canonicalBox7_791) (k := keys7Chunk24.get ⟨23, by decide⟩) (canonicalMatch7_791) (canonicalDecode7_791)

def canonicalPose7_792 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, false, false, true, false], ![2, 2, 1, 0, 0, 2, 0]⟩
def canonicalBox7_792 : BoxKey 7 :=
  ⟨![275520, 241920, 60480, 120960, 0, 262080, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 60080, 121380, 560, 261632, 108010], false⟩

theorem canonicalMatch7_792 :
    canonicalPose7_792.boxKey 188160 (referenceBox7 (!canonicalBox7_792.bump)) = canonicalBox7_792 := by decide +kernel

theorem canonicalDecode7_792 : canonicalBox7_792.toKeyData 188160 = keys7Chunk24.get ⟨24, by decide⟩ := by
  change canonicalBox7_792.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (9 / 28), (9 / 14), 0, (39 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (751 / 2352), (289 / 448), (1 / 336), (146 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_792 : keySolid (keys7Chunk24.get ⟨24, by decide⟩) = canonicalPose7_792.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_792 (box := canonicalBox7_792) (k := keys7Chunk24.get ⟨24, by decide⟩) (canonicalMatch7_792) (canonicalDecode7_792)

def canonicalPose7_793 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, false, false, true, false, false, false], ![2, 1, 0, 1, 0, 2, 0]⟩
def canonicalBox7_793 : BoxKey 7 :=
  ⟨![275520, 322560, 127680, 67200, 114240, 376320, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 322945, 128080, 66780, 114688, 376880, 108010], true⟩

theorem canonicalMatch7_793 :
    canonicalPose7_793.boxKey 188160 (referenceBox7 (!canonicalBox7_793.bump)) = canonicalBox7_793 := by decide +kernel

theorem canonicalDecode7_793 : canonicalBox7_793.toKeyData 188160 = keys7Chunk24.get ⟨25, by decide⟩ := by
  change canonicalBox7_793.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (19 / 28), (5 / 14), (17 / 28), 2, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (9227 / 5376), (1601 / 2352), (159 / 448), (64 / 105), (673 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_793 : keySolid (keys7Chunk24.get ⟨25, by decide⟩) = canonicalPose7_793.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_793 (box := canonicalBox7_793) (k := keys7Chunk24.get ⟨25, by decide⟩) (canonicalMatch7_793) (canonicalDecode7_793)

def canonicalPose7_794 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, false, false, true, false, true, false], ![2, 1, 0, 1, 0, 2, 0]⟩
def canonicalBox7_794 : BoxKey 7 :=
  ⟨![262080, 309120, 127680, 53760, 100800, 268800, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 309540, 128080, 53375, 101360, 268310, 560], false⟩

theorem canonicalMatch7_794 :
    canonicalPose7_794.boxKey 188160 (referenceBox7 (!canonicalBox7_794.bump)) = canonicalBox7_794 := by decide +kernel

theorem canonicalDecode7_794 : canonicalBox7_794.toKeyData 188160 = keys7Chunk24.get ⟨26, by decide⟩ := by
  change canonicalBox7_794.toKeyData 188160 = ⟨![(39 / 28), (23 / 14), (19 / 28), (2 / 7), (15 / 28), (10 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (737 / 448), (1601 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_794 : keySolid (keys7Chunk24.get ⟨26, by decide⟩) = canonicalPose7_794.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_794 (box := canonicalBox7_794) (k := keys7Chunk24.get ⟨26, by decide⟩) (canonicalMatch7_794) (canonicalDecode7_794)

def canonicalPose7_795 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, true, true, false, true, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_795 : BoxKey 7 :=
  ⟨![376320, 262080, 67200, 127680, 53760, 275520, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![376880, 261632, 66780, 128080, 53375, 274960, 268310], true⟩

theorem canonicalMatch7_795 :
    canonicalPose7_795.boxKey 188160 (referenceBox7 (!canonicalBox7_795.bump)) = canonicalBox7_795 := by decide +kernel

theorem canonicalDecode7_795 : canonicalBox7_795.toKeyData 188160 = keys7Chunk24.get ⟨27, by decide⟩ := by
  change canonicalBox7_795.toKeyData 188160 = ⟨![2, (39 / 28), (5 / 14), (19 / 28), (2 / 7), (41 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(673 / 336), (146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_795 : keySolid (keys7Chunk24.get ⟨27, by decide⟩) = canonicalPose7_795.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_795 (box := canonicalBox7_795) (k := keys7Chunk24.get ⟨27, by decide⟩) (canonicalMatch7_795) (canonicalDecode7_795)

def canonicalPose7_796 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, false, true, false, true, true], ![2, 2, 0, 1, 0, 2, 2]⟩
def canonicalBox7_796 : BoxKey 7 :=
  ⟨![262080, 376320, 120960, 60480, 134400, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 375760, 121380, 60080, 134785, 274960, 268310], false⟩

theorem canonicalMatch7_796 :
    canonicalPose7_796.boxKey 188160 (referenceBox7 (!canonicalBox7_796.bump)) = canonicalBox7_796 := by decide +kernel

theorem canonicalDecode7_796 : canonicalBox7_796.toKeyData 188160 = keys7Chunk24.get ⟨28, by decide⟩ := by
  change canonicalBox7_796.toKeyData 188160 = ⟨![(39 / 28), 2, (9 / 14), (9 / 28), (5 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (671 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_796 : keySolid (keys7Chunk24.get ⟨28, by decide⟩) = canonicalPose7_796.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_796 (box := canonicalBox7_796) (k := keys7Chunk24.get ⟨28, by decide⟩) (canonicalMatch7_796) (canonicalDecode7_796)

def canonicalPose7_797 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, false, false, false, true, false], ![1, 2, 0, 0, 0, 2, 1]⟩
def canonicalBox7_797 : BoxKey 7 :=
  ⟨![315840, 255360, 0, 114240, 107520, 275520, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 254940, 560, 114688, 108010, 274960, 322945], false⟩

theorem canonicalMatch7_797 :
    canonicalPose7_797.boxKey 188160 (referenceBox7 (!canonicalBox7_797.bump)) = canonicalBox7_797 := by decide +kernel

theorem canonicalDecode7_797 : canonicalBox7_797.toKeyData 188160 = keys7Chunk24.get ⟨29, by decide⟩ := by
  change canonicalBox7_797.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (491 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_797 : keySolid (keys7Chunk24.get ⟨29, by decide⟩) = canonicalPose7_797.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_797 (box := canonicalBox7_797) (k := keys7Chunk24.get ⟨29, by decide⟩) (canonicalMatch7_797) (canonicalDecode7_797)

def canonicalPose7_798 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, true, true, true, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_798 : BoxKey 7 :=
  ⟨![275520, 268800, 73920, 0, 67200, 248640, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 73472, -560, 66780, 248240, 241535], true⟩

theorem canonicalMatch7_798 :
    canonicalPose7_798.boxKey 188160 (referenceBox7 (!canonicalBox7_798.bump)) = canonicalBox7_798 := by decide +kernel

theorem canonicalDecode7_798 : canonicalBox7_798.toKeyData 188160 = keys7Chunk24.get ⟨30, by decide⟩ := by
  change canonicalBox7_798.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (11 / 28), 0, (5 / 14), (37 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (41 / 105), (-1 / 336), (159 / 448), (3103 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_798 : keySolid (keys7Chunk24.get ⟨30, by decide⟩) = canonicalPose7_798.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_798 (box := canonicalBox7_798) (k := keys7Chunk24.get ⟨30, by decide⟩) (canonicalMatch7_798) (canonicalDecode7_798)

def canonicalPose7_799 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, false, true, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_799 : BoxKey 7 :=
  ⟨![241920, 248640, 67200, 0, 73920, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 248240, 66780, 560, 73472, 268310, 274960], false⟩

theorem canonicalMatch7_799 :
    canonicalPose7_799.boxKey 188160 (referenceBox7 (!canonicalBox7_799.bump)) = canonicalBox7_799 := by decide +kernel

theorem canonicalDecode7_799 : canonicalBox7_799.toKeyData 188160 = keys7Chunk24.get ⟨31, by decide⟩ := by
  change canonicalBox7_799.toKeyData 188160 = ⟨![(9 / 7), (37 / 28), (5 / 14), 0, (11 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (3103 / 2352), (159 / 448), (1 / 336), (41 / 105), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_799 : keySolid (keys7Chunk24.get ⟨31, by decide⟩) = canonicalPose7_799.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_799 (box := canonicalBox7_799) (k := keys7Chunk24.get ⟨31, by decide⟩) (canonicalMatch7_799) (canonicalDecode7_799)

theorem keys7Chunk24_canonical : ∀ k ∈ keys7Chunk24,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk24, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_768, canonicalSolid7_768⟩
  · exact ⟨canonicalPose7_769, canonicalSolid7_769⟩
  · exact ⟨canonicalPose7_770, canonicalSolid7_770⟩
  · exact ⟨canonicalPose7_771, canonicalSolid7_771⟩
  · exact ⟨canonicalPose7_772, canonicalSolid7_772⟩
  · exact ⟨canonicalPose7_773, canonicalSolid7_773⟩
  · exact ⟨canonicalPose7_774, canonicalSolid7_774⟩
  · exact ⟨canonicalPose7_775, canonicalSolid7_775⟩
  · exact ⟨canonicalPose7_776, canonicalSolid7_776⟩
  · exact ⟨canonicalPose7_777, canonicalSolid7_777⟩
  · exact ⟨canonicalPose7_778, canonicalSolid7_778⟩
  · exact ⟨canonicalPose7_779, canonicalSolid7_779⟩
  · exact ⟨canonicalPose7_780, canonicalSolid7_780⟩
  · exact ⟨canonicalPose7_781, canonicalSolid7_781⟩
  · exact ⟨canonicalPose7_782, canonicalSolid7_782⟩
  · exact ⟨canonicalPose7_783, canonicalSolid7_783⟩
  · exact ⟨canonicalPose7_784, canonicalSolid7_784⟩
  · exact ⟨canonicalPose7_785, canonicalSolid7_785⟩
  · exact ⟨canonicalPose7_786, canonicalSolid7_786⟩
  · exact ⟨canonicalPose7_787, canonicalSolid7_787⟩
  · exact ⟨canonicalPose7_788, canonicalSolid7_788⟩
  · exact ⟨canonicalPose7_789, canonicalSolid7_789⟩
  · exact ⟨canonicalPose7_790, canonicalSolid7_790⟩
  · exact ⟨canonicalPose7_791, canonicalSolid7_791⟩
  · exact ⟨canonicalPose7_792, canonicalSolid7_792⟩
  · exact ⟨canonicalPose7_793, canonicalSolid7_793⟩
  · exact ⟨canonicalPose7_794, canonicalSolid7_794⟩
  · exact ⟨canonicalPose7_795, canonicalSolid7_795⟩
  · exact ⟨canonicalPose7_796, canonicalSolid7_796⟩
  · exact ⟨canonicalPose7_797, canonicalSolid7_797⟩
  · exact ⟨canonicalPose7_798, canonicalSolid7_798⟩
  · exact ⟨canonicalPose7_799, canonicalSolid7_799⟩

#print axioms keys7Chunk24_canonical

end SparseMonotiles.Canonical
