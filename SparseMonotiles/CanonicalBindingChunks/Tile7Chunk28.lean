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

def canonicalPose7_896 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, false, false, true, false, false], ![2, 2, 0, 2, 2, 1, 1]⟩
def canonicalBox7_896 : BoxKey 7 :=
  ⟨![275520, 268800, 114240, 376320, 255360, 315840, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 114688, 376880, 254940, 316240, 322945], true⟩

theorem canonicalMatch7_896 :
    canonicalPose7_896.boxKey 188160 (referenceBox7 (!canonicalBox7_896.bump)) = canonicalBox7_896 := by decide +kernel

theorem canonicalDecode7_896 : canonicalBox7_896.toKeyData 188160 = keys7Chunk28.get ⟨0, by decide⟩ := by
  change canonicalBox7_896.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (47 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (3953 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_896 : keySolid (keys7Chunk28.get ⟨0, by decide⟩) = canonicalPose7_896.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_896 (box := canonicalBox7_896) (k := keys7Chunk28.get ⟨0, by decide⟩) (canonicalMatch7_896) (canonicalDecode7_896)

def canonicalPose7_897 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, false, true, true], ![2, 2, 1, 2, 2, 2, 2]⟩
def canonicalBox7_897 : BoxKey 7 :=
  ⟨![275520, 241920, 60480, 255360, 376320, 262080, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 60080, 254940, 376880, 261632, 268310], true⟩

theorem canonicalMatch7_897 :
    canonicalPose7_897.boxKey 188160 (referenceBox7 (!canonicalBox7_897.bump)) = canonicalBox7_897 := by decide +kernel

theorem canonicalDecode7_897 : canonicalBox7_897.toKeyData 188160 = keys7Chunk28.get ⟨1, by decide⟩ := by
  change canonicalBox7_897.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (9 / 28), (19 / 14), 2, (39 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (673 / 336), (146 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_897 : keySolid (keys7Chunk28.get ⟨1, by decide⟩) = canonicalPose7_897.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_897 (box := canonicalBox7_897) (k := keys7Chunk28.get ⟨1, by decide⟩) (canonicalMatch7_897) (canonicalDecode7_897)

def canonicalPose7_898 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, false, false, false, true, true, true], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_898 : BoxKey 7 :=
  ⟨![275520, 322560, 127680, 309120, 262080, 376320, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 322945, 128080, 309540, 261632, 375760, 268310], false⟩

theorem canonicalMatch7_898 :
    canonicalPose7_898.boxKey 188160 (referenceBox7 (!canonicalBox7_898.bump)) = canonicalBox7_898 := by decide +kernel

theorem canonicalDecode7_898 : canonicalBox7_898.toKeyData 188160 = keys7Chunk28.get ⟨2, by decide⟩ := by
  change canonicalBox7_898.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (19 / 28), (23 / 14), (39 / 28), 2, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (671 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_898 : keySolid (keys7Chunk28.get ⟨2, by decide⟩) = canonicalPose7_898.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_898 (box := canonicalBox7_898) (k := keys7Chunk28.get ⟨2, by decide⟩) (canonicalMatch7_898) (canonicalDecode7_898)

def canonicalPose7_899 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, false, false, false, true, true, false], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_899 : BoxKey 7 :=
  ⟨![262080, 309120, 127680, 322560, 275520, 268800, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 309540, 128080, 322945, 274960, 268310, 376880], true⟩

theorem canonicalMatch7_899 :
    canonicalPose7_899.boxKey 188160 (referenceBox7 (!canonicalBox7_899.bump)) = canonicalBox7_899 := by decide +kernel

theorem canonicalDecode7_899 : canonicalBox7_899.toKeyData 188160 = keys7Chunk28.get ⟨3, by decide⟩ := by
  change canonicalBox7_899.toKeyData 188160 = ⟨![(39 / 28), (23 / 14), (19 / 28), (12 / 7), (41 / 28), (10 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_899 : keySolid (keys7Chunk28.get ⟨3, by decide⟩) = canonicalPose7_899.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_899 (box := canonicalBox7_899) (k := keys7Chunk28.get ⟨3, by decide⟩) (canonicalMatch7_899) (canonicalDecode7_899)

def canonicalPose7_900 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, false, true, true, false], ![2, 2, 2, 0, 1, 1, 0]⟩
def canonicalBox7_900 : BoxKey 7 :=
  ⟨![376320, 262080, 268800, 100800, 53760, 60480, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 261632, 268310, 101360, 53375, 60080, 121380], true⟩

theorem canonicalMatch7_900 :
    canonicalPose7_900.boxKey 188160 (referenceBox7 (!canonicalBox7_900.bump)) = canonicalBox7_900 := by decide +kernel

theorem canonicalDecode7_900 : canonicalBox7_900.toKeyData 188160 = keys7Chunk28.get ⟨4, by decide⟩ := by
  change canonicalBox7_900.toKeyData 188160 = ⟨![2, (39 / 28), (10 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (146 / 105), (3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_900 : keySolid (keys7Chunk28.get ⟨4, by decide⟩) = canonicalPose7_900.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_900 (box := canonicalBox7_900) (k := keys7Chunk28.get ⟨4, by decide⟩) (canonicalMatch7_900) (canonicalDecode7_900)

def canonicalPose7_901 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, false, false, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_901 : BoxKey 7 :=
  ⟨![302400, 376320, 309120, 127680, 134400, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, 375760, 309540, 128080, 134785, 101360, 108010], false⟩

theorem canonicalMatch7_901 :
    canonicalPose7_901.boxKey 188160 (referenceBox7 (!canonicalBox7_901.bump)) = canonicalBox7_901 := by decide +kernel

theorem canonicalDecode7_901 : canonicalBox7_901.toKeyData 188160 = keys7Chunk28.get ⟨5, by decide⟩ := by
  change canonicalBox7_901.toKeyData 188160 = ⟨![(45 / 28), 2, (23 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (671 / 336), (737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_901 : keySolid (keys7Chunk28.get ⟨5, by decide⟩) = canonicalPose7_901.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_901 (box := canonicalBox7_901) (k := keys7Chunk28.get ⟨5, by decide⟩) (canonicalMatch7_901) (canonicalDecode7_901)

def canonicalPose7_902 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, false, false, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_902 : BoxKey 7 :=
  ⟨![309120, 376320, 302400, 107520, 100800, 134400, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 376880, 302848, 108010, 101360, 134785, 128080], true⟩

theorem canonicalMatch7_902 :
    canonicalPose7_902.boxKey 188160 (referenceBox7 (!canonicalBox7_902.bump)) = canonicalBox7_902 := by decide +kernel

theorem canonicalDecode7_902 : canonicalBox7_902.toKeyData 188160 = keys7Chunk28.get ⟨6, by decide⟩ := by
  change canonicalBox7_902.toKeyData 188160 = ⟨![(23 / 14), 2, (45 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (673 / 336), (169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_902 : keySolid (keys7Chunk28.get ⟨6, by decide⟩) = canonicalPose7_902.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_902 (box := canonicalBox7_902) (k := keys7Chunk28.get ⟨6, by decide⟩) (canonicalMatch7_902) (canonicalDecode7_902)

def canonicalPose7_903 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, false, true, true, false], ![2, 2, 2, 0, 1, 1, 0]⟩
def canonicalBox7_903 : BoxKey 7 :=
  ⟨![268800, 262080, 376320, 120960, 60480, 53760, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 375760, 121380, 60080, 53375, 101360], false⟩

theorem canonicalMatch7_903 :
    canonicalPose7_903.boxKey 188160 (referenceBox7 (!canonicalBox7_903.bump)) = canonicalBox7_903 := by decide +kernel

theorem canonicalDecode7_903 : canonicalBox7_903.toKeyData 188160 = keys7Chunk28.get ⟨7, by decide⟩ := by
  change canonicalBox7_903.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 2, (9 / 14), (9 / 28), (2 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_903 : keySolid (keys7Chunk28.get ⟨7, by decide⟩) = canonicalPose7_903.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_903 (box := canonicalBox7_903) (k := keys7Chunk28.get ⟨7, by decide⟩) (canonicalMatch7_903) (canonicalDecode7_903)

def canonicalPose7_904 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, true, false, false, false, false], ![2, 1, 2, 0, 0, 0, 0]⟩
def canonicalBox7_904 : BoxKey 7 :=
  ⟨![241920, 315840, 255360, 0, 114240, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 316240, 254940, 560, 114688, 108010, 101360], false⟩

theorem canonicalMatch7_904 :
    canonicalPose7_904.boxKey 188160 (referenceBox7 (!canonicalBox7_904.bump)) = canonicalBox7_904 := by decide +kernel

theorem canonicalDecode7_904 : canonicalBox7_904.toKeyData 188160 = keys7Chunk28.get ⟨8, by decide⟩ := by
  change canonicalBox7_904.toKeyData 188160 = ⟨![(9 / 7), (47 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_904 : keySolid (keys7Chunk28.get ⟨8, by decide⟩) = canonicalPose7_904.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_904 (box := canonicalBox7_904) (k := keys7Chunk28.get ⟨8, by decide⟩) (canonicalMatch7_904) (canonicalDecode7_904)

def canonicalPose7_905 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, true, false, false, true, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_905 : BoxKey 7 :=
  ⟨![322560, 248640, 309120, 114240, 0, 107520, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 248240, 309540, 114688, -560, 108010, 101360], true⟩

theorem canonicalMatch7_905 :
    canonicalPose7_905.boxKey 188160 (referenceBox7 (!canonicalBox7_905.bump)) = canonicalBox7_905 := by decide +kernel

theorem canonicalDecode7_905 : canonicalBox7_905.toKeyData 188160 = keys7Chunk28.get ⟨9, by decide⟩ := by
  change canonicalBox7_905.toKeyData 188160 = ⟨![(12 / 7), (37 / 28), (23 / 14), (17 / 28), 0, (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105), (-1 / 336), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_905 : keySolid (keys7Chunk28.get ⟨9, by decide⟩) = canonicalPose7_905.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_905 (box := canonicalBox7_905) (k := keys7Chunk28.get ⟨9, by decide⟩) (canonicalMatch7_905) (canonicalDecode7_905)

def canonicalPose7_906 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, true, false, false, false, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_906 : BoxKey 7 :=
  ⟨![309120, 248640, 322560, 100800, 107520, 0, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 248240, 322945, 101360, 108010, 560, 114688], false⟩

theorem canonicalMatch7_906 :
    canonicalPose7_906.boxKey 188160 (referenceBox7 (!canonicalBox7_906.bump)) = canonicalBox7_906 := by decide +kernel

theorem canonicalDecode7_906 : canonicalBox7_906.toKeyData 188160 = keys7Chunk28.get ⟨10, by decide⟩ := by
  change canonicalBox7_906.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (12 / 7), (15 / 28), (4 / 7), 0, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (1 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_906 : keySolid (keys7Chunk28.get ⟨10, by decide⟩) = canonicalPose7_906.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_906 (box := canonicalBox7_906) (k := keys7Chunk28.get ⟨10, by decide⟩) (canonicalMatch7_906) (canonicalDecode7_906)

def canonicalPose7_907 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, true, false, false, false, true], ![2, 1, 2, 0, 0, 0, 0]⟩
def canonicalBox7_907 : BoxKey 7 :=
  ⟨![255360, 315840, 241920, 100800, 107520, 114240, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 316240, 241535, 101360, 108010, 114688, -560], true⟩

theorem canonicalMatch7_907 :
    canonicalPose7_907.boxKey 188160 (referenceBox7 (!canonicalBox7_907.bump)) = canonicalBox7_907 := by decide +kernel

theorem canonicalDecode7_907 : canonicalBox7_907.toKeyData 188160 = keys7Chunk28.get ⟨11, by decide⟩ := by
  change canonicalBox7_907.toKeyData 188160 = ⟨![(19 / 14), (47 / 28), (9 / 7), (15 / 28), (4 / 7), (17 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_907 : keySolid (keys7Chunk28.get ⟨11, by decide⟩) = canonicalPose7_907.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_907 (box := canonicalBox7_907) (k := keys7Chunk28.get ⟨11, by decide⟩) (canonicalMatch7_907) (canonicalDecode7_907)

def canonicalPose7_908 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, true, true, true, false, true, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_908 : BoxKey 7 :=
  ⟨![376320, 268800, 275520, 53760, 127680, 67200, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![375760, 268310, 274960, 53375, 128080, 66780, 261632], false⟩

theorem canonicalMatch7_908 :
    canonicalPose7_908.boxKey 188160 (referenceBox7 (!canonicalBox7_908.bump)) = canonicalBox7_908 := by decide +kernel

theorem canonicalDecode7_908 : canonicalBox7_908.toKeyData 188160 = keys7Chunk28.get ⟨12, by decide⟩ := by
  change canonicalBox7_908.toKeyData 188160 = ⟨![2, (10 / 7), (41 / 28), (2 / 7), (19 / 28), (5 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(671 / 336), (3833 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_908 : keySolid (keys7Chunk28.get ⟨12, by decide⟩) = canonicalPose7_908.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_908 (box := canonicalBox7_908) (k := keys7Chunk28.get ⟨12, by decide⟩) (canonicalMatch7_908) (canonicalDecode7_908)

def canonicalPose7_909 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, false, true, true, false, true, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_909 : BoxKey 7 :=
  ⟨![268800, 376320, 262080, 67200, 127680, 53760, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 376880, 261632, 66780, 128080, 53375, 274960], true⟩

theorem canonicalMatch7_909 :
    canonicalPose7_909.boxKey 188160 (referenceBox7 (!canonicalBox7_909.bump)) = canonicalBox7_909 := by decide +kernel

theorem canonicalDecode7_909 : canonicalBox7_909.toKeyData 188160 = keys7Chunk28.get ⟨13, by decide⟩ := by
  change canonicalBox7_909.toKeyData 188160 = ⟨![(10 / 7), 2, (39 / 28), (5 / 14), (19 / 28), (2 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (673 / 336), (146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_909 : keySolid (keys7Chunk28.get ⟨13, by decide⟩) = canonicalPose7_909.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_909 (box := canonicalBox7_909) (k := keys7Chunk28.get ⟨13, by decide⟩) (canonicalMatch7_909) (canonicalDecode7_909)

def canonicalPose7_910 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, false, true, false, true], ![2, 2, 2, 0, 1, 0, 2]⟩
def canonicalBox7_910 : BoxKey 7 :=
  ⟨![268800, 262080, 376320, 120960, 60480, 134400, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 375760, 121380, 60080, 134785, 274960], false⟩

theorem canonicalMatch7_910 :
    canonicalPose7_910.boxKey 188160 (referenceBox7 (!canonicalBox7_910.bump)) = canonicalBox7_910 := by decide +kernel

theorem canonicalDecode7_910 : canonicalBox7_910.toKeyData 188160 = keys7Chunk28.get ⟨14, by decide⟩ := by
  change canonicalBox7_910.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 2, (9 / 14), (9 / 28), (5 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_910 : keySolid (keys7Chunk28.get ⟨14, by decide⟩) = canonicalPose7_910.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_910 (box := canonicalBox7_910) (k := keys7Chunk28.get ⟨14, by decide⟩) (canonicalMatch7_910) (canonicalDecode7_910)

def canonicalPose7_911 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, true, false, false, false, true], ![1, 1, 2, 0, 0, 0, 2]⟩
def canonicalBox7_911 : BoxKey 7 :=
  ⟨![322560, 315840, 255360, 0, 114240, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 316240, 254940, 560, 114688, 108010, 274960], false⟩

theorem canonicalMatch7_911 :
    canonicalPose7_911.boxKey 188160 (referenceBox7 (!canonicalBox7_911.bump)) = canonicalBox7_911 := by decide +kernel

theorem canonicalDecode7_911 : canonicalBox7_911.toKeyData 188160 = keys7Chunk28.get ⟨15, by decide⟩ := by
  change canonicalBox7_911.toKeyData 188160 = ⟨![(12 / 7), (47 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_911 : keySolid (keys7Chunk28.get ⟨15, by decide⟩) = canonicalPose7_911.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_911 (box := canonicalBox7_911) (k := keys7Chunk28.get ⟨15, by decide⟩) (canonicalMatch7_911) (canonicalDecode7_911)

def canonicalPose7_912 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, false, true, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_912 : BoxKey 7 :=
  ⟨![275520, 241920, 248640, 67200, 0, 73920, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 248240, 66780, 560, 73472, 268310], false⟩

theorem canonicalMatch7_912 :
    canonicalPose7_912.boxKey 188160 (referenceBox7 (!canonicalBox7_912.bump)) = canonicalBox7_912 := by decide +kernel

theorem canonicalDecode7_912 : canonicalBox7_912.toKeyData 188160 = keys7Chunk28.get ⟨16, by decide⟩ := by
  change canonicalBox7_912.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (37 / 28), (5 / 14), 0, (11 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448), (1 / 336), (41 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_912 : keySolid (keys7Chunk28.get ⟨16, by decide⟩) = canonicalPose7_912.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_912 (box := canonicalBox7_912) (k := keys7Chunk28.get ⟨16, by decide⟩) (canonicalMatch7_912) (canonicalDecode7_912)

def canonicalPose7_913 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, true, true, true, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_913 : BoxKey 7 :=
  ⟨![241920, 275520, 268800, 73920, 0, 67200, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 268310, 73472, -560, 66780, 248240], true⟩

theorem canonicalMatch7_913 :
    canonicalPose7_913.boxKey 188160 (referenceBox7 (!canonicalBox7_913.bump)) = canonicalBox7_913 := by decide +kernel

theorem canonicalDecode7_913 : canonicalBox7_913.toKeyData 188160 = keys7Chunk28.get ⟨17, by decide⟩ := by
  change canonicalBox7_913.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (10 / 7), (11 / 28), 0, (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105), (-1 / 336), (159 / 448), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_913 : keySolid (keys7Chunk28.get ⟨17, by decide⟩) = canonicalPose7_913.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_913 (box := canonicalBox7_913) (k := keys7Chunk28.get ⟨17, by decide⟩) (canonicalMatch7_913) (canonicalDecode7_913)

def canonicalPose7_914 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, true, false, false, true, true], ![1, 1, 2, 0, 0, 0, 2]⟩
def canonicalBox7_914 : BoxKey 7 :=
  ⟨![315840, 322560, 275520, 107520, 114240, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 322945, 274960, 108010, 114688, -560, 254940], true⟩

theorem canonicalMatch7_914 :
    canonicalPose7_914.boxKey 188160 (referenceBox7 (!canonicalBox7_914.bump)) = canonicalBox7_914 := by decide +kernel

theorem canonicalDecode7_914 : canonicalBox7_914.toKeyData 188160 = keys7Chunk28.get ⟨18, by decide⟩ := by
  change canonicalBox7_914.toKeyData 188160 = ⟨![(47 / 28), (12 / 7), (41 / 28), (4 / 7), (17 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_914 : keySolid (keys7Chunk28.get ⟨18, by decide⟩) = canonicalPose7_914.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_914 (box := canonicalBox7_914) (k := keys7Chunk28.get ⟨18, by decide⟩) (canonicalMatch7_914) (canonicalDecode7_914)

def canonicalPose7_915 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, true, false, true, false, false], ![2, 2, 2, 0, 1, 0, 2]⟩
def canonicalBox7_915 : BoxKey 7 :=
  ⟨![262080, 268800, 275520, 134400, 60480, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 274960, 134785, 60080, 121380, 376880], true⟩

theorem canonicalMatch7_915 :
    canonicalPose7_915.boxKey 188160 (referenceBox7 (!canonicalBox7_915.bump)) = canonicalBox7_915 := by decide +kernel

theorem canonicalDecode7_915 : canonicalBox7_915.toKeyData 188160 = keys7Chunk28.get ⟨19, by decide⟩ := by
  change canonicalBox7_915.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (41 / 28), (5 / 7), (9 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_915 : keySolid (keys7Chunk28.get ⟨19, by decide⟩) = canonicalPose7_915.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_915 (box := canonicalBox7_915) (k := keys7Chunk28.get ⟨19, by decide⟩) (canonicalMatch7_915) (canonicalDecode7_915)

def canonicalPose7_916 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, false, false, false, true, false], ![2, 2, 1, 0, 0, 2, 0]⟩
def canonicalBox7_916 : BoxKey 7 :=
  ⟨![376320, 255360, 315840, 134400, 100800, 268800, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 254940, 316240, 134785, 101360, 268310, 114688], false⟩

theorem canonicalMatch7_916 :
    canonicalPose7_916.boxKey 188160 (referenceBox7 (!canonicalBox7_916.bump)) = canonicalBox7_916 := by decide +kernel

theorem canonicalDecode7_916 : canonicalBox7_916.toKeyData 188160 = keys7Chunk28.get ⟨20, by decide⟩ := by
  change canonicalBox7_916.toKeyData 188160 = ⟨![2, (19 / 14), (47 / 28), (5 / 7), (15 / 28), (10 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (607 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_916 : keySolid (keys7Chunk28.get ⟨20, by decide⟩) = canonicalPose7_916.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_916 (box := canonicalBox7_916) (k := keys7Chunk28.get ⟨20, by decide⟩) (canonicalMatch7_916) (canonicalDecode7_916)

def canonicalPose7_917 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, true, false, false, false, true], ![2, 2, 2, 0, 0, 1, 1]⟩
def canonicalBox7_917 : BoxKey 7 :=
  ⟨![255360, 376320, 262080, 107520, 100800, 322560, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 375760, 261632, 108010, 101360, 322945, 60080], false⟩

theorem canonicalMatch7_917 :
    canonicalPose7_917.boxKey 188160 (referenceBox7 (!canonicalBox7_917.bump)) = canonicalBox7_917 := by decide +kernel

theorem canonicalDecode7_917 : canonicalBox7_917.toKeyData 188160 = keys7Chunk28.get ⟨21, by decide⟩ := by
  change canonicalBox7_917.toKeyData 188160 = ⟨![(19 / 14), 2, (39 / 28), (4 / 7), (15 / 28), (12 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (671 / 336), (146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_917 : keySolid (keys7Chunk28.get ⟨21, by decide⟩) = canonicalPose7_917.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_917 (box := canonicalBox7_917) (k := keys7Chunk28.get ⟨21, by decide⟩) (canonicalMatch7_917) (canonicalDecode7_917)

def canonicalPose7_918 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, true, false, true, false], ![2, 1, 2, 1, 0, 2, 0]⟩
def canonicalBox7_918 : BoxKey 7 :=
  ⟨![268800, 302400, 376320, 67200, 127680, 241920, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 302848, 376880, 66780, 128080, 241535, 101360], true⟩

theorem canonicalMatch7_918 :
    canonicalPose7_918.boxKey 188160 (referenceBox7 (!canonicalBox7_918.bump)) = canonicalBox7_918 := by decide +kernel

theorem canonicalDecode7_918 : canonicalBox7_918.toKeyData 188160 = keys7Chunk28.get ⟨22, by decide⟩ := by
  change canonicalBox7_918.toKeyData 188160 = ⟨![(10 / 7), (45 / 28), 2, (5 / 14), (19 / 28), (9 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (169 / 105), (673 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_918 : keySolid (keys7Chunk28.get ⟨22, by decide⟩) = canonicalPose7_918.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_918 (box := canonicalBox7_918) (k := keys7Chunk28.get ⟨22, by decide⟩) (canonicalMatch7_918) (canonicalDecode7_918)

def canonicalPose7_919 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, true, true, false, true, false], ![2, 1, 2, 1, 0, 2, 0]⟩
def canonicalBox7_919 : BoxKey 7 :=
  ⟨![248640, 309120, 376320, 73920, 107520, 275520, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 309540, 375760, 73472, 108010, 274960, 134785], false⟩

theorem canonicalMatch7_919 :
    canonicalPose7_919.boxKey 188160 (referenceBox7 (!canonicalBox7_919.bump)) = canonicalBox7_919 := by decide +kernel

theorem canonicalDecode7_919 : canonicalBox7_919.toKeyData 188160 = keys7Chunk28.get ⟨23, by decide⟩ := by
  change canonicalBox7_919.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), 2, (11 / 28), (4 / 7), (41 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (671 / 336), (41 / 105), (1543 / 2688), (491 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_919 : keySolid (keys7Chunk28.get ⟨23, by decide⟩) = canonicalPose7_919.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_919 (box := canonicalBox7_919) (k := keys7Chunk28.get ⟨23, by decide⟩) (canonicalMatch7_919) (canonicalDecode7_919)

def canonicalPose7_920 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, true, true, false, false, true], ![2, 2, 2, 0, 0, 1, 1]⟩
def canonicalBox7_920 : BoxKey 7 :=
  ⟨![275520, 268800, 262080, 0, 120960, 315840, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 261632, -560, 121380, 316240, 53375], true⟩

theorem canonicalMatch7_920 :
    canonicalPose7_920.boxKey 188160 (referenceBox7 (!canonicalBox7_920.bump)) = canonicalBox7_920 := by decide +kernel

theorem canonicalDecode7_920 : canonicalBox7_920.toKeyData 188160 = keys7Chunk28.get ⟨24, by decide⟩ := by
  change canonicalBox7_920.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (289 / 448), (3953 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_920 : keySolid (keys7Chunk28.get ⟨24, by decide⟩) = canonicalPose7_920.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_920 (box := canonicalBox7_920) (k := keys7Chunk28.get ⟨24, by decide⟩) (canonicalMatch7_920) (canonicalDecode7_920)

def canonicalPose7_921 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, false, true, true, false], ![2, 2, 1, 0, 0, 2, 0]⟩
def canonicalBox7_921 : BoxKey 7 :=
  ⟨![275520, 241920, 315840, 120960, 0, 262080, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 316240, 121380, -560, 261632, 108010], true⟩

theorem canonicalMatch7_921 :
    canonicalPose7_921.boxKey 188160 (referenceBox7 (!canonicalBox7_921.bump)) = canonicalBox7_921 := by decide +kernel

theorem canonicalDecode7_921 : canonicalBox7_921.toKeyData 188160 = keys7Chunk28.get ⟨25, by decide⟩ := by
  change canonicalBox7_921.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (146 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_921 : keySolid (keys7Chunk28.get ⟨25, by decide⟩) = canonicalPose7_921.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_921 (box := canonicalBox7_921) (k := keys7Chunk28.get ⟨25, by decide⟩) (canonicalMatch7_921) (canonicalDecode7_921)

def canonicalPose7_922 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, false, true, true, false, true, false], ![2, 1, 2, 1, 0, 2, 0]⟩
def canonicalBox7_922 : BoxKey 7 :=
  ⟨![275520, 322560, 248640, 67200, 114240, 376320, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 322945, 248240, 66780, 114688, 375760, 108010], false⟩

theorem canonicalMatch7_922 :
    canonicalPose7_922.boxKey 188160 (referenceBox7 (!canonicalBox7_922.bump)) = canonicalBox7_922 := by decide +kernel

theorem canonicalDecode7_922 : canonicalBox7_922.toKeyData 188160 = keys7Chunk28.get ⟨26, by decide⟩ := by
  change canonicalBox7_922.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (37 / 28), (5 / 14), (17 / 28), 2, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (9227 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (671 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_922 : keySolid (keys7Chunk28.get ⟨26, by decide⟩) = canonicalPose7_922.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_922 (box := canonicalBox7_922) (k := keys7Chunk28.get ⟨26, by decide⟩) (canonicalMatch7_922) (canonicalDecode7_922)

def canonicalPose7_923 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, false, true, true, false, true, true], ![2, 1, 2, 1, 0, 2, 0]⟩
def canonicalBox7_923 : BoxKey 7 :=
  ⟨![262080, 309120, 248640, 53760, 100800, 268800, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 309540, 248240, 53375, 101360, 268310, -560], true⟩

theorem canonicalMatch7_923 :
    canonicalPose7_923.boxKey 188160 (referenceBox7 (!canonicalBox7_923.bump)) = canonicalBox7_923 := by decide +kernel

theorem canonicalDecode7_923 : canonicalBox7_923.toKeyData 188160 = keys7Chunk28.get ⟨27, by decide⟩ := by
  change canonicalBox7_923.toKeyData 188160 = ⟨![(39 / 28), (23 / 14), (37 / 28), (2 / 7), (15 / 28), (10 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (737 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_923 : keySolid (keys7Chunk28.get ⟨27, by decide⟩) = canonicalPose7_923.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_923 (box := canonicalBox7_923) (k := keys7Chunk28.get ⟨27, by decide⟩) (canonicalMatch7_923) (canonicalDecode7_923)

def canonicalPose7_924 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, true, false, false, true, false], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_924 : BoxKey 7 :=
  ⟨![376320, 302400, 268800, 100800, 134400, 248640, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 302848, 268310, 101360, 134785, 248240, 309540], true⟩

theorem canonicalMatch7_924 :
    canonicalPose7_924.boxKey 188160 (referenceBox7 (!canonicalBox7_924.bump)) = canonicalBox7_924 := by decide +kernel

theorem canonicalDecode7_924 : canonicalBox7_924.toKeyData 188160 = keys7Chunk28.get ⟨28, by decide⟩ := by
  change canonicalBox7_924.toKeyData 188160 = ⟨![2, (45 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_924 : keySolid (keys7Chunk28.get ⟨28, by decide⟩) = canonicalPose7_924.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_924 (box := canonicalBox7_924) (k := keys7Chunk28.get ⟨28, by decide⟩) (canonicalMatch7_924) (canonicalDecode7_924)

def canonicalPose7_925 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, true, false, false, true, false], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_925 : BoxKey 7 :=
  ⟨![376320, 309120, 248640, 134400, 100800, 268800, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 309540, 248240, 134785, 101360, 268310, 302848], false⟩

theorem canonicalMatch7_925 :
    canonicalPose7_925.boxKey 188160 (referenceBox7 (!canonicalBox7_925.bump)) = canonicalBox7_925 := by decide +kernel

theorem canonicalDecode7_925 : canonicalBox7_925.toKeyData 188160 = keys7Chunk28.get ⟨29, by decide⟩ := by
  change canonicalBox7_925.toKeyData 188160 = ⟨![2, (23 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_925 : keySolid (keys7Chunk28.get ⟨29, by decide⟩) = canonicalPose7_925.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_925 (box := canonicalBox7_925) (k := keys7Chunk28.get ⟨29, by decide⟩) (canonicalMatch7_925) (canonicalDecode7_925)

def canonicalPose7_926 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, true, true, true, true], ![2, 2, 2, 1, 1, 2, 2]⟩
def canonicalBox7_926 : BoxKey 7 :=
  ⟨![262080, 376320, 255360, 60480, 53760, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 375760, 254940, 60080, 53375, 274960, 268310], false⟩

theorem canonicalMatch7_926 :
    canonicalPose7_926.boxKey 188160 (referenceBox7 (!canonicalBox7_926.bump)) = canonicalBox7_926 := by decide +kernel

theorem canonicalDecode7_926 : canonicalBox7_926.toKeyData 188160 = keys7Chunk28.get ⟨30, by decide⟩ := by
  change canonicalBox7_926.toKeyData 188160 = ⟨![(39 / 28), 2, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (671 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_926 : keySolid (keys7Chunk28.get ⟨30, by decide⟩) = canonicalPose7_926.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_926 (box := canonicalBox7_926) (k := keys7Chunk28.get ⟨30, by decide⟩) (canonicalMatch7_926) (canonicalDecode7_926)

def canonicalPose7_927 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, true, false, false, true, true], ![1, 2, 2, 0, 0, 2, 2]⟩
def canonicalBox7_927 : BoxKey 7 :=
  ⟨![315840, 255360, 376320, 114240, 107520, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 254940, 375760, 114688, 108010, 274960, 241535], false⟩

theorem canonicalMatch7_927 :
    canonicalPose7_927.boxKey 188160 (referenceBox7 (!canonicalBox7_927.bump)) = canonicalBox7_927 := by decide +kernel

theorem canonicalDecode7_927 : canonicalBox7_927.toKeyData 188160 = keys7Chunk28.get ⟨31, by decide⟩ := by
  change canonicalBox7_927.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (671 / 336), (64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_927 : keySolid (keys7Chunk28.get ⟨31, by decide⟩) = canonicalPose7_927.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_927 (box := canonicalBox7_927) (k := keys7Chunk28.get ⟨31, by decide⟩) (canonicalMatch7_927) (canonicalDecode7_927)

theorem keys7Chunk28_canonical : ∀ k ∈ keys7Chunk28,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk28, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_896, canonicalSolid7_896⟩
  · exact ⟨canonicalPose7_897, canonicalSolid7_897⟩
  · exact ⟨canonicalPose7_898, canonicalSolid7_898⟩
  · exact ⟨canonicalPose7_899, canonicalSolid7_899⟩
  · exact ⟨canonicalPose7_900, canonicalSolid7_900⟩
  · exact ⟨canonicalPose7_901, canonicalSolid7_901⟩
  · exact ⟨canonicalPose7_902, canonicalSolid7_902⟩
  · exact ⟨canonicalPose7_903, canonicalSolid7_903⟩
  · exact ⟨canonicalPose7_904, canonicalSolid7_904⟩
  · exact ⟨canonicalPose7_905, canonicalSolid7_905⟩
  · exact ⟨canonicalPose7_906, canonicalSolid7_906⟩
  · exact ⟨canonicalPose7_907, canonicalSolid7_907⟩
  · exact ⟨canonicalPose7_908, canonicalSolid7_908⟩
  · exact ⟨canonicalPose7_909, canonicalSolid7_909⟩
  · exact ⟨canonicalPose7_910, canonicalSolid7_910⟩
  · exact ⟨canonicalPose7_911, canonicalSolid7_911⟩
  · exact ⟨canonicalPose7_912, canonicalSolid7_912⟩
  · exact ⟨canonicalPose7_913, canonicalSolid7_913⟩
  · exact ⟨canonicalPose7_914, canonicalSolid7_914⟩
  · exact ⟨canonicalPose7_915, canonicalSolid7_915⟩
  · exact ⟨canonicalPose7_916, canonicalSolid7_916⟩
  · exact ⟨canonicalPose7_917, canonicalSolid7_917⟩
  · exact ⟨canonicalPose7_918, canonicalSolid7_918⟩
  · exact ⟨canonicalPose7_919, canonicalSolid7_919⟩
  · exact ⟨canonicalPose7_920, canonicalSolid7_920⟩
  · exact ⟨canonicalPose7_921, canonicalSolid7_921⟩
  · exact ⟨canonicalPose7_922, canonicalSolid7_922⟩
  · exact ⟨canonicalPose7_923, canonicalSolid7_923⟩
  · exact ⟨canonicalPose7_924, canonicalSolid7_924⟩
  · exact ⟨canonicalPose7_925, canonicalSolid7_925⟩
  · exact ⟨canonicalPose7_926, canonicalSolid7_926⟩
  · exact ⟨canonicalPose7_927, canonicalSolid7_927⟩

#print axioms keys7Chunk28_canonical

end SparseMonotiles.Canonical
