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

def canonicalPose7_864 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, false, true, false, true, false], ![1, 2, 0, 2, 0, 2, 1]⟩
def canonicalBox7_864 : BoxKey 7 :=
  ⟨![322560, 275520, 107520, 262080, 0, 255360, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 274960, 108010, 261632, 560, 254940, 316240], false⟩

theorem canonicalMatch7_864 :
    canonicalPose7_864.boxKey 188160 (referenceBox7 (!canonicalBox7_864.bump)) = canonicalBox7_864 := by decide +kernel

theorem canonicalDecode7_864 : canonicalBox7_864.toKeyData 188160 = keys7Chunk27.get ⟨0, by decide⟩ := by
  change canonicalBox7_864.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (19 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (607 / 448), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_864 : keySolid (keys7Chunk27.get ⟨0, by decide⟩) = canonicalPose7_864.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_864 (box := canonicalBox7_864) (k := keys7Chunk27.get ⟨0, by decide⟩) (canonicalMatch7_864) (canonicalDecode7_864)

def canonicalPose7_865 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, false, false, false, true, true], ![2, 2, 0, 1, 0, 2, 2]⟩
def canonicalBox7_865 : BoxKey 7 :=
  ⟨![268800, 275520, 134400, 315840, 120960, 376320, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 134785, 316240, 121380, 375760, 261632], false⟩

theorem canonicalMatch7_865 :
    canonicalPose7_865.boxKey 188160 (referenceBox7 (!canonicalBox7_865.bump)) = canonicalBox7_865 := by decide +kernel

theorem canonicalDecode7_865 : canonicalBox7_865.toKeyData 188160 = keys7Chunk27.get ⟨1, by decide⟩ := by
  change canonicalBox7_865.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (5 / 7), (47 / 28), (9 / 14), 2, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_865 : keySolid (keys7Chunk27.get ⟨1, by decide⟩) = canonicalPose7_865.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_865 (box := canonicalBox7_865) (k := keys7Chunk27.get ⟨1, by decide⟩) (canonicalMatch7_865) (canonicalDecode7_865)

def canonicalPose7_866 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, true, true, true, true, true, false], ![2, 2, 1, 2, 1, 2, 2]⟩
def canonicalBox7_866 : BoxKey 7 :=
  ⟨![268800, 275520, 53760, 248640, 67200, 262080, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 274960, 53375, 248240, 66780, 261632, 376880], true⟩

theorem canonicalMatch7_866 :
    canonicalPose7_866.boxKey 188160 (referenceBox7 (!canonicalBox7_866.bump)) = canonicalBox7_866 := by decide +kernel

theorem canonicalDecode7_866 : canonicalBox7_866.toKeyData 188160 = keys7Chunk27.get ⟨2, by decide⟩ := by
  change canonicalBox7_866.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (2 / 7), (37 / 28), (5 / 14), (39 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_866 : keySolid (keys7Chunk27.get ⟨2, by decide⟩) = canonicalPose7_866.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_866 (box := canonicalBox7_866) (k := keys7Chunk27.get ⟨2, by decide⟩) (canonicalMatch7_866) (canonicalDecode7_866)

def canonicalPose7_867 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, true, true, false, false], ![2, 2, 1, 2, 2, 0, 0]⟩
def canonicalBox7_867 : BoxKey 7 :=
  ⟨![376320, 255360, 60480, 241920, 275520, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 254940, 60080, 241535, 274960, 108010, 114688], false⟩

theorem canonicalMatch7_867 :
    canonicalPose7_867.boxKey 188160 (referenceBox7 (!canonicalBox7_867.bump)) = canonicalBox7_867 := by decide +kernel

theorem canonicalDecode7_867 : canonicalBox7_867.toKeyData 188160 = keys7Chunk27.get ⟨3, by decide⟩ := by
  change canonicalBox7_867.toKeyData 188160 = ⟨![2, (19 / 14), (9 / 28), (9 / 7), (41 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_867 : keySolid (keys7Chunk27.get ⟨3, by decide⟩) = canonicalPose7_867.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_867 (box := canonicalBox7_867) (k := keys7Chunk27.get ⟨3, by decide⟩) (canonicalMatch7_867) (canonicalDecode7_867)

def canonicalPose7_868 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, false, true, true, true, true], ![2, 2, 0, 2, 2, 1, 1]⟩
def canonicalBox7_868 : BoxKey 7 :=
  ⟨![255360, 376320, 114240, 268800, 275520, 53760, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 375760, 114688, 268310, 274960, 53375, 60080], false⟩

theorem canonicalMatch7_868 :
    canonicalPose7_868.boxKey 188160 (referenceBox7 (!canonicalBox7_868.bump)) = canonicalBox7_868 := by decide +kernel

theorem canonicalDecode7_868 : canonicalBox7_868.toKeyData 188160 = keys7Chunk27.get ⟨4, by decide⟩ := by
  change canonicalBox7_868.toKeyData 188160 = ⟨![(19 / 14), 2, (17 / 28), (10 / 7), (41 / 28), (2 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_868 : keySolid (keys7Chunk27.get ⟨4, by decide⟩) = canonicalPose7_868.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_868 (box := canonicalBox7_868) (k := keys7Chunk27.get ⟨4, by decide⟩) (canonicalMatch7_868) (canonicalDecode7_868)

def canonicalPose7_869 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, true, false, true, false, false], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_869 : BoxKey 7 :=
  ⟨![268800, 302400, 0, 309120, 248640, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 302848, -560, 309540, 248240, 134785, 101360], true⟩

theorem canonicalMatch7_869 :
    canonicalPose7_869.boxKey 188160 (referenceBox7 (!canonicalBox7_869.bump)) = canonicalBox7_869 := by decide +kernel

theorem canonicalDecode7_869 : canonicalBox7_869.toKeyData 188160 = keys7Chunk27.get ⟨5, by decide⟩ := by
  change canonicalBox7_869.toKeyData 188160 = ⟨![(10 / 7), (45 / 28), 0, (23 / 14), (37 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (169 / 105), (-1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_869 : keySolid (keys7Chunk27.get ⟨5, by decide⟩) = canonicalPose7_869.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_869 (box := canonicalBox7_869) (k := keys7Chunk27.get ⟨5, by decide⟩) (canonicalMatch7_869) (canonicalDecode7_869)

def canonicalPose7_870 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, false, false, true, false, false], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_870 : BoxKey 7 :=
  ⟨![248640, 309120, 0, 302400, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 309540, 560, 302848, 268310, 101360, 134785], false⟩

theorem canonicalMatch7_870 :
    canonicalPose7_870.boxKey 188160 (referenceBox7 (!canonicalBox7_870.bump)) = canonicalBox7_870 := by decide +kernel

theorem canonicalDecode7_870 : canonicalBox7_870.toKeyData 188160 = keys7Chunk27.get ⟨6, by decide⟩ := by
  change canonicalBox7_870.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), 0, (45 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (1 / 336), (169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_870 : keySolid (keys7Chunk27.get ⟨6, by decide⟩) = canonicalPose7_870.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_870 (box := canonicalBox7_870) (k := keys7Chunk27.get ⟨6, by decide⟩) (canonicalMatch7_870) (canonicalDecode7_870)

def canonicalPose7_871 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, false, false, true, true, true], ![2, 2, 0, 2, 2, 1, 1]⟩
def canonicalBox7_871 : BoxKey 7 :=
  ⟨![275520, 268800, 114240, 376320, 255360, 60480, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 114688, 376880, 254940, 60080, 53375], true⟩

theorem canonicalMatch7_871 :
    canonicalPose7_871.boxKey 188160 (referenceBox7 (!canonicalBox7_871.bump)) = canonicalBox7_871 := by decide +kernel

theorem canonicalDecode7_871 : canonicalBox7_871.toKeyData 188160 = keys7Chunk27.get ⟨7, by decide⟩ := by
  change canonicalBox7_871.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (751 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_871 : keySolid (keys7Chunk27.get ⟨7, by decide⟩) = canonicalPose7_871.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_871 (box := canonicalBox7_871) (k := keys7Chunk27.get ⟨7, by decide⟩) (canonicalMatch7_871) (canonicalDecode7_871)

def canonicalPose7_872 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, false, false, false], ![2, 2, 1, 2, 2, 0, 0]⟩
def canonicalBox7_872 : BoxKey 7 :=
  ⟨![275520, 241920, 60480, 255360, 376320, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 60080, 254940, 376880, 114688, 108010], true⟩

theorem canonicalMatch7_872 :
    canonicalPose7_872.boxKey 188160 (referenceBox7 (!canonicalBox7_872.bump)) = canonicalBox7_872 := by decide +kernel

theorem canonicalDecode7_872 : canonicalBox7_872.toKeyData 188160 = keys7Chunk27.get ⟨8, by decide⟩ := by
  change canonicalBox7_872.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (673 / 336), (64 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_872 : keySolid (keys7Chunk27.get ⟨8, by decide⟩) = canonicalPose7_872.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_872 (box := canonicalBox7_872) (k := keys7Chunk27.get ⟨8, by decide⟩) (canonicalMatch7_872) (canonicalDecode7_872)

def canonicalPose7_873 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, false, false, false, true, false, false], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_873 : BoxKey 7 :=
  ⟨![275520, 322560, 127680, 309120, 262080, 0, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 322945, 128080, 309540, 261632, 560, 108010], false⟩

theorem canonicalMatch7_873 :
    canonicalPose7_873.boxKey 188160 (referenceBox7 (!canonicalBox7_873.bump)) = canonicalBox7_873 := by decide +kernel

theorem canonicalDecode7_873 : canonicalBox7_873.toKeyData 188160 = keys7Chunk27.get ⟨9, by decide⟩ := by
  change canonicalBox7_873.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (19 / 28), (23 / 14), (39 / 28), 0, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (1 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_873 : keySolid (keys7Chunk27.get ⟨9, by decide⟩) = canonicalPose7_873.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_873 (box := canonicalBox7_873) (k := keys7Chunk27.get ⟨9, by decide⟩) (canonicalMatch7_873) (canonicalDecode7_873)

def canonicalPose7_874 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, false, false, false, true, false, true], ![2, 1, 0, 1, 2, 0, 0]⟩
def canonicalBox7_874 : BoxKey 7 :=
  ⟨![262080, 309120, 127680, 322560, 275520, 107520, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 309540, 128080, 322945, 274960, 108010, -560], true⟩

theorem canonicalMatch7_874 :
    canonicalPose7_874.boxKey 188160 (referenceBox7 (!canonicalBox7_874.bump)) = canonicalBox7_874 := by decide +kernel

theorem canonicalDecode7_874 : canonicalBox7_874.toKeyData 188160 = keys7Chunk27.get ⟨10, by decide⟩ := by
  change canonicalBox7_874.toKeyData 188160 = ⟨![(39 / 28), (23 / 14), (19 / 28), (12 / 7), (41 / 28), (4 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_874 : keySolid (keys7Chunk27.get ⟨10, by decide⟩) = canonicalPose7_874.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_874 (box := canonicalBox7_874) (k := keys7Chunk27.get ⟨10, by decide⟩) (canonicalMatch7_874) (canonicalDecode7_874)

def canonicalPose7_875 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, true, true, false, false], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_875 : BoxKey 7 :=
  ⟨![376320, 302400, 107520, 275520, 241920, 127680, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 302848, 108010, 274960, 241535, 128080, 309540], true⟩

theorem canonicalMatch7_875 :
    canonicalPose7_875.boxKey 188160 (referenceBox7 (!canonicalBox7_875.bump)) = canonicalBox7_875 := by decide +kernel

theorem canonicalDecode7_875 : canonicalBox7_875.toKeyData 188160 = keys7Chunk27.get ⟨11, by decide⟩ := by
  change canonicalBox7_875.toKeyData 188160 = ⟨![2, (45 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_875 : keySolid (keys7Chunk27.get ⟨11, by decide⟩) = canonicalPose7_875.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_875 (box := canonicalBox7_875) (k := keys7Chunk27.get ⟨11, by decide⟩) (canonicalMatch7_875) (canonicalDecode7_875)

def canonicalPose7_876 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, true, true, false, false], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_876 : BoxKey 7 :=
  ⟨![376320, 309120, 127680, 241920, 275520, 107520, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 309540, 128080, 241535, 274960, 108010, 302848], false⟩

theorem canonicalMatch7_876 :
    canonicalPose7_876.boxKey 188160 (referenceBox7 (!canonicalBox7_876.bump)) = canonicalBox7_876 := by decide +kernel

theorem canonicalDecode7_876 : canonicalBox7_876.toKeyData 188160 = keys7Chunk27.get ⟨12, by decide⟩ := by
  change canonicalBox7_876.toKeyData 188160 = ⟨![2, (23 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_876 : keySolid (keys7Chunk27.get ⟨12, by decide⟩) = canonicalPose7_876.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_876 (box := canonicalBox7_876) (k := keys7Chunk27.get ⟨12, by decide⟩) (canonicalMatch7_876) (canonicalDecode7_876)

def canonicalPose7_877 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, false, false, false, false, true], ![2, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_877 : BoxKey 7 :=
  ⟨![262080, 376320, 120960, 315840, 322560, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 375760, 121380, 316240, 322945, 101360, 268310], false⟩

theorem canonicalMatch7_877 :
    canonicalPose7_877.boxKey 188160 (referenceBox7 (!canonicalBox7_877.bump)) = canonicalBox7_877 := by decide +kernel

theorem canonicalDecode7_877 : canonicalBox7_877.toKeyData 188160 = keys7Chunk27.get ⟨13, by decide⟩ := by
  change canonicalBox7_877.toKeyData 188160 = ⟨![(39 / 28), 2, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (671 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_877 : keySolid (keys7Chunk27.get ⟨13, by decide⟩) = canonicalPose7_877.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_877 (box := canonicalBox7_877) (k := keys7Chunk27.get ⟨13, by decide⟩) (canonicalMatch7_877) (canonicalDecode7_877)

def canonicalPose7_878 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, false, true, true, false, true], ![1, 2, 0, 2, 2, 0, 2]⟩
def canonicalBox7_878 : BoxKey 7 :=
  ⟨![315840, 255360, 0, 262080, 268800, 100800, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 254940, 560, 261632, 268310, 101360, 241535], false⟩

theorem canonicalMatch7_878 :
    canonicalPose7_878.boxKey 188160 (referenceBox7 (!canonicalBox7_878.bump)) = canonicalBox7_878 := by decide +kernel

theorem canonicalDecode7_878 : canonicalBox7_878.toKeyData 188160 = keys7Chunk27.get ⟨14, by decide⟩ := by
  change canonicalBox7_878.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_878 : keySolid (keys7Chunk27.get ⟨14, by decide⟩) = canonicalPose7_878.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_878 (box := canonicalBox7_878) (k := keys7Chunk27.get ⟨14, by decide⟩) (canonicalMatch7_878) (canonicalDecode7_878)

def canonicalPose7_879 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, false, false, false, true, false, false], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_879 : BoxKey 7 :=
  ⟨![248640, 309120, 114240, 376320, 268800, 100800, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 309540, 114688, 376880, 268310, 101360, 322945], true⟩

theorem canonicalMatch7_879 :
    canonicalPose7_879.boxKey 188160 (referenceBox7 (!canonicalBox7_879.bump)) = canonicalBox7_879 := by decide +kernel

theorem canonicalDecode7_879 : canonicalBox7_879.toKeyData 188160 = keys7Chunk27.get ⟨15, by decide⟩ := by
  change canonicalBox7_879.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (64 / 105), (673 / 336), (3833 / 2688), (181 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_879 : keySolid (keys7Chunk27.get ⟨15, by decide⟩) = canonicalPose7_879.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_879 (box := canonicalBox7_879) (k := keys7Chunk27.get ⟨15, by decide⟩) (canonicalMatch7_879) (canonicalDecode7_879)

def canonicalPose7_880 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, false, false, true, true, false, false], ![2, 1, 0, 2, 2, 0, 1]⟩
def canonicalBox7_880 : BoxKey 7 :=
  ⟨![248640, 322560, 100800, 268800, 376320, 114240, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 322945, 101360, 268310, 375760, 114688, 309540], false⟩

theorem canonicalMatch7_880 :
    canonicalPose7_880.boxKey 188160 (referenceBox7 (!canonicalBox7_880.bump)) = canonicalBox7_880 := by decide +kernel

theorem canonicalDecode7_880 : canonicalBox7_880.toKeyData 188160 = keys7Chunk27.get ⟨16, by decide⟩ := by
  change canonicalBox7_880.toKeyData 188160 = ⟨![(37 / 28), (12 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (671 / 336), (64 / 105), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_880 : keySolid (keys7Chunk27.get ⟨16, by decide⟩) = canonicalPose7_880.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_880 (box := canonicalBox7_880) (k := keys7Chunk27.get ⟨16, by decide⟩) (canonicalMatch7_880) (canonicalDecode7_880)

def canonicalPose7_881 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, false, true, true, true, true], ![1, 2, 0, 2, 2, 0, 2]⟩
def canonicalBox7_881 : BoxKey 7 :=
  ⟨![315840, 241920, 100800, 268800, 262080, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 241535, 101360, 268310, 261632, -560, 254940], true⟩

theorem canonicalMatch7_881 :
    canonicalPose7_881.boxKey 188160 (referenceBox7 (!canonicalBox7_881.bump)) = canonicalBox7_881 := by decide +kernel

theorem canonicalDecode7_881 : canonicalBox7_881.toKeyData 188160 = keys7Chunk27.get ⟨17, by decide⟩ := by
  change canonicalBox7_881.toKeyData 188160 = ⟨![(47 / 28), (9 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_881 : keySolid (keys7Chunk27.get ⟨17, by decide⟩) = canonicalPose7_881.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_881 (box := canonicalBox7_881) (k := keys7Chunk27.get ⟨17, by decide⟩) (canonicalMatch7_881) (canonicalDecode7_881)

def canonicalPose7_882 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, false, false, false, false], ![2, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_882 : BoxKey 7 :=
  ⟨![262080, 268800, 100800, 322560, 315840, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 101360, 322945, 316240, 121380, 376880], true⟩

theorem canonicalMatch7_882 :
    canonicalPose7_882.boxKey 188160 (referenceBox7 (!canonicalBox7_882.bump)) = canonicalBox7_882 := by decide +kernel

theorem canonicalDecode7_882 : canonicalBox7_882.toKeyData 188160 = keys7Chunk27.get ⟨18, by decide⟩ := by
  change canonicalBox7_882.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_882 : keySolid (keys7Chunk27.get ⟨18, by decide⟩) = canonicalPose7_882.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_882 (box := canonicalBox7_882) (k := keys7Chunk27.get ⟨18, by decide⟩) (canonicalMatch7_882) (canonicalDecode7_882)

def canonicalPose7_883 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, true, false, false, true, false, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_883 : BoxKey 7 :=
  ⟨![376320, 268800, 100800, 322560, 248640, 309120, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![376880, 268310, 101360, 322945, 248240, 309540, 114688], true⟩

theorem canonicalMatch7_883 :
    canonicalPose7_883.boxKey 188160 (referenceBox7 (!canonicalBox7_883.bump)) = canonicalBox7_883 := by decide +kernel

theorem canonicalDecode7_883 : canonicalBox7_883.toKeyData 188160 = keys7Chunk27.get ⟨19, by decide⟩ := by
  change canonicalBox7_883.toKeyData 188160 = ⟨![2, (10 / 7), (15 / 28), (12 / 7), (37 / 28), (23 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(673 / 336), (3833 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_883 : keySolid (keys7Chunk27.get ⟨19, by decide⟩) = canonicalPose7_883.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_883 (box := canonicalBox7_883) (k := keys7Chunk27.get ⟨19, by decide⟩) (canonicalMatch7_883) (canonicalDecode7_883)

def canonicalPose7_884 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, true, false, false, true, false, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_884 : BoxKey 7 :=
  ⟨![268800, 376320, 114240, 309120, 248640, 322560, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 375760, 114688, 309540, 248240, 322945, 101360], false⟩

theorem canonicalMatch7_884 :
    canonicalPose7_884.boxKey 188160 (referenceBox7 (!canonicalBox7_884.bump)) = canonicalBox7_884 := by decide +kernel

theorem canonicalDecode7_884 : canonicalBox7_884.toKeyData 188160 = keys7Chunk27.get ⟨20, by decide⟩ := by
  change canonicalBox7_884.toKeyData 188160 = ⟨![(10 / 7), 2, (17 / 28), (23 / 14), (37 / 28), (12 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (671 / 336), (64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_884 : keySolid (keys7Chunk27.get ⟨20, by decide⟩) = canonicalPose7_884.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_884 (box := canonicalBox7_884) (k := keys7Chunk27.get ⟨20, by decide⟩) (canonicalMatch7_884) (canonicalDecode7_884)

def canonicalPose7_885 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, true, false, true, false], ![2, 2, 0, 2, 1, 2, 0]⟩
def canonicalBox7_885 : BoxKey 7 :=
  ⟨![268800, 262080, 0, 255360, 315840, 241920, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, -560, 254940, 316240, 241535, 101360], true⟩

theorem canonicalMatch7_885 :
    canonicalPose7_885.boxKey 188160 (referenceBox7 (!canonicalBox7_885.bump)) = canonicalBox7_885 := by decide +kernel

theorem canonicalDecode7_885 : canonicalBox7_885.toKeyData 188160 = keys7Chunk27.get ⟨21, by decide⟩ := by
  change canonicalBox7_885.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 0, (19 / 14), (47 / 28), (9 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_885 : keySolid (keys7Chunk27.get ⟨21, by decide⟩) = canonicalPose7_885.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_885 (box := canonicalBox7_885) (k := keys7Chunk27.get ⟨21, by decide⟩) (canonicalMatch7_885) (canonicalDecode7_885)

def canonicalPose7_886 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, false, true, true, false], ![1, 1, 0, 2, 2, 2, 0]⟩
def canonicalBox7_886 : BoxKey 7 :=
  ⟨![322560, 315840, 120960, 376320, 262080, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 316240, 121380, 376880, 261632, 268310, 101360], true⟩

theorem canonicalMatch7_886 :
    canonicalPose7_886.boxKey 188160 (referenceBox7 (!canonicalBox7_886.bump)) = canonicalBox7_886 := by decide +kernel

theorem canonicalDecode7_886 : canonicalBox7_886.toKeyData 188160 = keys7Chunk27.get ⟨22, by decide⟩ := by
  change canonicalBox7_886.toKeyData 188160 = ⟨![(12 / 7), (47 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (3953 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_886 : keySolid (keys7Chunk27.get ⟨22, by decide⟩) = canonicalPose7_886.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_886 (box := canonicalBox7_886) (k := keys7Chunk27.get ⟨22, by decide⟩) (canonicalMatch7_886) (canonicalDecode7_886)

def canonicalPose7_887 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, false, false, false, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_887 : BoxKey 7 :=
  ⟨![275520, 241920, 127680, 309120, 376320, 302400, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 128080, 309540, 376880, 302848, 108010], true⟩

theorem canonicalMatch7_887 :
    canonicalPose7_887.boxKey 188160 (referenceBox7 (!canonicalBox7_887.bump)) = canonicalBox7_887 := by decide +kernel

theorem canonicalDecode7_887 : canonicalBox7_887.toKeyData 188160 = keys7Chunk27.get ⟨23, by decide⟩ := by
  change canonicalBox7_887.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (19 / 28), (23 / 14), 2, (45 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448), (673 / 336), (169 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_887 : keySolid (keys7Chunk27.get ⟨23, by decide⟩) = canonicalPose7_887.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_887 (box := canonicalBox7_887) (k := keys7Chunk27.get ⟨23, by decide⟩) (canonicalMatch7_887) (canonicalDecode7_887)

def canonicalPose7_888 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, false, true, false, false], ![2, 2, 0, 1, 2, 1, 0]⟩
def canonicalBox7_888 : BoxKey 7 :=
  ⟨![241920, 275520, 107520, 302400, 376320, 309120, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 108010, 302848, 375760, 309540, 128080], false⟩

theorem canonicalMatch7_888 :
    canonicalPose7_888.boxKey 188160 (referenceBox7 (!canonicalBox7_888.bump)) = canonicalBox7_888 := by decide +kernel

theorem canonicalDecode7_888 : canonicalBox7_888.toKeyData 188160 = keys7Chunk27.get ⟨24, by decide⟩ := by
  change canonicalBox7_888.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (4 / 7), (45 / 28), 2, (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105), (671 / 336), (737 / 448), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_888 : keySolid (keys7Chunk27.get ⟨24, by decide⟩) = canonicalPose7_888.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_888 (box := canonicalBox7_888) (k := keys7Chunk27.get ⟨24, by decide⟩) (canonicalMatch7_888) (canonicalDecode7_888)

def canonicalPose7_889 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, false, true, true, true, false], ![1, 1, 0, 2, 2, 2, 0]⟩
def canonicalBox7_889 : BoxKey 7 :=
  ⟨![315840, 322560, 100800, 268800, 262080, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 322945, 101360, 268310, 261632, 375760, 121380], false⟩

theorem canonicalMatch7_889 :
    canonicalPose7_889.boxKey 188160 (referenceBox7 (!canonicalBox7_889.bump)) = canonicalBox7_889 := by decide +kernel

theorem canonicalDecode7_889 : canonicalBox7_889.toKeyData 188160 = keys7Chunk27.get ⟨25, by decide⟩ := by
  change canonicalBox7_889.toKeyData 188160 = ⟨![(47 / 28), (12 / 7), (15 / 28), (10 / 7), (39 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_889 : keySolid (keys7Chunk27.get ⟨25, by decide⟩) = canonicalPose7_889.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_889 (box := canonicalBox7_889) (k := keys7Chunk27.get ⟨25, by decide⟩) (canonicalMatch7_889) (canonicalDecode7_889)

def canonicalPose7_890 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, true, false, true, false], ![2, 2, 0, 2, 1, 2, 0]⟩
def canonicalBox7_890 : BoxKey 7 :=
  ⟨![262080, 268800, 100800, 241920, 315840, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 101360, 241535, 316240, 254940, 560], false⟩

theorem canonicalMatch7_890 :
    canonicalPose7_890.boxKey 188160 (referenceBox7 (!canonicalBox7_890.bump)) = canonicalBox7_890 := by decide +kernel

theorem canonicalDecode7_890 : canonicalBox7_890.toKeyData 188160 = keys7Chunk27.get ⟨26, by decide⟩ := by
  change canonicalBox7_890.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (15 / 28), (9 / 7), (47 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_890 : keySolid (keys7Chunk27.get ⟨26, by decide⟩) = canonicalPose7_890.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_890 (box := canonicalBox7_890) (k := keys7Chunk27.get ⟨26, by decide⟩) (canonicalMatch7_890) (canonicalDecode7_890)

def canonicalPose7_891 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, true, true, true, true], ![2, 2, 1, 2, 2, 2, 2]⟩
def canonicalBox7_891 : BoxKey 7 :=
  ⟨![376320, 255360, 60480, 241920, 275520, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 254940, 60080, 241535, 274960, 268310, 261632], false⟩

theorem canonicalMatch7_891 :
    canonicalPose7_891.boxKey 188160 (referenceBox7 (!canonicalBox7_891.bump)) = canonicalBox7_891 := by decide +kernel

theorem canonicalDecode7_891 : canonicalBox7_891.toKeyData 188160 = keys7Chunk27.get ⟨27, by decide⟩ := by
  change canonicalBox7_891.toKeyData 188160 = ⟨![2, (19 / 14), (9 / 28), (9 / 7), (41 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_891 : keySolid (keys7Chunk27.get ⟨27, by decide⟩) = canonicalPose7_891.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_891 (box := canonicalBox7_891) (k := keys7Chunk27.get ⟨27, by decide⟩) (canonicalMatch7_891) (canonicalDecode7_891)

def canonicalPose7_892 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, false, true, true, false, false], ![2, 2, 0, 2, 2, 1, 1]⟩
def canonicalBox7_892 : BoxKey 7 :=
  ⟨![255360, 376320, 114240, 268800, 275520, 322560, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 375760, 114688, 268310, 274960, 322945, 316240], false⟩

theorem canonicalMatch7_892 :
    canonicalPose7_892.boxKey 188160 (referenceBox7 (!canonicalBox7_892.bump)) = canonicalBox7_892 := by decide +kernel

theorem canonicalDecode7_892 : canonicalBox7_892.toKeyData 188160 = keys7Chunk27.get ⟨28, by decide⟩ := by
  change canonicalBox7_892.toKeyData 188160 = ⟨![(19 / 14), 2, (17 / 28), (10 / 7), (41 / 28), (12 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_892 : keySolid (keys7Chunk27.get ⟨28, by decide⟩) = canonicalPose7_892.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_892 (box := canonicalBox7_892) (k := keys7Chunk27.get ⟨28, by decide⟩) (canonicalMatch7_892) (canonicalDecode7_892)

def canonicalPose7_893 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, true, false, true, true, true], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_893 : BoxKey 7 :=
  ⟨![268800, 302400, 0, 309120, 248640, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 302848, -560, 309540, 248240, 241535, 274960], true⟩

theorem canonicalMatch7_893 :
    canonicalPose7_893.boxKey 188160 (referenceBox7 (!canonicalBox7_893.bump)) = canonicalBox7_893 := by decide +kernel

theorem canonicalDecode7_893 : canonicalBox7_893.toKeyData 188160 = keys7Chunk27.get ⟨29, by decide⟩ := by
  change canonicalBox7_893.toKeyData 188160 = ⟨![(10 / 7), (45 / 28), 0, (23 / 14), (37 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (169 / 105), (-1 / 336), (737 / 448), (3103 / 2352), (6901 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_893 : keySolid (keys7Chunk27.get ⟨29, by decide⟩) = canonicalPose7_893.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_893 (box := canonicalBox7_893) (k := keys7Chunk27.get ⟨29, by decide⟩) (canonicalMatch7_893) (canonicalDecode7_893)

def canonicalPose7_894 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, false, false, true, true, true], ![2, 1, 0, 1, 2, 2, 2]⟩
def canonicalBox7_894 : BoxKey 7 :=
  ⟨![248640, 309120, 0, 302400, 268800, 275520, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 309540, 560, 302848, 268310, 274960, 241535], false⟩

theorem canonicalMatch7_894 :
    canonicalPose7_894.boxKey 188160 (referenceBox7 (!canonicalBox7_894.bump)) = canonicalBox7_894 := by decide +kernel

theorem canonicalDecode7_894 : canonicalBox7_894.toKeyData 188160 = keys7Chunk27.get ⟨30, by decide⟩ := by
  change canonicalBox7_894.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), 0, (45 / 28), (10 / 7), (41 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (1 / 336), (169 / 105), (3833 / 2688), (491 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_894 : keySolid (keys7Chunk27.get ⟨30, by decide⟩) = canonicalPose7_894.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_894 (box := canonicalBox7_894) (k := keys7Chunk27.get ⟨30, by decide⟩) (canonicalMatch7_894) (canonicalDecode7_894)

def canonicalPose7_895 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, true, false, false, false, false], ![2, 1, 1, 1, 1, 1, 1]⟩
def canonicalBox7_895 : BoxKey 7 :=
  ⟨![248640, 309120, 188160, 302400, 295680, 288960, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 309540, 187600, 302848, 296170, 289520, 322945], false⟩

theorem canonicalMatch7_895 :
    canonicalPose7_895.boxKey 188160 (referenceBox7 (!canonicalBox7_895.bump)) = canonicalBox7_895 := by decide +kernel

theorem canonicalDecode7_895 : canonicalBox7_895.toKeyData 188160 = keys7Chunk27.get ⟨31, by decide⟩ := by
  change canonicalBox7_895.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), 1, (45 / 28), (11 / 7), (43 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (335 / 336), (169 / 105), (4231 / 2688), (517 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_895 : keySolid (keys7Chunk27.get ⟨31, by decide⟩) = canonicalPose7_895.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_895 (box := canonicalBox7_895) (k := keys7Chunk27.get ⟨31, by decide⟩) (canonicalMatch7_895) (canonicalDecode7_895)

theorem keys7Chunk27_canonical : ∀ k ∈ keys7Chunk27,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk27, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_864, canonicalSolid7_864⟩
  · exact ⟨canonicalPose7_865, canonicalSolid7_865⟩
  · exact ⟨canonicalPose7_866, canonicalSolid7_866⟩
  · exact ⟨canonicalPose7_867, canonicalSolid7_867⟩
  · exact ⟨canonicalPose7_868, canonicalSolid7_868⟩
  · exact ⟨canonicalPose7_869, canonicalSolid7_869⟩
  · exact ⟨canonicalPose7_870, canonicalSolid7_870⟩
  · exact ⟨canonicalPose7_871, canonicalSolid7_871⟩
  · exact ⟨canonicalPose7_872, canonicalSolid7_872⟩
  · exact ⟨canonicalPose7_873, canonicalSolid7_873⟩
  · exact ⟨canonicalPose7_874, canonicalSolid7_874⟩
  · exact ⟨canonicalPose7_875, canonicalSolid7_875⟩
  · exact ⟨canonicalPose7_876, canonicalSolid7_876⟩
  · exact ⟨canonicalPose7_877, canonicalSolid7_877⟩
  · exact ⟨canonicalPose7_878, canonicalSolid7_878⟩
  · exact ⟨canonicalPose7_879, canonicalSolid7_879⟩
  · exact ⟨canonicalPose7_880, canonicalSolid7_880⟩
  · exact ⟨canonicalPose7_881, canonicalSolid7_881⟩
  · exact ⟨canonicalPose7_882, canonicalSolid7_882⟩
  · exact ⟨canonicalPose7_883, canonicalSolid7_883⟩
  · exact ⟨canonicalPose7_884, canonicalSolid7_884⟩
  · exact ⟨canonicalPose7_885, canonicalSolid7_885⟩
  · exact ⟨canonicalPose7_886, canonicalSolid7_886⟩
  · exact ⟨canonicalPose7_887, canonicalSolid7_887⟩
  · exact ⟨canonicalPose7_888, canonicalSolid7_888⟩
  · exact ⟨canonicalPose7_889, canonicalSolid7_889⟩
  · exact ⟨canonicalPose7_890, canonicalSolid7_890⟩
  · exact ⟨canonicalPose7_891, canonicalSolid7_891⟩
  · exact ⟨canonicalPose7_892, canonicalSolid7_892⟩
  · exact ⟨canonicalPose7_893, canonicalSolid7_893⟩
  · exact ⟨canonicalPose7_894, canonicalSolid7_894⟩
  · exact ⟨canonicalPose7_895, canonicalSolid7_895⟩

#print axioms keys7Chunk27_canonical

end SparseMonotiles.Canonical
