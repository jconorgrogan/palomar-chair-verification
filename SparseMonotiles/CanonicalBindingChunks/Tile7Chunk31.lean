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

def canonicalPose7_992 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, true, true, false, true, true], ![1, 1, 2, 2, 0, 2, 2]⟩
def canonicalBox7_992 : BoxKey 7 :=
  ⟨![322560, 315840, 255360, 376320, 114240, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 316240, 254940, 375760, 114688, 268310, 274960], false⟩

theorem canonicalMatch7_992 :
    canonicalPose7_992.boxKey 188160 (referenceBox7 (!canonicalBox7_992.bump)) = canonicalBox7_992 := by decide +kernel

theorem canonicalDecode7_992 : canonicalBox7_992.toKeyData 188160 = keys7Chunk31.get ⟨0, by decide⟩ := by
  change canonicalBox7_992.toKeyData 188160 = ⟨![(12 / 7), (47 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (3953 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_992 : keySolid (keys7Chunk31.get ⟨0, by decide⟩) = canonicalPose7_992.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_992 (box := canonicalBox7_992) (k := keys7Chunk31.get ⟨0, by decide⟩) (canonicalMatch7_992) (canonicalDecode7_992)

def canonicalPose7_993 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, false, false, false, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_993 : BoxKey 7 :=
  ⟨![275520, 241920, 248640, 309120, 0, 302400, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 248240, 309540, 560, 302848, 268310], false⟩

theorem canonicalMatch7_993 :
    canonicalPose7_993.boxKey 188160 (referenceBox7 (!canonicalBox7_993.bump)) = canonicalBox7_993 := by decide +kernel

theorem canonicalDecode7_993 : canonicalBox7_993.toKeyData 188160 = keys7Chunk31.get ⟨1, by decide⟩ := by
  change canonicalBox7_993.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (37 / 28), (23 / 14), 0, (45 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (3103 / 2352), (737 / 448), (1 / 336), (169 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_993 : keySolid (keys7Chunk31.get ⟨1, by decide⟩) = canonicalPose7_993.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_993 (box := canonicalBox7_993) (k := keys7Chunk31.get ⟨1, by decide⟩) (canonicalMatch7_993) (canonicalDecode7_993)

def canonicalPose7_994 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, false, true, false, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_994 : BoxKey 7 :=
  ⟨![241920, 275520, 268800, 302400, 0, 309120, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 268310, 302848, -560, 309540, 248240], true⟩

theorem canonicalMatch7_994 :
    canonicalPose7_994.boxKey 188160 (referenceBox7 (!canonicalBox7_994.bump)) = canonicalBox7_994 := by decide +kernel

theorem canonicalDecode7_994 : canonicalBox7_994.toKeyData 188160 = keys7Chunk31.get ⟨2, by decide⟩ := by
  change canonicalBox7_994.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (10 / 7), (45 / 28), 0, (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (3833 / 2688), (169 / 105), (-1 / 336), (737 / 448), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_994 : keySolid (keys7Chunk31.get ⟨2, by decide⟩) = canonicalPose7_994.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_994 (box := canonicalBox7_994) (k := keys7Chunk31.get ⟨2, by decide⟩) (canonicalMatch7_994) (canonicalDecode7_994)

def canonicalPose7_995 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, true, false, false, true, false, true], ![1, 2, 1, 1, 1, 1, 2]⟩
def canonicalBox7_995 : BoxKey 7 :=
  ⟨![315840, 241920, 288960, 295680, 188160, 302400, 255360], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![316240, 241535, 289520, 296170, 187600, 302848, 254940], false⟩

theorem canonicalMatch7_995 :
    canonicalPose7_995.boxKey 188160 (referenceBox7 (!canonicalBox7_995.bump)) = canonicalBox7_995 := by decide +kernel

theorem canonicalDecode7_995 : canonicalBox7_995.toKeyData 188160 = keys7Chunk31.get ⟨3, by decide⟩ := by
  change canonicalBox7_995.toKeyData 188160 = ⟨![(47 / 28), (9 / 7), (43 / 28), (11 / 7), 1, (45 / 28), (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3953 / 2352), (6901 / 5376), (517 / 336), (4231 / 2688), (335 / 336), (169 / 105), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_995 : keySolid (keys7Chunk31.get ⟨3, by decide⟩) = canonicalPose7_995.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_995 (box := canonicalBox7_995) (k := keys7Chunk31.get ⟨3, by decide⟩) (canonicalMatch7_995) (canonicalDecode7_995)

def canonicalPose7_996 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, true, true, false, false, true], ![1, 1, 2, 2, 0, 2, 2]⟩
def canonicalBox7_996 : BoxKey 7 :=
  ⟨![315840, 322560, 275520, 268800, 114240, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 322945, 274960, 268310, 114688, 376880, 254940], true⟩

theorem canonicalMatch7_996 :
    canonicalPose7_996.boxKey 188160 (referenceBox7 (!canonicalBox7_996.bump)) = canonicalBox7_996 := by decide +kernel

theorem canonicalDecode7_996 : canonicalBox7_996.toKeyData 188160 = keys7Chunk31.get ⟨4, by decide⟩ := by
  change canonicalBox7_996.toKeyData 188160 = ⟨![(47 / 28), (12 / 7), (41 / 28), (10 / 7), (17 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_996 : keySolid (keys7Chunk31.get ⟨4, by decide⟩) = canonicalPose7_996.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_996 (box := canonicalBox7_996) (k := keys7Chunk31.get ⟨4, by decide⟩) (canonicalMatch7_996) (canonicalDecode7_996)

def canonicalPose7_997 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, true, true, true, true, false], ![2, 2, 2, 2, 1, 2, 2]⟩
def canonicalBox7_997 : BoxKey 7 :=
  ⟨![262080, 268800, 275520, 241920, 60480, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 274960, 241535, 60080, 254940, 376880], true⟩

theorem canonicalMatch7_997 :
    canonicalPose7_997.boxKey 188160 (referenceBox7 (!canonicalBox7_997.bump)) = canonicalBox7_997 := by decide +kernel

theorem canonicalDecode7_997 : canonicalBox7_997.toKeyData 188160 = keys7Chunk31.get ⟨5, by decide⟩ := by
  change canonicalBox7_997.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (41 / 28), (9 / 7), (9 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_997 : keySolid (keys7Chunk31.get ⟨5, by decide⟩) = canonicalPose7_997.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_997 (box := canonicalBox7_997) (k := keys7Chunk31.get ⟨5, by decide⟩) (canonicalMatch7_997) (canonicalDecode7_997)

def canonicalPose7_998 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, false, true, true, false, false], ![2, 2, 1, 2, 2, 0, 0]⟩
def canonicalBox7_998 : BoxKey 7 :=
  ⟨![376320, 255360, 315840, 241920, 275520, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 254940, 316240, 241535, 274960, 108010, 114688], true⟩

theorem canonicalMatch7_998 :
    canonicalPose7_998.boxKey 188160 (referenceBox7 (!canonicalBox7_998.bump)) = canonicalBox7_998 := by decide +kernel

theorem canonicalDecode7_998 : canonicalBox7_998.toKeyData 188160 = keys7Chunk31.get ⟨6, by decide⟩ := by
  change canonicalBox7_998.toKeyData 188160 = ⟨![2, (19 / 14), (47 / 28), (9 / 7), (41 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_998 : keySolid (keys7Chunk31.get ⟨6, by decide⟩) = canonicalPose7_998.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_998 (box := canonicalBox7_998) (k := keys7Chunk31.get ⟨6, by decide⟩) (canonicalMatch7_998) (canonicalDecode7_998)

def canonicalPose7_999 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, true, true, true, true], ![2, 2, 2, 2, 2, 1, 1]⟩
def canonicalBox7_999 : BoxKey 7 :=
  ⟨![255360, 376320, 262080, 268800, 275520, 53760, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 376880, 261632, 268310, 274960, 53375, 60080], true⟩

theorem canonicalMatch7_999 :
    canonicalPose7_999.boxKey 188160 (referenceBox7 (!canonicalBox7_999.bump)) = canonicalBox7_999 := by decide +kernel

theorem canonicalDecode7_999 : canonicalBox7_999.toKeyData 188160 = keys7Chunk31.get ⟨7, by decide⟩ := by
  change canonicalBox7_999.toKeyData 188160 = ⟨![(19 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (2 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_999 : keySolid (keys7Chunk31.get ⟨7, by decide⟩) = canonicalPose7_999.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_999 (box := canonicalBox7_999) (k := keys7Chunk31.get ⟨7, by decide⟩) (canonicalMatch7_999) (canonicalDecode7_999)

def canonicalPose7_1000 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, true, false, true, false, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_1000 : BoxKey 7 :=
  ⟨![268800, 302400, 376320, 309120, 248640, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 302848, 375760, 309540, 248240, 134785, 101360], false⟩

theorem canonicalMatch7_1000 :
    canonicalPose7_1000.boxKey 188160 (referenceBox7 (!canonicalBox7_1000.bump)) = canonicalBox7_1000 := by decide +kernel

theorem canonicalDecode7_1000 : canonicalBox7_1000.toKeyData 188160 = keys7Chunk31.get ⟨8, by decide⟩ := by
  change canonicalBox7_1000.toKeyData 188160 = ⟨![(10 / 7), (45 / 28), 2, (23 / 14), (37 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (169 / 105), (671 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1000 : keySolid (keys7Chunk31.get ⟨8, by decide⟩) = canonicalPose7_1000.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1000 (box := canonicalBox7_1000) (k := keys7Chunk31.get ⟨8, by decide⟩) (canonicalMatch7_1000) (canonicalDecode7_1000)

def canonicalPose7_1001 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, false, false, true, false, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_1001 : BoxKey 7 :=
  ⟨![248640, 309120, 376320, 302400, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![248240, 309540, 376880, 302848, 268310, 101360, 134785], true⟩

theorem canonicalMatch7_1001 :
    canonicalPose7_1001.boxKey 188160 (referenceBox7 (!canonicalBox7_1001.bump)) = canonicalBox7_1001 := by decide +kernel

theorem canonicalDecode7_1001 : canonicalBox7_1001.toKeyData 188160 = keys7Chunk31.get ⟨9, by decide⟩ := by
  change canonicalBox7_1001.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), 2, (45 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (673 / 336), (169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1001 : keySolid (keys7Chunk31.get ⟨9, by decide⟩) = canonicalPose7_1001.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1001 (box := canonicalBox7_1001) (k := keys7Chunk31.get ⟨9, by decide⟩) (canonicalMatch7_1001) (canonicalDecode7_1001)

def canonicalPose7_1002 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 2, 1, 1]⟩
def canonicalBox7_1002 : BoxKey 7 :=
  ⟨![275520, 268800, 262080, 376320, 255360, 60480, 53760], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 261632, 375760, 254940, 60080, 53375], false⟩

theorem canonicalMatch7_1002 :
    canonicalPose7_1002.boxKey 188160 (referenceBox7 (!canonicalBox7_1002.bump)) = canonicalBox7_1002 := by decide +kernel

theorem canonicalDecode7_1002 : canonicalBox7_1002.toKeyData 188160 = keys7Chunk31.get ⟨10, by decide⟩ := by
  change canonicalBox7_1002.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (39 / 28), 2, (19 / 14), (9 / 28), (2 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (607 / 448), (751 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1002 : keySolid (keys7Chunk31.get ⟨10, by decide⟩) = canonicalPose7_1002.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1002 (box := canonicalBox7_1002) (k := keys7Chunk31.get ⟨10, by decide⟩) (canonicalMatch7_1002) (canonicalDecode7_1002)

def canonicalPose7_1003 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, false, true, true, false, false], ![2, 2, 1, 2, 2, 0, 0]⟩
def canonicalBox7_1003 : BoxKey 7 :=
  ⟨![275520, 241920, 315840, 255360, 376320, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 316240, 254940, 375760, 114688, 108010], false⟩

theorem canonicalMatch7_1003 :
    canonicalPose7_1003.boxKey 188160 (referenceBox7 (!canonicalBox7_1003.bump)) = canonicalBox7_1003 := by decide +kernel

theorem canonicalDecode7_1003 : canonicalBox7_1003.toKeyData 188160 = keys7Chunk31.get ⟨11, by decide⟩ := by
  change canonicalBox7_1003.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (47 / 28), (19 / 14), 2, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (671 / 336), (64 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1003 : keySolid (keys7Chunk31.get ⟨11, by decide⟩) = canonicalPose7_1003.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1003 (box := canonicalBox7_1003) (k := keys7Chunk31.get ⟨11, by decide⟩) (canonicalMatch7_1003) (canonicalDecode7_1003)

def canonicalPose7_1004 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, false, true, false, true, true, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_1004 : BoxKey 7 :=
  ⟨![275520, 322560, 248640, 309120, 262080, 0, 107520], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 322945, 248240, 309540, 261632, -560, 108010], true⟩

theorem canonicalMatch7_1004 :
    canonicalPose7_1004.boxKey 188160 (referenceBox7 (!canonicalBox7_1004.bump)) = canonicalBox7_1004 := by decide +kernel

theorem canonicalDecode7_1004 : canonicalBox7_1004.toKeyData 188160 = keys7Chunk31.get ⟨12, by decide⟩ := by
  change canonicalBox7_1004.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (37 / 28), (23 / 14), (39 / 28), 0, (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (146 / 105), (-1 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1004 : keySolid (keys7Chunk31.get ⟨12, by decide⟩) = canonicalPose7_1004.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1004 (box := canonicalBox7_1004) (k := keys7Chunk31.get ⟨12, by decide⟩) (canonicalMatch7_1004) (canonicalDecode7_1004)

def canonicalPose7_1005 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, false, true, false, true, false, false], ![2, 1, 2, 1, 2, 0, 0]⟩
def canonicalBox7_1005 : BoxKey 7 :=
  ⟨![262080, 309120, 248640, 322560, 275520, 107520, 0], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 309540, 248240, 322945, 274960, 108010, 560], false⟩

theorem canonicalMatch7_1005 :
    canonicalPose7_1005.boxKey 188160 (referenceBox7 (!canonicalBox7_1005.bump)) = canonicalBox7_1005 := by decide +kernel

theorem canonicalDecode7_1005 : canonicalBox7_1005.toKeyData 188160 = keys7Chunk31.get ⟨13, by decide⟩ := by
  change canonicalBox7_1005.toKeyData 188160 = ⟨![(39 / 28), (23 / 14), (37 / 28), (12 / 7), (41 / 28), (4 / 7), 0], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1005 : keySolid (keys7Chunk31.get ⟨13, by decide⟩) = canonicalPose7_1005.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1005 (box := canonicalBox7_1005) (k := keys7Chunk31.get ⟨13, by decide⟩) (canonicalMatch7_1005) (canonicalDecode7_1005)

def canonicalPose7_1006 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, true, true, true, true], ![2, 2, 2, 2, 2, 1, 2]⟩
def canonicalBox7_1006 : BoxKey 7 :=
  ⟨![376320, 262080, 268800, 275520, 241920, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 261632, 268310, 274960, 241535, 60080, 254940], true⟩

theorem canonicalMatch7_1006 :
    canonicalPose7_1006.boxKey 188160 (referenceBox7 (!canonicalBox7_1006.bump)) = canonicalBox7_1006 := by decide +kernel

theorem canonicalDecode7_1006 : canonicalBox7_1006.toKeyData 188160 = keys7Chunk31.get ⟨14, by decide⟩ := by
  change canonicalBox7_1006.toKeyData 188160 = ⟨![2, (39 / 28), (10 / 7), (41 / 28), (9 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1006 : keySolid (keys7Chunk31.get ⟨14, by decide⟩) = canonicalPose7_1006.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1006 (box := canonicalBox7_1006) (k := keys7Chunk31.get ⟨14, by decide⟩) (canonicalMatch7_1006) (canonicalDecode7_1006)

def canonicalPose7_1007 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, true, true, true, false, false, false], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_1007 : BoxKey 7 :=
  ⟨![262080, 376320, 268800, 275520, 322560, 127680, 309120], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, 375760, 268310, 274960, 322945, 128080, 309540], false⟩

theorem canonicalMatch7_1007 :
    canonicalPose7_1007.boxKey 188160 (referenceBox7 (!canonicalBox7_1007.bump)) = canonicalBox7_1007 := by decide +kernel

theorem canonicalDecode7_1007 : canonicalBox7_1007.toKeyData 188160 = keys7Chunk31.get ⟨15, by decide⟩ := by
  change canonicalBox7_1007.toKeyData 188160 = ⟨![(39 / 28), 2, (10 / 7), (41 / 28), (12 / 7), (19 / 28), (23 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (671 / 336), (3833 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1007 : keySolid (keys7Chunk31.get ⟨15, by decide⟩) = canonicalPose7_1007.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1007 (box := canonicalBox7_1007) (k := keys7Chunk31.get ⟨15, by decide⟩) (canonicalMatch7_1007) (canonicalDecode7_1007)

def canonicalPose7_1008 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, true, false, true, false, false, false], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_1008 : BoxKey 7 :=
  ⟨![275520, 268800, 376320, 262080, 309120, 127680, 322560], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 268310, 376880, 261632, 309540, 128080, 322945], true⟩

theorem canonicalMatch7_1008 :
    canonicalPose7_1008.boxKey 188160 (referenceBox7 (!canonicalBox7_1008.bump)) = canonicalBox7_1008 := by decide +kernel

theorem canonicalDecode7_1008 : canonicalBox7_1008.toKeyData 188160 = keys7Chunk31.get ⟨16, by decide⟩ := by
  change canonicalBox7_1008.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), 2, (39 / 28), (23 / 14), (19 / 28), (12 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (673 / 336), (146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1008 : keySolid (keys7Chunk31.get ⟨16, by decide⟩) = canonicalPose7_1008.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1008 (box := canonicalBox7_1008) (k := keys7Chunk31.get ⟨16, by decide⟩) (canonicalMatch7_1008) (canonicalDecode7_1008)

def canonicalPose7_1009 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 2, 1, 2]⟩
def canonicalBox7_1009 : BoxKey 7 :=
  ⟨![275520, 268800, 262080, 376320, 255360, 60480, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 261632, 375760, 254940, 60080, 241535], false⟩

theorem canonicalMatch7_1009 :
    canonicalPose7_1009.boxKey 188160 (referenceBox7 (!canonicalBox7_1009.bump)) = canonicalBox7_1009 := by decide +kernel

theorem canonicalDecode7_1009 : canonicalBox7_1009.toKeyData 188160 = keys7Chunk31.get ⟨17, by decide⟩ := by
  change canonicalBox7_1009.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (39 / 28), 2, (19 / 14), (9 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (607 / 448), (751 / 2352), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1009 : keySolid (keys7Chunk31.get ⟨17, by decide⟩) = canonicalPose7_1009.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1009 (box := canonicalBox7_1009) (k := keys7Chunk31.get ⟨17, by decide⟩) (canonicalMatch7_1009) (canonicalDecode7_1009)

def canonicalPose7_1010 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, false, true, true, false, true], ![2, 1, 1, 2, 2, 0, 2]⟩
def canonicalBox7_1010 : BoxKey 7 :=
  ⟨![275520, 322560, 315840, 255360, 376320, 114240, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 322945, 316240, 254940, 375760, 114688, 268310], false⟩

theorem canonicalMatch7_1010 :
    canonicalPose7_1010.boxKey 188160 (referenceBox7 (!canonicalBox7_1010.bump)) = canonicalBox7_1010 := by decide +kernel

theorem canonicalDecode7_1010 : canonicalBox7_1010.toKeyData 188160 = keys7Chunk31.get ⟨18, by decide⟩ := by
  change canonicalBox7_1010.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (47 / 28), (19 / 14), 2, (17 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1010 : keySolid (keys7Chunk31.get ⟨18, by decide⟩) = canonicalPose7_1010.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1010 (box := canonicalBox7_1010) (k := keys7Chunk31.get ⟨18, by decide⟩) (canonicalMatch7_1010) (canonicalDecode7_1010)

def canonicalPose7_1011 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, true, false, false, false], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_1011 : BoxKey 7 :=
  ⟨![268800, 275520, 241920, 248640, 309120, 0, 302400], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 241535, 248240, 309540, 560, 302848], false⟩

theorem canonicalMatch7_1011 :
    canonicalPose7_1011.boxKey 188160 (referenceBox7 (!canonicalBox7_1011.bump)) = canonicalBox7_1011 := by decide +kernel

theorem canonicalDecode7_1011 : canonicalBox7_1011.toKeyData 188160 = keys7Chunk31.get ⟨19, by decide⟩ := by
  change canonicalBox7_1011.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (9 / 7), (37 / 28), (23 / 14), 0, (45 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (737 / 448), (1 / 336), (169 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1011 : keySolid (keys7Chunk31.get ⟨19, by decide⟩) = canonicalPose7_1011.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1011 (box := canonicalBox7_1011) (k := keys7Chunk31.get ⟨19, by decide⟩) (canonicalMatch7_1011) (canonicalDecode7_1011)

def canonicalPose7_1012 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, true, false, true, false], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_1012 : BoxKey 7 :=
  ⟨![248640, 241920, 275520, 268800, 302400, 0, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 241535, 274960, 268310, 302848, -560, 309540], true⟩

theorem canonicalMatch7_1012 :
    canonicalPose7_1012.boxKey 188160 (referenceBox7 (!canonicalBox7_1012.bump)) = canonicalBox7_1012 := by decide +kernel

theorem canonicalDecode7_1012 : canonicalBox7_1012.toKeyData 188160 = keys7Chunk31.get ⟨20, by decide⟩ := by
  change canonicalBox7_1012.toKeyData 188160 = ⟨![(37 / 28), (9 / 7), (41 / 28), (10 / 7), (45 / 28), 0, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (169 / 105), (-1 / 336), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1012 : keySolid (keys7Chunk31.get ⟨20, by decide⟩) = canonicalPose7_1012.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1012 (box := canonicalBox7_1012) (k := keys7Chunk31.get ⟨20, by decide⟩) (canonicalMatch7_1012) (canonicalDecode7_1012)

def canonicalPose7_1013 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, false, false, false, false], ![2, 1, 1, 1, 1, 1, 1]⟩
def canonicalBox7_1013 : BoxKey 7 :=
  ⟨![248640, 322560, 288960, 295680, 302400, 188160, 309120], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 322945, 289520, 296170, 302848, 188720, 309540], true⟩

theorem canonicalMatch7_1013 :
    canonicalPose7_1013.boxKey 188160 (referenceBox7 (!canonicalBox7_1013.bump)) = canonicalBox7_1013 := by decide +kernel

theorem canonicalDecode7_1013 : canonicalBox7_1013.toKeyData 188160 = keys7Chunk31.get ⟨21, by decide⟩ := by
  change canonicalBox7_1013.toKeyData 188160 = ⟨![(37 / 28), (12 / 7), (43 / 28), (11 / 7), (45 / 28), 1, (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (9227 / 5376), (517 / 336), (4231 / 2688), (169 / 105), (337 / 336), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1013 : keySolid (keys7Chunk31.get ⟨21, by decide⟩) = canonicalPose7_1013.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1013 (box := canonicalBox7_1013) (k := keys7Chunk31.get ⟨21, by decide⟩) (canonicalMatch7_1013) (canonicalDecode7_1013)

def canonicalPose7_1014 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, false, true, true, false, false], ![2, 1, 1, 2, 2, 0, 2]⟩
def canonicalBox7_1014 : BoxKey 7 :=
  ⟨![255360, 315840, 322560, 275520, 268800, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 316240, 322945, 274960, 268310, 114688, 376880], true⟩

theorem canonicalMatch7_1014 :
    canonicalPose7_1014.boxKey 188160 (referenceBox7 (!canonicalBox7_1014.bump)) = canonicalBox7_1014 := by decide +kernel

theorem canonicalDecode7_1014 : canonicalBox7_1014.toKeyData 188160 = keys7Chunk31.get ⟨22, by decide⟩ := by
  change canonicalBox7_1014.toKeyData 188160 = ⟨![(19 / 14), (47 / 28), (12 / 7), (41 / 28), (10 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1014 : keySolid (keys7Chunk31.get ⟨22, by decide⟩) = canonicalPose7_1014.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1014 (box := canonicalBox7_1014) (k := keys7Chunk31.get ⟨22, by decide⟩) (canonicalMatch7_1014) (canonicalDecode7_1014)

def canonicalPose7_1015 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, false, false, true, true, false], ![2, 2, 1, 1, 2, 2, 0]⟩
def canonicalBox7_1015 : BoxKey 7 :=
  ⟨![376320, 255360, 315840, 322560, 275520, 268800, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 254940, 316240, 322945, 274960, 268310, 114688], true⟩

theorem canonicalMatch7_1015 :
    canonicalPose7_1015.boxKey 188160 (referenceBox7 (!canonicalBox7_1015.bump)) = canonicalBox7_1015 := by decide +kernel

theorem canonicalDecode7_1015 : canonicalBox7_1015.toKeyData 188160 = keys7Chunk31.get ⟨23, by decide⟩ := by
  change canonicalBox7_1015.toKeyData 188160 = ⟨![2, (19 / 14), (47 / 28), (12 / 7), (41 / 28), (10 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1015 : keySolid (keys7Chunk31.get ⟨23, by decide⟩) = canonicalPose7_1015.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1015 (box := canonicalBox7_1015) (k := keys7Chunk31.get ⟨23, by decide⟩) (canonicalMatch7_1015) (canonicalDecode7_1015)

def canonicalPose7_1016 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, true, true, true, true], ![2, 2, 2, 2, 2, 2, 1]⟩
def canonicalBox7_1016 : BoxKey 7 :=
  ⟨![255360, 376320, 262080, 268800, 275520, 241920, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 376880, 261632, 268310, 274960, 241535, 60080], true⟩

theorem canonicalMatch7_1016 :
    canonicalPose7_1016.boxKey 188160 (referenceBox7 (!canonicalBox7_1016.bump)) = canonicalBox7_1016 := by decide +kernel

theorem canonicalDecode7_1016 : canonicalBox7_1016.toKeyData 188160 = keys7Chunk31.get ⟨24, by decide⟩ := by
  change canonicalBox7_1016.toKeyData 188160 = ⟨![(19 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (9 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1016 : keySolid (keys7Chunk31.get ⟨24, by decide⟩) = canonicalPose7_1016.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1016 (box := canonicalBox7_1016) (k := keys7Chunk31.get ⟨24, by decide⟩) (canonicalMatch7_1016) (canonicalDecode7_1016)

def canonicalPose7_1017 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, true, true, true, true, false, false], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_1017 : BoxKey 7 :=
  ⟨![309120, 262080, 376320, 268800, 275520, 322560, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 261632, 375760, 268310, 274960, 322945, 128080], false⟩

theorem canonicalMatch7_1017 :
    canonicalPose7_1017.boxKey 188160 (referenceBox7 (!canonicalBox7_1017.bump)) = canonicalBox7_1017 := by decide +kernel

theorem canonicalDecode7_1017 : canonicalBox7_1017.toKeyData 188160 = keys7Chunk31.get ⟨25, by decide⟩ := by
  change canonicalBox7_1017.toKeyData 188160 = ⟨![(23 / 14), (39 / 28), 2, (10 / 7), (41 / 28), (12 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (146 / 105), (671 / 336), (3833 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1017 : keySolid (keys7Chunk31.get ⟨25, by decide⟩) = canonicalPose7_1017.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1017 (box := canonicalBox7_1017) (k := keys7Chunk31.get ⟨25, by decide⟩) (canonicalMatch7_1017) (canonicalDecode7_1017)

def canonicalPose7_1018 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, true, true, false, true, false, false], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_1018 : BoxKey 7 :=
  ⟨![322560, 275520, 268800, 376320, 262080, 309120, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 274960, 268310, 376880, 261632, 309540, 128080], true⟩

theorem canonicalMatch7_1018 :
    canonicalPose7_1018.boxKey 188160 (referenceBox7 (!canonicalBox7_1018.bump)) = canonicalBox7_1018 := by decide +kernel

theorem canonicalDecode7_1018 : canonicalBox7_1018.toKeyData 188160 = keys7Chunk31.get ⟨26, by decide⟩ := by
  change canonicalBox7_1018.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (10 / 7), 2, (39 / 28), (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (3833 / 2688), (673 / 336), (146 / 105), (737 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1018 : keySolid (keys7Chunk31.get ⟨26, by decide⟩) = canonicalPose7_1018.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1018 (box := canonicalBox7_1018) (k := keys7Chunk31.get ⟨26, by decide⟩) (canonicalMatch7_1018) (canonicalDecode7_1018)

def canonicalPose7_1019 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 2, 2, 1]⟩
def canonicalBox7_1019 : BoxKey 7 :=
  ⟨![241920, 275520, 268800, 262080, 376320, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 268310, 261632, 375760, 254940, 60080], false⟩

theorem canonicalMatch7_1019 :
    canonicalPose7_1019.boxKey 188160 (referenceBox7 (!canonicalBox7_1019.bump)) = canonicalBox7_1019 := by decide +kernel

theorem canonicalDecode7_1019 : canonicalBox7_1019.toKeyData 188160 = keys7Chunk31.get ⟨27, by decide⟩ := by
  change canonicalBox7_1019.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (607 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1019 : keySolid (keys7Chunk31.get ⟨27, by decide⟩) = canonicalPose7_1019.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1019 (box := canonicalBox7_1019) (k := keys7Chunk31.get ⟨27, by decide⟩) (canonicalMatch7_1019) (canonicalDecode7_1019)

def canonicalPose7_1020 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, false, false, true, true, false], ![2, 2, 1, 1, 2, 2, 0]⟩
def canonicalBox7_1020 : BoxKey 7 :=
  ⟨![268800, 275520, 322560, 315840, 255360, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 322945, 316240, 254940, 375760, 114688], false⟩

theorem canonicalMatch7_1020 :
    canonicalPose7_1020.boxKey 188160 (referenceBox7 (!canonicalBox7_1020.bump)) = canonicalBox7_1020 := by decide +kernel

theorem canonicalDecode7_1020 : canonicalBox7_1020.toKeyData 188160 = keys7Chunk31.get ⟨28, by decide⟩ := by
  change canonicalBox7_1020.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1020 : keySolid (keys7Chunk31.get ⟨28, by decide⟩) = canonicalPose7_1020.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1020 (box := canonicalBox7_1020) (k := keys7Chunk31.get ⟨28, by decide⟩) (canonicalMatch7_1020) (canonicalDecode7_1020)

def canonicalPose7_1021 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, true, true, true, false, false], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_1021 : BoxKey 7 :=
  ⟨![302400, 268800, 275520, 241920, 248640, 309120, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 268310, 274960, 241535, 248240, 309540, 560], false⟩

theorem canonicalMatch7_1021 :
    canonicalPose7_1021.boxKey 188160 (referenceBox7 (!canonicalBox7_1021.bump)) = canonicalBox7_1021 := by decide +kernel

theorem canonicalDecode7_1021 : canonicalBox7_1021.toKeyData 188160 = keys7Chunk31.get ⟨29, by decide⟩ := by
  change canonicalBox7_1021.toKeyData 188160 = ⟨![(45 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28), (23 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (737 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1021 : keySolid (keys7Chunk31.get ⟨29, by decide⟩) = canonicalPose7_1021.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1021 (box := canonicalBox7_1021) (k := keys7Chunk31.get ⟨29, by decide⟩) (canonicalMatch7_1021) (canonicalDecode7_1021)

def canonicalPose7_1022 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, true, true, true, true, false, true], ![1, 2, 2, 2, 2, 1, 0]⟩
def canonicalBox7_1022 : BoxKey 7 :=
  ⟨![309120, 248640, 241920, 275520, 268800, 302400, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 248240, 241535, 274960, 268310, 302848, -560], true⟩

theorem canonicalMatch7_1022 :
    canonicalPose7_1022.boxKey 188160 (referenceBox7 (!canonicalBox7_1022.bump)) = canonicalBox7_1022 := by decide +kernel

theorem canonicalDecode7_1022 : canonicalBox7_1022.toKeyData 188160 = keys7Chunk31.get ⟨30, by decide⟩ := by
  change canonicalBox7_1022.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7), (45 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (169 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1022 : keySolid (keys7Chunk31.get ⟨30, by decide⟩) = canonicalPose7_1022.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1022 (box := canonicalBox7_1022) (k := keys7Chunk31.get ⟨30, by decide⟩) (canonicalMatch7_1022) (canonicalDecode7_1022)

def canonicalPose7_1023 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, false, true, true, false, false], ![1, 1, 1, 2, 2, 1, 1]⟩
def canonicalBox7_1023 : BoxKey 7 :=
  ⟨![302400, 295680, 288960, 241920, 248640, 309120, 188160], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 296170, 289520, 241535, 248240, 309540, 188720], true⟩

theorem canonicalMatch7_1023 :
    canonicalPose7_1023.boxKey 188160 (referenceBox7 (!canonicalBox7_1023.bump)) = canonicalBox7_1023 := by decide +kernel

theorem canonicalDecode7_1023 : canonicalBox7_1023.toKeyData 188160 = keys7Chunk31.get ⟨31, by decide⟩ := by
  change canonicalBox7_1023.toKeyData 188160 = ⟨![(45 / 28), (11 / 7), (43 / 28), (9 / 7), (37 / 28), (23 / 14), 1], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (4231 / 2688), (517 / 336), (6901 / 5376), (3103 / 2352), (737 / 448), (337 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_1023 : keySolid (keys7Chunk31.get ⟨31, by decide⟩) = canonicalPose7_1023.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_1023 (box := canonicalBox7_1023) (k := keys7Chunk31.get ⟨31, by decide⟩) (canonicalMatch7_1023) (canonicalDecode7_1023)

theorem keys7Chunk31_canonical : ∀ k ∈ keys7Chunk31,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk31, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_992, canonicalSolid7_992⟩
  · exact ⟨canonicalPose7_993, canonicalSolid7_993⟩
  · exact ⟨canonicalPose7_994, canonicalSolid7_994⟩
  · exact ⟨canonicalPose7_995, canonicalSolid7_995⟩
  · exact ⟨canonicalPose7_996, canonicalSolid7_996⟩
  · exact ⟨canonicalPose7_997, canonicalSolid7_997⟩
  · exact ⟨canonicalPose7_998, canonicalSolid7_998⟩
  · exact ⟨canonicalPose7_999, canonicalSolid7_999⟩
  · exact ⟨canonicalPose7_1000, canonicalSolid7_1000⟩
  · exact ⟨canonicalPose7_1001, canonicalSolid7_1001⟩
  · exact ⟨canonicalPose7_1002, canonicalSolid7_1002⟩
  · exact ⟨canonicalPose7_1003, canonicalSolid7_1003⟩
  · exact ⟨canonicalPose7_1004, canonicalSolid7_1004⟩
  · exact ⟨canonicalPose7_1005, canonicalSolid7_1005⟩
  · exact ⟨canonicalPose7_1006, canonicalSolid7_1006⟩
  · exact ⟨canonicalPose7_1007, canonicalSolid7_1007⟩
  · exact ⟨canonicalPose7_1008, canonicalSolid7_1008⟩
  · exact ⟨canonicalPose7_1009, canonicalSolid7_1009⟩
  · exact ⟨canonicalPose7_1010, canonicalSolid7_1010⟩
  · exact ⟨canonicalPose7_1011, canonicalSolid7_1011⟩
  · exact ⟨canonicalPose7_1012, canonicalSolid7_1012⟩
  · exact ⟨canonicalPose7_1013, canonicalSolid7_1013⟩
  · exact ⟨canonicalPose7_1014, canonicalSolid7_1014⟩
  · exact ⟨canonicalPose7_1015, canonicalSolid7_1015⟩
  · exact ⟨canonicalPose7_1016, canonicalSolid7_1016⟩
  · exact ⟨canonicalPose7_1017, canonicalSolid7_1017⟩
  · exact ⟨canonicalPose7_1018, canonicalSolid7_1018⟩
  · exact ⟨canonicalPose7_1019, canonicalSolid7_1019⟩
  · exact ⟨canonicalPose7_1020, canonicalSolid7_1020⟩
  · exact ⟨canonicalPose7_1021, canonicalSolid7_1021⟩
  · exact ⟨canonicalPose7_1022, canonicalSolid7_1022⟩
  · exact ⟨canonicalPose7_1023, canonicalSolid7_1023⟩

#print axioms keys7Chunk31_canonical

end SparseMonotiles.Canonical
