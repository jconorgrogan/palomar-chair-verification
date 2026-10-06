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

def canonicalPose7_960 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, false, false, false, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_960 : BoxKey 7 :=
  ⟨![241920, 248640, 309120, 0, 302400, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 248240, 309540, 560, 302848, 268310, 274960], false⟩

theorem canonicalMatch7_960 :
    canonicalPose7_960.boxKey 188160 (referenceBox7 (!canonicalBox7_960.bump)) = canonicalBox7_960 := by decide +kernel

theorem canonicalDecode7_960 : canonicalBox7_960.toKeyData 188160 = keys7Chunk30.get ⟨0, by decide⟩ := by
  change canonicalBox7_960.toKeyData 188160 = ⟨![(9 / 7), (37 / 28), (23 / 14), 0, (45 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (3103 / 2352), (737 / 448), (1 / 336), (169 / 105), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_960 : keySolid (keys7Chunk30.get ⟨0, by decide⟩) = canonicalPose7_960.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_960 (box := canonicalBox7_960) (k := keys7Chunk30.get ⟨0, by decide⟩) (canonicalMatch7_960) (canonicalDecode7_960)

def canonicalPose7_961 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, true, false, false, false, false, true], ![1, 2, 1, 1, 1, 1, 2]⟩
def canonicalBox7_961 : BoxKey 7 :=
  ⟨![315840, 255360, 302400, 188160, 295680, 288960, 241920], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![316240, 254940, 302848, 188720, 296170, 289520, 241535], true⟩

theorem canonicalMatch7_961 :
    canonicalPose7_961.boxKey 188160 (referenceBox7 (!canonicalBox7_961.bump)) = canonicalBox7_961 := by decide +kernel

theorem canonicalDecode7_961 : canonicalBox7_961.toKeyData 188160 = keys7Chunk30.get ⟨1, by decide⟩ := by
  change canonicalBox7_961.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), (45 / 28), 1, (11 / 7), (43 / 28), (9 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (169 / 105), (337 / 336), (4231 / 2688), (517 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_961 : keySolid (keys7Chunk30.get ⟨1, by decide⟩) = canonicalPose7_961.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_961 (box := canonicalBox7_961) (k := keys7Chunk30.get ⟨1, by decide⟩) (canonicalMatch7_961) (canonicalDecode7_961)

def canonicalPose7_962 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, true, false, false, true, false], ![1, 2, 2, 0, 2, 2, 1]⟩
def canonicalBox7_962 : BoxKey 7 :=
  ⟨![322560, 275520, 268800, 114240, 376320, 255360, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![322945, 274960, 268310, 114688, 376880, 254940, 316240], true⟩

theorem canonicalMatch7_962 :
    canonicalPose7_962.boxKey 188160 (referenceBox7 (!canonicalBox7_962.bump)) = canonicalBox7_962 := by decide +kernel

theorem canonicalDecode7_962 : canonicalBox7_962.toKeyData 188160 = keys7Chunk30.get ⟨2, by decide⟩ := by
  change canonicalBox7_962.toKeyData 188160 = ⟨![(12 / 7), (41 / 28), (10 / 7), (17 / 28), 2, (19 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(9227 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_962 : keySolid (keys7Chunk30.get ⟨2, by decide⟩) = canonicalPose7_962.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_962 (box := canonicalBox7_962) (k := keys7Chunk30.get ⟨2, by decide⟩) (canonicalMatch7_962) (canonicalDecode7_962)

def canonicalPose7_963 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, true, true, false, true], ![2, 2, 2, 1, 2, 2, 2]⟩
def canonicalBox7_963 : BoxKey 7 :=
  ⟨![268800, 275520, 241920, 60480, 255360, 376320, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 241535, 60080, 254940, 376880, 261632], true⟩

theorem canonicalMatch7_963 :
    canonicalPose7_963.boxKey 188160 (referenceBox7 (!canonicalBox7_963.bump)) = canonicalBox7_963 := by decide +kernel

theorem canonicalDecode7_963 : canonicalBox7_963.toKeyData 188160 = keys7Chunk30.get ⟨3, by decide⟩ := by
  change canonicalBox7_963.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (9 / 7), (9 / 28), (19 / 14), 2, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (607 / 448), (673 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_963 : keySolid (keys7Chunk30.get ⟨3, by decide⟩) = canonicalPose7_963.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_963 (box := canonicalBox7_963) (k := keys7Chunk30.get ⟨3, by decide⟩) (canonicalMatch7_963) (canonicalDecode7_963)

def canonicalPose7_964 : Pose 7 :=
  ⟨canonicalPerm7_4, ![true, true, false, false, false, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_964 : BoxKey 7 :=
  ⟨![268800, 275520, 322560, 127680, 309120, 262080, 376320], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![268310, 274960, 322945, 128080, 309540, 261632, 375760], false⟩

theorem canonicalMatch7_964 :
    canonicalPose7_964.boxKey 188160 (referenceBox7 (!canonicalBox7_964.bump)) = canonicalBox7_964 := by decide +kernel

theorem canonicalDecode7_964 : canonicalBox7_964.toKeyData 188160 = keys7Chunk30.get ⟨4, by decide⟩ := by
  change canonicalBox7_964.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (12 / 7), (19 / 28), (23 / 14), (39 / 28), 2], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(3833 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_964 : keySolid (keys7Chunk30.get ⟨4, by decide⟩) = canonicalPose7_964.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_964 (box := canonicalBox7_964) (k := keys7Chunk30.get ⟨4, by decide⟩) (canonicalMatch7_964) (canonicalDecode7_964)

def canonicalPose7_965 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, true, false, true, false], ![2, 2, 2, 2, 0, 1, 0]⟩
def canonicalBox7_965 : BoxKey 7 :=
  ⟨![376320, 262080, 268800, 275520, 134400, 60480, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 261632, 268310, 274960, 134785, 60080, 121380], true⟩

theorem canonicalMatch7_965 :
    canonicalPose7_965.boxKey 188160 (referenceBox7 (!canonicalBox7_965.bump)) = canonicalBox7_965 := by decide +kernel

theorem canonicalDecode7_965 : canonicalBox7_965.toKeyData 188160 = keys7Chunk30.get ⟨5, by decide⟩ := by
  change canonicalBox7_965.toKeyData 188160 = ⟨![2, (39 / 28), (10 / 7), (41 / 28), (5 / 7), (9 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376), (751 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_965 : keySolid (keys7Chunk30.get ⟨5, by decide⟩) = canonicalPose7_965.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_965 (box := canonicalBox7_965) (k := keys7Chunk30.get ⟨5, by decide⟩) (canonicalMatch7_965) (canonicalDecode7_965)

def canonicalPose7_966 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, true, true, true, true, false, true], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_966 : BoxKey 7 :=
  ⟨![262080, 376320, 268800, 275520, 53760, 127680, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, 375760, 268310, 274960, 53375, 128080, 66780], false⟩

theorem canonicalMatch7_966 :
    canonicalPose7_966.boxKey 188160 (referenceBox7 (!canonicalBox7_966.bump)) = canonicalBox7_966 := by decide +kernel

theorem canonicalDecode7_966 : canonicalBox7_966.toKeyData 188160 = keys7Chunk30.get ⟨6, by decide⟩ := by
  change canonicalBox7_966.toKeyData 188160 = ⟨![(39 / 28), 2, (10 / 7), (41 / 28), (2 / 7), (19 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (671 / 336), (3833 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_966 : keySolid (keys7Chunk30.get ⟨6, by decide⟩) = canonicalPose7_966.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_966 (box := canonicalBox7_966) (k := keys7Chunk30.get ⟨6, by decide⟩) (canonicalMatch7_966) (canonicalDecode7_966)

def canonicalPose7_967 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, true, false, true, true, false, true], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_967 : BoxKey 7 :=
  ⟨![275520, 268800, 376320, 262080, 67200, 127680, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 268310, 376880, 261632, 66780, 128080, 53375], true⟩

theorem canonicalMatch7_967 :
    canonicalPose7_967.boxKey 188160 (referenceBox7 (!canonicalBox7_967.bump)) = canonicalBox7_967 := by decide +kernel

theorem canonicalDecode7_967 : canonicalBox7_967.toKeyData 188160 = keys7Chunk30.get ⟨7, by decide⟩ := by
  change canonicalBox7_967.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), 2, (39 / 28), (5 / 14), (19 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (673 / 336), (146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_967 : keySolid (keys7Chunk30.get ⟨7, by decide⟩) = canonicalPose7_967.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_967 (box := canonicalBox7_967) (k := keys7Chunk30.get ⟨7, by decide⟩) (canonicalMatch7_967) (canonicalDecode7_967)

def canonicalPose7_968 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, true, true, false, true, false], ![2, 2, 2, 2, 0, 1, 0]⟩
def canonicalBox7_968 : BoxKey 7 :=
  ⟨![275520, 268800, 262080, 376320, 120960, 60480, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 261632, 375760, 121380, 60080, 134785], false⟩

theorem canonicalMatch7_968 :
    canonicalPose7_968.boxKey 188160 (referenceBox7 (!canonicalBox7_968.bump)) = canonicalBox7_968 := by decide +kernel

theorem canonicalDecode7_968 : canonicalBox7_968.toKeyData 188160 = keys7Chunk30.get ⟨8, by decide⟩ := by
  change canonicalBox7_968.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (9 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (751 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_968 : keySolid (keys7Chunk30.get ⟨8, by decide⟩) = canonicalPose7_968.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_968 (box := canonicalBox7_968) (k := keys7Chunk30.get ⟨8, by decide⟩) (canonicalMatch7_968) (canonicalDecode7_968)

def canonicalPose7_969 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, false, true, false, false, false], ![2, 1, 1, 2, 0, 0, 0]⟩
def canonicalBox7_969 : BoxKey 7 :=
  ⟨![275520, 322560, 315840, 255360, 0, 114240, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 322945, 316240, 254940, 560, 114688, 108010], false⟩

theorem canonicalMatch7_969 :
    canonicalPose7_969.boxKey 188160 (referenceBox7 (!canonicalBox7_969.bump)) = canonicalBox7_969 := by decide +kernel

theorem canonicalDecode7_969 : canonicalBox7_969.toKeyData 188160 = keys7Chunk30.get ⟨9, by decide⟩ := by
  change canonicalBox7_969.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (47 / 28), (19 / 14), 0, (17 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_969 : keySolid (keys7Chunk30.get ⟨9, by decide⟩) = canonicalPose7_969.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_969 (box := canonicalBox7_969) (k := keys7Chunk30.get ⟨9, by decide⟩) (canonicalMatch7_969) (canonicalDecode7_969)

def canonicalPose7_970 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, true, true, false, true], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_970 : BoxKey 7 :=
  ⟨![268800, 275520, 241920, 248640, 67200, 0, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 241535, 248240, 66780, 560, 73472], false⟩

theorem canonicalMatch7_970 :
    canonicalPose7_970.boxKey 188160 (referenceBox7 (!canonicalBox7_970.bump)) = canonicalBox7_970 := by decide +kernel

theorem canonicalDecode7_970 : canonicalBox7_970.toKeyData 188160 = keys7Chunk30.get ⟨10, by decide⟩ := by
  change canonicalBox7_970.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (9 / 7), (37 / 28), (5 / 14), 0, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448), (1 / 336), (41 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_970 : keySolid (keys7Chunk30.get ⟨10, by decide⟩) = canonicalPose7_970.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_970 (box := canonicalBox7_970) (k := keys7Chunk30.get ⟨10, by decide⟩) (canonicalMatch7_970) (canonicalDecode7_970)

def canonicalPose7_971 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 1, 0, 1]⟩
def canonicalBox7_971 : BoxKey 7 :=
  ⟨![248640, 241920, 275520, 268800, 73920, 0, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 241535, 274960, 268310, 73472, -560, 66780], true⟩

theorem canonicalMatch7_971 :
    canonicalPose7_971.boxKey 188160 (referenceBox7 (!canonicalBox7_971.bump)) = canonicalBox7_971 := by decide +kernel

theorem canonicalDecode7_971 : canonicalBox7_971.toKeyData 188160 = keys7Chunk30.get ⟨11, by decide⟩ := by
  change canonicalBox7_971.toKeyData 188160 = ⟨![(37 / 28), (9 / 7), (41 / 28), (10 / 7), (11 / 28), 0, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105), (-1 / 336), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_971 : keySolid (keys7Chunk30.get ⟨11, by decide⟩) = canonicalPose7_971.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_971 (box := canonicalBox7_971) (k := keys7Chunk30.get ⟨11, by decide⟩) (canonicalMatch7_971) (canonicalDecode7_971)

def canonicalPose7_972 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, false, true, false, false, true], ![2, 1, 1, 2, 0, 0, 0]⟩
def canonicalBox7_972 : BoxKey 7 :=
  ⟨![255360, 315840, 322560, 275520, 107520, 114240, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 316240, 322945, 274960, 108010, 114688, -560], true⟩

theorem canonicalMatch7_972 :
    canonicalPose7_972.boxKey 188160 (referenceBox7 (!canonicalBox7_972.bump)) = canonicalBox7_972 := by decide +kernel

theorem canonicalDecode7_972 : canonicalBox7_972.toKeyData 188160 = keys7Chunk30.get ⟨12, by decide⟩ := by
  change canonicalBox7_972.toKeyData 188160 = ⟨![(19 / 14), (47 / 28), (12 / 7), (41 / 28), (4 / 7), (17 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_972 : keySolid (keys7Chunk30.get ⟨12, by decide⟩) = canonicalPose7_972.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_972 (box := canonicalBox7_972) (k := keys7Chunk30.get ⟨12, by decide⟩) (canonicalMatch7_972) (canonicalDecode7_972)

def canonicalPose7_973 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, true, true, true, true], ![2, 2, 2, 2, 1, 1, 2]⟩
def canonicalBox7_973 : BoxKey 7 :=
  ⟨![376320, 262080, 268800, 275520, 53760, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 261632, 268310, 274960, 53375, 60080, 254940], true⟩

theorem canonicalMatch7_973 :
    canonicalPose7_973.boxKey 188160 (referenceBox7 (!canonicalBox7_973.bump)) = canonicalBox7_973 := by decide +kernel

theorem canonicalDecode7_973 : canonicalBox7_973.toKeyData 188160 = keys7Chunk30.get ⟨13, by decide⟩ := by
  change canonicalBox7_973.toKeyData 188160 = ⟨![2, (39 / 28), (10 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_973 : keySolid (keys7Chunk30.get ⟨13, by decide⟩) = canonicalPose7_973.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_973 (box := canonicalBox7_973) (k := keys7Chunk30.get ⟨13, by decide⟩) (canonicalMatch7_973) (canonicalDecode7_973)

def canonicalPose7_974 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, true, false, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_974 : BoxKey 7 :=
  ⟨![302400, 376320, 309120, 248640, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, 375760, 309540, 248240, 134785, 101360, 268310], false⟩

theorem canonicalMatch7_974 :
    canonicalPose7_974.boxKey 188160 (referenceBox7 (!canonicalBox7_974.bump)) = canonicalBox7_974 := by decide +kernel

theorem canonicalDecode7_974 : canonicalBox7_974.toKeyData 188160 = keys7Chunk30.get ⟨14, by decide⟩ := by
  change canonicalBox7_974.toKeyData 188160 = ⟨![(45 / 28), 2, (23 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (671 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_974 : keySolid (keys7Chunk30.get ⟨14, by decide⟩) = canonicalPose7_974.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_974 (box := canonicalBox7_974) (k := keys7Chunk30.get ⟨14, by decide⟩) (canonicalMatch7_974) (canonicalDecode7_974)

def canonicalPose7_975 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, true, false, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_975 : BoxKey 7 :=
  ⟨![309120, 376320, 302400, 268800, 100800, 134400, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 376880, 302848, 268310, 101360, 134785, 248240], true⟩

theorem canonicalMatch7_975 :
    canonicalPose7_975.boxKey 188160 (referenceBox7 (!canonicalBox7_975.bump)) = canonicalBox7_975 := by decide +kernel

theorem canonicalDecode7_975 : canonicalBox7_975.toKeyData 188160 = keys7Chunk30.get ⟨15, by decide⟩ := by
  change canonicalBox7_975.toKeyData 188160 = ⟨![(23 / 14), 2, (45 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (673 / 336), (169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_975 : keySolid (keys7Chunk30.get ⟨15, by decide⟩) = canonicalPose7_975.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_975 (box := canonicalBox7_975) (k := keys7Chunk30.get ⟨15, by decide⟩) (canonicalMatch7_975) (canonicalDecode7_975)

def canonicalPose7_976 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 1, 1, 2]⟩
def canonicalBox7_976 : BoxKey 7 :=
  ⟨![268800, 262080, 376320, 255360, 60480, 53760, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 375760, 254940, 60080, 53375, 274960], false⟩

theorem canonicalMatch7_976 :
    canonicalPose7_976.boxKey 188160 (referenceBox7 (!canonicalBox7_976.bump)) = canonicalBox7_976 := by decide +kernel

theorem canonicalDecode7_976 : canonicalBox7_976.toKeyData 188160 = keys7Chunk30.get ⟨16, by decide⟩ := by
  change canonicalBox7_976.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 2, (19 / 14), (9 / 28), (2 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (671 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_976 : keySolid (keys7Chunk30.get ⟨16, by decide⟩) = canonicalPose7_976.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_976 (box := canonicalBox7_976) (k := keys7Chunk30.get ⟨16, by decide⟩) (canonicalMatch7_976) (canonicalDecode7_976)

def canonicalPose7_977 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, true, true, false, false, true], ![2, 1, 2, 2, 0, 0, 2]⟩
def canonicalBox7_977 : BoxKey 7 :=
  ⟨![241920, 315840, 255360, 376320, 114240, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 316240, 254940, 375760, 114688, 108010, 274960], false⟩

theorem canonicalMatch7_977 :
    canonicalPose7_977.boxKey 188160 (referenceBox7 (!canonicalBox7_977.bump)) = canonicalBox7_977 := by decide +kernel

theorem canonicalDecode7_977 : canonicalBox7_977.toKeyData 188160 = keys7Chunk30.get ⟨17, by decide⟩ := by
  change canonicalBox7_977.toKeyData 188160 = ⟨![(9 / 7), (47 / 28), (19 / 14), 2, (17 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (3953 / 2352), (607 / 448), (671 / 336), (64 / 105), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_977 : keySolid (keys7Chunk30.get ⟨17, by decide⟩) = canonicalPose7_977.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_977 (box := canonicalBox7_977) (k := keys7Chunk30.get ⟨17, by decide⟩) (canonicalMatch7_977) (canonicalDecode7_977)

def canonicalPose7_978 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, true, false, true, true, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_978 : BoxKey 7 :=
  ⟨![322560, 248640, 309120, 262080, 0, 107520, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 248240, 309540, 261632, -560, 108010, 274960], true⟩

theorem canonicalMatch7_978 :
    canonicalPose7_978.boxKey 188160 (referenceBox7 (!canonicalBox7_978.bump)) = canonicalBox7_978 := by decide +kernel

theorem canonicalDecode7_978 : canonicalBox7_978.toKeyData 188160 = keys7Chunk30.get ⟨18, by decide⟩ := by
  change canonicalBox7_978.toKeyData 188160 = ⟨![(12 / 7), (37 / 28), (23 / 14), (39 / 28), 0, (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (3103 / 2352), (737 / 448), (146 / 105), (-1 / 336), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_978 : keySolid (keys7Chunk30.get ⟨18, by decide⟩) = canonicalPose7_978.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_978 (box := canonicalBox7_978) (k := keys7Chunk30.get ⟨18, by decide⟩) (canonicalMatch7_978) (canonicalDecode7_978)

def canonicalPose7_979 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, true, false, true, false, false, true], ![1, 2, 1, 2, 0, 0, 2]⟩
def canonicalBox7_979 : BoxKey 7 :=
  ⟨![309120, 248640, 322560, 275520, 107520, 0, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 248240, 322945, 274960, 108010, 560, 261632], false⟩

theorem canonicalMatch7_979 :
    canonicalPose7_979.boxKey 188160 (referenceBox7 (!canonicalBox7_979.bump)) = canonicalBox7_979 := by decide +kernel

theorem canonicalDecode7_979 : canonicalBox7_979.toKeyData 188160 = keys7Chunk30.get ⟨19, by decide⟩ := by
  change canonicalBox7_979.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (12 / 7), (41 / 28), (4 / 7), 0, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (1 / 336), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_979 : keySolid (keys7Chunk30.get ⟨19, by decide⟩) = canonicalPose7_979.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_979 (box := canonicalBox7_979) (k := keys7Chunk30.get ⟨19, by decide⟩) (canonicalMatch7_979) (canonicalDecode7_979)

def canonicalPose7_980 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, true, true, false, false, false], ![2, 1, 2, 2, 0, 0, 2]⟩
def canonicalBox7_980 : BoxKey 7 :=
  ⟨![255360, 315840, 241920, 275520, 107520, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 316240, 241535, 274960, 108010, 114688, 376880], true⟩

theorem canonicalMatch7_980 :
    canonicalPose7_980.boxKey 188160 (referenceBox7 (!canonicalBox7_980.bump)) = canonicalBox7_980 := by decide +kernel

theorem canonicalDecode7_980 : canonicalBox7_980.toKeyData 188160 = keys7Chunk30.get ⟨20, by decide⟩ := by
  change canonicalBox7_980.toKeyData 188160 = ⟨![(19 / 14), (47 / 28), (9 / 7), (41 / 28), (4 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_980 : keySolid (keys7Chunk30.get ⟨20, by decide⟩) = canonicalPose7_980.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_980 (box := canonicalBox7_980) (k := keys7Chunk30.get ⟨20, by decide⟩) (canonicalMatch7_980) (canonicalDecode7_980)

def canonicalPose7_981 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, true, true, false, false, false], ![2, 2, 2, 2, 0, 1, 0]⟩
def canonicalBox7_981 : BoxKey 7 :=
  ⟨![376320, 262080, 268800, 275520, 134400, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 261632, 268310, 274960, 134785, 316240, 121380], false⟩

theorem canonicalMatch7_981 :
    canonicalPose7_981.boxKey 188160 (referenceBox7 (!canonicalBox7_981.bump)) = canonicalBox7_981 := by decide +kernel

theorem canonicalDecode7_981 : canonicalBox7_981.toKeyData 188160 = keys7Chunk30.get ⟨21, by decide⟩ := by
  change canonicalBox7_981.toKeyData 188160 = ⟨![2, (39 / 28), (10 / 7), (41 / 28), (5 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_981 : keySolid (keys7Chunk30.get ⟨21, by decide⟩) = canonicalPose7_981.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_981 (box := canonicalBox7_981) (k := keys7Chunk30.get ⟨21, by decide⟩) (canonicalMatch7_981) (canonicalDecode7_981)

def canonicalPose7_982 : Pose 7 :=
  ⟨canonicalPerm7_10, ![true, false, true, true, true, true, true], ![2, 2, 2, 2, 1, 2, 1]⟩
def canonicalBox7_982 : BoxKey 7 :=
  ⟨![262080, 376320, 268800, 275520, 53760, 248640, 67200], ![2240, 0, 1960, 1680, 3080, 2800, 2520], ![261632, 376880, 268310, 274960, 53375, 248240, 66780], true⟩

theorem canonicalMatch7_982 :
    canonicalPose7_982.boxKey 188160 (referenceBox7 (!canonicalBox7_982.bump)) = canonicalBox7_982 := by decide +kernel

theorem canonicalDecode7_982 : canonicalBox7_982.toKeyData 188160 = keys7Chunk30.get ⟨22, by decide⟩ := by
  change canonicalBox7_982.toKeyData 188160 = ⟨![(39 / 28), 2, (10 / 7), (41 / 28), (2 / 7), (37 / 28), (5 / 14)], ![(1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(146 / 105), (673 / 336), (3833 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_982 : keySolid (keys7Chunk30.get ⟨22, by decide⟩) = canonicalPose7_982.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_982 (box := canonicalBox7_982) (k := keys7Chunk30.get ⟨22, by decide⟩) (canonicalMatch7_982) (canonicalDecode7_982)

def canonicalPose7_983 : Pose 7 :=
  ⟨canonicalPerm7_1, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 1, 2, 1]⟩
def canonicalBox7_983 : BoxKey 7 :=
  ⟨![275520, 268800, 376320, 262080, 67200, 248640, 53760], ![1680, 1960, 0, 2240, 2520, 2800, 3080], ![274960, 268310, 375760, 261632, 66780, 248240, 53375], false⟩

theorem canonicalMatch7_983 :
    canonicalPose7_983.boxKey 188160 (referenceBox7 (!canonicalBox7_983.bump)) = canonicalBox7_983 := by decide +kernel

theorem canonicalDecode7_983 : canonicalBox7_983.toKeyData 188160 = keys7Chunk30.get ⟨23, by decide⟩ := by
  change canonicalBox7_983.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), 2, (39 / 28), (5 / 14), (37 / 28), (2 / 7)], ![(1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (671 / 336), (146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_983 : keySolid (keys7Chunk30.get ⟨23, by decide⟩) = canonicalPose7_983.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_983 (box := canonicalBox7_983) (k := keys7Chunk30.get ⟨23, by decide⟩) (canonicalMatch7_983) (canonicalDecode7_983)

def canonicalPose7_984 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, true, false, false, false, false], ![2, 2, 2, 2, 0, 1, 0]⟩
def canonicalBox7_984 : BoxKey 7 :=
  ⟨![275520, 268800, 262080, 376320, 120960, 315840, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 261632, 376880, 121380, 316240, 134785], true⟩

theorem canonicalMatch7_984 :
    canonicalPose7_984.boxKey 188160 (referenceBox7 (!canonicalBox7_984.bump)) = canonicalBox7_984 := by decide +kernel

theorem canonicalDecode7_984 : canonicalBox7_984.toKeyData 188160 = keys7Chunk30.get ⟨24, by decide⟩ := by
  change canonicalBox7_984.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (47 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (146 / 105), (673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_984 : keySolid (keys7Chunk30.get ⟨24, by decide⟩) = canonicalPose7_984.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_984 (box := canonicalBox7_984) (k := keys7Chunk30.get ⟨24, by decide⟩) (canonicalMatch7_984) (canonicalDecode7_984)

def canonicalPose7_985 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, false, true, true, true, false], ![2, 1, 1, 2, 0, 2, 0]⟩
def canonicalBox7_985 : BoxKey 7 :=
  ⟨![275520, 322560, 315840, 255360, 0, 262080, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 322945, 316240, 254940, -560, 261632, 108010], true⟩

theorem canonicalMatch7_985 :
    canonicalPose7_985.boxKey 188160 (referenceBox7 (!canonicalBox7_985.bump)) = canonicalBox7_985 := by decide +kernel

theorem canonicalDecode7_985 : canonicalBox7_985.toKeyData 188160 = keys7Chunk30.get ⟨25, by decide⟩ := by
  change canonicalBox7_985.toKeyData 188160 = ⟨![(41 / 28), (12 / 7), (47 / 28), (19 / 14), 0, (39 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (-1 / 336), (146 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_985 : keySolid (keys7Chunk30.get ⟨25, by decide⟩) = canonicalPose7_985.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_985 (box := canonicalBox7_985) (k := keys7Chunk30.get ⟨25, by decide⟩) (canonicalMatch7_985) (canonicalDecode7_985)

def canonicalPose7_986 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, true, true, true, true, false, true], ![2, 2, 2, 2, 1, 2, 1]⟩
def canonicalBox7_986 : BoxKey 7 :=
  ⟨![268800, 275520, 241920, 248640, 67200, 376320, 73920], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 274960, 241535, 248240, 66780, 376880, 73472], true⟩

theorem canonicalMatch7_986 :
    canonicalPose7_986.boxKey 188160 (referenceBox7 (!canonicalBox7_986.bump)) = canonicalBox7_986 := by decide +kernel

theorem canonicalDecode7_986 : canonicalBox7_986.toKeyData 188160 = keys7Chunk30.get ⟨26, by decide⟩ := by
  change canonicalBox7_986.toKeyData 188160 = ⟨![(10 / 7), (41 / 28), (9 / 7), (37 / 28), (5 / 14), 2, (11 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448), (673 / 336), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_986 : keySolid (keys7Chunk30.get ⟨26, by decide⟩) = canonicalPose7_986.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_986 (box := canonicalBox7_986) (k := keys7Chunk30.get ⟨26, by decide⟩) (canonicalMatch7_986) (canonicalDecode7_986)

def canonicalPose7_987 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 1, 2, 1]⟩
def canonicalBox7_987 : BoxKey 7 :=
  ⟨![248640, 241920, 275520, 268800, 73920, 376320, 67200], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![248240, 241535, 274960, 268310, 73472, 375760, 66780], false⟩

theorem canonicalMatch7_987 :
    canonicalPose7_987.boxKey 188160 (referenceBox7 (!canonicalBox7_987.bump)) = canonicalBox7_987 := by decide +kernel

theorem canonicalDecode7_987 : canonicalBox7_987.toKeyData 188160 = keys7Chunk30.get ⟨27, by decide⟩ := by
  change canonicalBox7_987.toKeyData 188160 = ⟨![(37 / 28), (9 / 7), (41 / 28), (10 / 7), (11 / 28), 2, (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105), (671 / 336), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_987 : keySolid (keys7Chunk30.get ⟨27, by decide⟩) = canonicalPose7_987.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_987 (box := canonicalBox7_987) (k := keys7Chunk30.get ⟨27, by decide⟩) (canonicalMatch7_987) (canonicalDecode7_987)

def canonicalPose7_988 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, false, true, false, true, false], ![2, 1, 1, 2, 0, 2, 0]⟩
def canonicalBox7_988 : BoxKey 7 :=
  ⟨![255360, 315840, 322560, 275520, 107520, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 316240, 322945, 274960, 108010, 261632, 560], false⟩

theorem canonicalMatch7_988 :
    canonicalPose7_988.boxKey 188160 (referenceBox7 (!canonicalBox7_988.bump)) = canonicalBox7_988 := by decide +kernel

theorem canonicalDecode7_988 : canonicalBox7_988.toKeyData 188160 = keys7Chunk30.get ⟨28, by decide⟩ := by
  change canonicalBox7_988.toKeyData 188160 = ⟨![(19 / 14), (47 / 28), (12 / 7), (41 / 28), (4 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_988 : keySolid (keys7Chunk30.get ⟨28, by decide⟩) = canonicalPose7_988.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_988 (box := canonicalBox7_988) (k := keys7Chunk30.get ⟨28, by decide⟩) (canonicalMatch7_988) (canonicalDecode7_988)

def canonicalPose7_989 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, true, true, false, false, false, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_989 : BoxKey 7 :=
  ⟨![376320, 268800, 275520, 322560, 127680, 309120, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![375760, 268310, 274960, 322945, 128080, 309540, 261632], false⟩

theorem canonicalMatch7_989 :
    canonicalPose7_989.boxKey 188160 (referenceBox7 (!canonicalBox7_989.bump)) = canonicalBox7_989 := by decide +kernel

theorem canonicalDecode7_989 : canonicalBox7_989.toKeyData 188160 = keys7Chunk30.get ⟨29, by decide⟩ := by
  change canonicalBox7_989.toKeyData 188160 = ⟨![2, (10 / 7), (41 / 28), (12 / 7), (19 / 28), (23 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(671 / 336), (3833 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_989 : keySolid (keys7Chunk30.get ⟨29, by decide⟩) = canonicalPose7_989.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_989 (box := canonicalBox7_989) (k := keys7Chunk30.get ⟨29, by decide⟩) (canonicalMatch7_989) (canonicalDecode7_989)

def canonicalPose7_990 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, false, true, false, false, false, true], ![2, 2, 2, 1, 0, 1, 2]⟩
def canonicalBox7_990 : BoxKey 7 :=
  ⟨![268800, 376320, 262080, 309120, 127680, 322560, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 376880, 261632, 309540, 128080, 322945, 274960], true⟩

theorem canonicalMatch7_990 :
    canonicalPose7_990.boxKey 188160 (referenceBox7 (!canonicalBox7_990.bump)) = canonicalBox7_990 := by decide +kernel

theorem canonicalDecode7_990 : canonicalBox7_990.toKeyData 188160 = keys7Chunk30.get ⟨30, by decide⟩ := by
  change canonicalBox7_990.toKeyData 188160 = ⟨![(10 / 7), 2, (39 / 28), (23 / 14), (19 / 28), (12 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (673 / 336), (146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_990 : keySolid (keys7Chunk30.get ⟨30, by decide⟩) = canonicalPose7_990.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_990 (box := canonicalBox7_990) (k := keys7Chunk30.get ⟨30, by decide⟩) (canonicalMatch7_990) (canonicalDecode7_990)

def canonicalPose7_991 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, true, true, true, true], ![2, 2, 2, 2, 1, 2, 2]⟩
def canonicalBox7_991 : BoxKey 7 :=
  ⟨![268800, 262080, 376320, 255360, 60480, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 375760, 254940, 60080, 241535, 274960], false⟩

theorem canonicalMatch7_991 :
    canonicalPose7_991.boxKey 188160 (referenceBox7 (!canonicalBox7_991.bump)) = canonicalBox7_991 := by decide +kernel

theorem canonicalDecode7_991 : canonicalBox7_991.toKeyData 188160 = keys7Chunk30.get ⟨31, by decide⟩ := by
  change canonicalBox7_991.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 2, (19 / 14), (9 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (671 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_991 : keySolid (keys7Chunk30.get ⟨31, by decide⟩) = canonicalPose7_991.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_991 (box := canonicalBox7_991) (k := keys7Chunk30.get ⟨31, by decide⟩) (canonicalMatch7_991) (canonicalDecode7_991)

theorem keys7Chunk30_canonical : ∀ k ∈ keys7Chunk30,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk30, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_960, canonicalSolid7_960⟩
  · exact ⟨canonicalPose7_961, canonicalSolid7_961⟩
  · exact ⟨canonicalPose7_962, canonicalSolid7_962⟩
  · exact ⟨canonicalPose7_963, canonicalSolid7_963⟩
  · exact ⟨canonicalPose7_964, canonicalSolid7_964⟩
  · exact ⟨canonicalPose7_965, canonicalSolid7_965⟩
  · exact ⟨canonicalPose7_966, canonicalSolid7_966⟩
  · exact ⟨canonicalPose7_967, canonicalSolid7_967⟩
  · exact ⟨canonicalPose7_968, canonicalSolid7_968⟩
  · exact ⟨canonicalPose7_969, canonicalSolid7_969⟩
  · exact ⟨canonicalPose7_970, canonicalSolid7_970⟩
  · exact ⟨canonicalPose7_971, canonicalSolid7_971⟩
  · exact ⟨canonicalPose7_972, canonicalSolid7_972⟩
  · exact ⟨canonicalPose7_973, canonicalSolid7_973⟩
  · exact ⟨canonicalPose7_974, canonicalSolid7_974⟩
  · exact ⟨canonicalPose7_975, canonicalSolid7_975⟩
  · exact ⟨canonicalPose7_976, canonicalSolid7_976⟩
  · exact ⟨canonicalPose7_977, canonicalSolid7_977⟩
  · exact ⟨canonicalPose7_978, canonicalSolid7_978⟩
  · exact ⟨canonicalPose7_979, canonicalSolid7_979⟩
  · exact ⟨canonicalPose7_980, canonicalSolid7_980⟩
  · exact ⟨canonicalPose7_981, canonicalSolid7_981⟩
  · exact ⟨canonicalPose7_982, canonicalSolid7_982⟩
  · exact ⟨canonicalPose7_983, canonicalSolid7_983⟩
  · exact ⟨canonicalPose7_984, canonicalSolid7_984⟩
  · exact ⟨canonicalPose7_985, canonicalSolid7_985⟩
  · exact ⟨canonicalPose7_986, canonicalSolid7_986⟩
  · exact ⟨canonicalPose7_987, canonicalSolid7_987⟩
  · exact ⟨canonicalPose7_988, canonicalSolid7_988⟩
  · exact ⟨canonicalPose7_989, canonicalSolid7_989⟩
  · exact ⟨canonicalPose7_990, canonicalSolid7_990⟩
  · exact ⟨canonicalPose7_991, canonicalSolid7_991⟩

#print axioms keys7Chunk30_canonical

end SparseMonotiles.Canonical
