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

def canonicalPose7_704 : Pose 7 :=
  ⟨canonicalPerm7_2, ![true, true, true, true, true, false, true], ![2, 1, 2, 1, 2, 2, 2]⟩
def canonicalBox7_704 : BoxKey 7 :=
  ⟨![275520, 53760, 248640, 67200, 262080, 376320, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![274960, 53375, 248240, 66780, 261632, 376880, 268310], true⟩

theorem canonicalMatch7_704 :
    canonicalPose7_704.boxKey 188160 (referenceBox7 (!canonicalBox7_704.bump)) = canonicalBox7_704 := by decide +kernel

theorem canonicalDecode7_704 : canonicalBox7_704.toKeyData 188160 = keys7Chunk22.get ⟨0, by decide⟩ := by
  change canonicalBox7_704.toKeyData 188160 = ⟨![(41 / 28), (2 / 7), (37 / 28), (5 / 14), (39 / 28), 2, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105), (673 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_704 : keySolid (keys7Chunk22.get ⟨0, by decide⟩) = canonicalPose7_704.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_704 (box := canonicalBox7_704) (k := keys7Chunk22.get ⟨0, by decide⟩) (canonicalMatch7_704) (canonicalDecode7_704)

def canonicalPose7_705 : Pose 7 :=
  ⟨canonicalPerm7_9, ![true, true, true, true, true, true, true], ![2, 1, 2, 1, 2, 2, 2]⟩
def canonicalBox7_705 : BoxKey 7 :=
  ⟨![262080, 67200, 248640, 53760, 275520, 268800, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![261632, 66780, 248240, 53375, 274960, 268310, 375760], false⟩

theorem canonicalMatch7_705 :
    canonicalPose7_705.boxKey 188160 (referenceBox7 (!canonicalBox7_705.bump)) = canonicalBox7_705 := by decide +kernel

theorem canonicalDecode7_705 : canonicalBox7_705.toKeyData 188160 = keys7Chunk22.get ⟨1, by decide⟩ := by
  change canonicalBox7_705.toKeyData 188160 = ⟨![(39 / 28), (5 / 14), (37 / 28), (2 / 7), (41 / 28), (10 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_705 : keySolid (keys7Chunk22.get ⟨1, by decide⟩) = canonicalPose7_705.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_705 (box := canonicalBox7_705) (k := keys7Chunk22.get ⟨1, by decide⟩) (canonicalMatch7_705) (canonicalDecode7_705)

def canonicalPose7_706 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, false, true, false, false, true, false], ![2, 0, 2, 1, 0, 1, 0]⟩
def canonicalBox7_706 : BoxKey 7 :=
  ⟨![376320, 107520, 275520, 322560, 127680, 67200, 114240], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![376880, 108010, 274960, 322945, 128080, 66780, 114688], true⟩

theorem canonicalMatch7_706 :
    canonicalPose7_706.boxKey 188160 (referenceBox7 (!canonicalBox7_706.bump)) = canonicalBox7_706 := by decide +kernel

theorem canonicalDecode7_706 : canonicalBox7_706.toKeyData 188160 = keys7Chunk22.get ⟨2, by decide⟩ := by
  change canonicalBox7_706.toKeyData 188160 = ⟨![2, (4 / 7), (41 / 28), (12 / 7), (19 / 28), (5 / 14), (17 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(673 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (1601 / 2352), (159 / 448), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_706 : keySolid (keys7Chunk22.get ⟨2, by decide⟩) = canonicalPose7_706.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_706 (box := canonicalBox7_706) (k := keys7Chunk22.get ⟨2, by decide⟩) (canonicalMatch7_706) (canonicalDecode7_706)

def canonicalPose7_707 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, false, true, false, false, true, false], ![2, 0, 2, 1, 0, 1, 0]⟩
def canonicalBox7_707 : BoxKey 7 :=
  ⟨![268800, 0, 262080, 309120, 127680, 53760, 100800], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 560, 261632, 309540, 128080, 53375, 101360], false⟩

theorem canonicalMatch7_707 :
    canonicalPose7_707.boxKey 188160 (referenceBox7 (!canonicalBox7_707.bump)) = canonicalBox7_707 := by decide +kernel

theorem canonicalDecode7_707 : canonicalBox7_707.toKeyData 188160 = keys7Chunk22.get ⟨3, by decide⟩ := by
  change canonicalBox7_707.toKeyData 188160 = ⟨![(10 / 7), 0, (39 / 28), (23 / 14), (19 / 28), (2 / 7), (15 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (1 / 336), (146 / 105), (737 / 448), (1601 / 2352), (1525 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_707 : keySolid (keys7Chunk22.get ⟨3, by decide⟩) = canonicalPose7_707.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_707 (box := canonicalBox7_707) (k := keys7Chunk22.get ⟨3, by decide⟩) (canonicalMatch7_707) (canonicalDecode7_707)

def canonicalPose7_708 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, true, true, false, false], ![2, 0, 2, 2, 1, 0, 0]⟩
def canonicalBox7_708 : BoxKey 7 :=
  ⟨![268800, 114240, 376320, 255360, 60480, 134400, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 114688, 376880, 254940, 60080, 134785, 101360], true⟩

theorem canonicalMatch7_708 :
    canonicalPose7_708.boxKey 188160 (referenceBox7 (!canonicalBox7_708.bump)) = canonicalBox7_708 := by decide +kernel

theorem canonicalDecode7_708 : canonicalBox7_708.toKeyData 188160 = keys7Chunk22.get ⟨4, by decide⟩ := by
  change canonicalBox7_708.toKeyData 188160 = ⟨![(10 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (5 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (751 / 2352), (3851 / 5376), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_708 : keySolid (keys7Chunk22.get ⟨4, by decide⟩) = canonicalPose7_708.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_708 (box := canonicalBox7_708) (k := keys7Chunk22.get ⟨4, by decide⟩) (canonicalMatch7_708) (canonicalDecode7_708)

def canonicalPose7_709 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, true, false, false, false, false], ![1, 1, 2, 2, 0, 0, 0]⟩
def canonicalBox7_709 : BoxKey 7 :=
  ⟨![322560, 60480, 255360, 376320, 114240, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 60080, 254940, 376880, 114688, 108010, 101360], true⟩

theorem canonicalMatch7_709 :
    canonicalPose7_709.boxKey 188160 (referenceBox7 (!canonicalBox7_709.bump)) = canonicalBox7_709 := by decide +kernel

theorem canonicalDecode7_709 : canonicalBox7_709.toKeyData 188160 = keys7Chunk22.get ⟨5, by decide⟩ := by
  change canonicalBox7_709.toKeyData 188160 = ⟨![(12 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (751 / 2352), (607 / 448), (673 / 336), (64 / 105), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_709 : keySolid (keys7Chunk22.get ⟨5, by decide⟩) = canonicalPose7_709.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_709 (box := canonicalBox7_709) (k := keys7Chunk22.get ⟨5, by decide⟩) (canonicalMatch7_709) (canonicalDecode7_709)

def canonicalPose7_710 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, false, true, false, true, true, false], ![2, 0, 2, 1, 0, 1, 0]⟩
def canonicalBox7_710 : BoxKey 7 :=
  ⟨![275520, 134400, 248640, 309120, 0, 73920, 107520], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 134785, 248240, 309540, -560, 73472, 108010], true⟩

theorem canonicalMatch7_710 :
    canonicalPose7_710.boxKey 188160 (referenceBox7 (!canonicalBox7_710.bump)) = canonicalBox7_710 := by decide +kernel

theorem canonicalDecode7_710 : canonicalBox7_710.toKeyData 188160 = keys7Chunk22.get ⟨6, by decide⟩ := by
  change canonicalBox7_710.toKeyData 188160 = ⟨![(41 / 28), (5 / 7), (37 / 28), (23 / 14), 0, (11 / 28), (4 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (-1 / 336), (41 / 105), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_710 : keySolid (keys7Chunk22.get ⟨6, by decide⟩) = canonicalPose7_710.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_710 (box := canonicalBox7_710) (k := keys7Chunk22.get ⟨6, by decide⟩) (canonicalMatch7_710) (canonicalDecode7_710)

def canonicalPose7_711 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, true, false, false, true, false], ![2, 0, 2, 1, 0, 1, 0]⟩
def canonicalBox7_711 : BoxKey 7 :=
  ⟨![241920, 100800, 268800, 302400, 0, 67200, 127680], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 101360, 268310, 302848, 560, 66780, 128080], false⟩

theorem canonicalMatch7_711 :
    canonicalPose7_711.boxKey 188160 (referenceBox7 (!canonicalBox7_711.bump)) = canonicalBox7_711 := by decide +kernel

theorem canonicalDecode7_711 : canonicalBox7_711.toKeyData 188160 = keys7Chunk22.get ⟨7, by decide⟩ := by
  change canonicalBox7_711.toKeyData 188160 = ⟨![(9 / 7), (15 / 28), (10 / 7), (45 / 28), 0, (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (1 / 336), (159 / 448), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_711 : keySolid (keys7Chunk22.get ⟨7, by decide⟩) = canonicalPose7_711.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_711 (box := canonicalBox7_711) (k := keys7Chunk22.get ⟨7, by decide⟩) (canonicalMatch7_711) (canonicalDecode7_711)

def canonicalPose7_712 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, true, false, false, false], ![1, 1, 2, 2, 0, 0, 0]⟩
def canonicalBox7_712 : BoxKey 7 :=
  ⟨![315840, 53760, 275520, 268800, 114240, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 53375, 274960, 268310, 114688, 560, 121380], false⟩

theorem canonicalMatch7_712 :
    canonicalPose7_712.boxKey 188160 (referenceBox7 (!canonicalBox7_712.bump)) = canonicalBox7_712 := by decide +kernel

theorem canonicalDecode7_712 : canonicalBox7_712.toKeyData 188160 = keys7Chunk22.get ⟨8, by decide⟩ := by
  change canonicalBox7_712.toKeyData 188160 = ⟨![(47 / 28), (2 / 7), (41 / 28), (10 / 7), (17 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (64 / 105), (1 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_712 : keySolid (keys7Chunk22.get ⟨8, by decide⟩) = canonicalPose7_712.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_712 (box := canonicalBox7_712) (k := keys7Chunk22.get ⟨8, by decide⟩) (canonicalMatch7_712) (canonicalDecode7_712)

def canonicalPose7_713 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, false, true, true, true, false, false], ![2, 0, 2, 2, 1, 0, 0]⟩
def canonicalBox7_713 : BoxKey 7 :=
  ⟨![262080, 107520, 275520, 241920, 60480, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 108010, 274960, 241535, 60080, 121380, 560], false⟩

theorem canonicalMatch7_713 :
    canonicalPose7_713.boxKey 188160 (referenceBox7 (!canonicalBox7_713.bump)) = canonicalBox7_713 := by decide +kernel

theorem canonicalDecode7_713 : canonicalBox7_713.toKeyData 188160 = keys7Chunk22.get ⟨9, by decide⟩ := by
  change canonicalBox7_713.toKeyData 188160 = ⟨![(39 / 28), (4 / 7), (41 / 28), (9 / 7), (9 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (751 / 2352), (289 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_713 : keySolid (keys7Chunk22.get ⟨9, by decide⟩) = canonicalPose7_713.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_713 (box := canonicalBox7_713) (k := keys7Chunk22.get ⟨9, by decide⟩) (canonicalMatch7_713) (canonicalDecode7_713)

def canonicalPose7_714 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, true, true, true, true], ![2, 0, 2, 2, 1, 1, 2]⟩
def canonicalBox7_714 : BoxKey 7 :=
  ⟨![376320, 114240, 268800, 275520, 53760, 60480, 255360], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 114688, 268310, 274960, 53375, 60080, 254940], false⟩

theorem canonicalMatch7_714 :
    canonicalPose7_714.boxKey 188160 (referenceBox7 (!canonicalBox7_714.bump)) = canonicalBox7_714 := by decide +kernel

theorem canonicalDecode7_714 : canonicalBox7_714.toKeyData 188160 = keys7Chunk22.get ⟨10, by decide⟩ := by
  change canonicalBox7_714.toKeyData 188160 = ⟨![2, (17 / 28), (10 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (64 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_714 : keySolid (keys7Chunk22.get ⟨10, by decide⟩) = canonicalPose7_714.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_714 (box := canonicalBox7_714) (k := keys7Chunk22.get ⟨10, by decide⟩) (canonicalMatch7_714) (canonicalDecode7_714)

def canonicalPose7_715 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, true, false, false, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_715 : BoxKey 7 :=
  ⟨![302400, 0, 309120, 248640, 134400, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, -560, 309540, 248240, 134785, 101360, 268310], true⟩

theorem canonicalMatch7_715 :
    canonicalPose7_715.boxKey 188160 (referenceBox7 (!canonicalBox7_715.bump)) = canonicalBox7_715 := by decide +kernel

theorem canonicalDecode7_715 : canonicalBox7_715.toKeyData 188160 = keys7Chunk22.get ⟨11, by decide⟩ := by
  change canonicalBox7_715.toKeyData 188160 = ⟨![(45 / 28), 0, (23 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (-1 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_715 : keySolid (keys7Chunk22.get ⟨11, by decide⟩) = canonicalPose7_715.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_715 (box := canonicalBox7_715) (k := keys7Chunk22.get ⟨11, by decide⟩) (canonicalMatch7_715) (canonicalDecode7_715)

def canonicalPose7_716 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, true, false, false, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_716 : BoxKey 7 :=
  ⟨![309120, 0, 302400, 268800, 100800, 134400, 248640], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 560, 302848, 268310, 101360, 134785, 248240], false⟩

theorem canonicalMatch7_716 :
    canonicalPose7_716.boxKey 188160 (referenceBox7 (!canonicalBox7_716.bump)) = canonicalBox7_716 := by decide +kernel

theorem canonicalDecode7_716 : canonicalBox7_716.toKeyData 188160 = keys7Chunk22.get ⟨12, by decide⟩ := by
  change canonicalBox7_716.toKeyData 188160 = ⟨![(23 / 14), 0, (45 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (1 / 336), (169 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_716 : keySolid (keys7Chunk22.get ⟨12, by decide⟩) = canonicalPose7_716.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_716 (box := canonicalBox7_716) (k := keys7Chunk22.get ⟨12, by decide⟩) (canonicalMatch7_716) (canonicalDecode7_716)

def canonicalPose7_717 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, false, false, true, true, true, true], ![2, 0, 2, 2, 1, 1, 2]⟩
def canonicalBox7_717 : BoxKey 7 :=
  ⟨![268800, 114240, 376320, 255360, 60480, 53760, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 114688, 376880, 254940, 60080, 53375, 274960], true⟩

theorem canonicalMatch7_717 :
    canonicalPose7_717.boxKey 188160 (referenceBox7 (!canonicalBox7_717.bump)) = canonicalBox7_717 := by decide +kernel

theorem canonicalDecode7_717 : canonicalBox7_717.toKeyData 188160 = keys7Chunk22.get ⟨13, by decide⟩ := by
  change canonicalBox7_717.toKeyData 188160 = ⟨![(10 / 7), (17 / 28), 2, (19 / 14), (9 / 28), (2 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (64 / 105), (673 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_717 : keySolid (keys7Chunk22.get ⟨13, by decide⟩) = canonicalPose7_717.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_717 (box := canonicalBox7_717) (k := keys7Chunk22.get ⟨13, by decide⟩) (canonicalMatch7_717) (canonicalDecode7_717)

def canonicalPose7_718 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, false, false, false, true], ![2, 1, 2, 2, 0, 0, 2]⟩
def canonicalBox7_718 : BoxKey 7 :=
  ⟨![241920, 60480, 255360, 376320, 114240, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 60080, 254940, 376880, 114688, 108010, 274960], true⟩

theorem canonicalMatch7_718 :
    canonicalPose7_718.boxKey 188160 (referenceBox7 (!canonicalBox7_718.bump)) = canonicalBox7_718 := by decide +kernel

theorem canonicalDecode7_718 : canonicalBox7_718.toKeyData 188160 = keys7Chunk22.get ⟨14, by decide⟩ := by
  change canonicalBox7_718.toKeyData 188160 = ⟨![(9 / 7), (9 / 28), (19 / 14), 2, (17 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (751 / 2352), (607 / 448), (673 / 336), (64 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_718 : keySolid (keys7Chunk22.get ⟨14, by decide⟩) = canonicalPose7_718.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_718 (box := canonicalBox7_718) (k := keys7Chunk22.get ⟨14, by decide⟩) (canonicalMatch7_718) (canonicalDecode7_718)

def canonicalPose7_719 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, false, false, true, false, false, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_719 : BoxKey 7 :=
  ⟨![322560, 127680, 309120, 262080, 0, 107520, 275520], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 128080, 309540, 261632, 560, 108010, 274960], false⟩

theorem canonicalMatch7_719 :
    canonicalPose7_719.boxKey 188160 (referenceBox7 (!canonicalBox7_719.bump)) = canonicalBox7_719 := by decide +kernel

theorem canonicalDecode7_719 : canonicalBox7_719.toKeyData 188160 = keys7Chunk22.get ⟨15, by decide⟩ := by
  change canonicalBox7_719.toKeyData 188160 = ⟨![(12 / 7), (19 / 28), (23 / 14), (39 / 28), 0, (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (1601 / 2352), (737 / 448), (146 / 105), (1 / 336), (1543 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_719 : keySolid (keys7Chunk22.get ⟨15, by decide⟩) = canonicalPose7_719.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_719 (box := canonicalBox7_719) (k := keys7Chunk22.get ⟨15, by decide⟩) (canonicalMatch7_719) (canonicalDecode7_719)

def canonicalPose7_720 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, false, false, true, false, true, true], ![1, 0, 1, 2, 0, 0, 2]⟩
def canonicalBox7_720 : BoxKey 7 :=
  ⟨![309120, 127680, 322560, 275520, 107520, 0, 262080], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 128080, 322945, 274960, 108010, -560, 261632], true⟩

theorem canonicalMatch7_720 :
    canonicalPose7_720.boxKey 188160 (referenceBox7 (!canonicalBox7_720.bump)) = canonicalBox7_720 := by decide +kernel

theorem canonicalDecode7_720 : canonicalBox7_720.toKeyData 188160 = keys7Chunk22.get ⟨16, by decide⟩ := by
  change canonicalBox7_720.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (12 / 7), (41 / 28), (4 / 7), 0, (39 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_720 : keySolid (keys7Chunk22.get ⟨16, by decide⟩) = canonicalPose7_720.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_720 (box := canonicalBox7_720) (k := keys7Chunk22.get ⟨16, by decide⟩) (canonicalMatch7_720) (canonicalDecode7_720)

def canonicalPose7_721 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, true, true, false, false, true], ![2, 1, 2, 2, 0, 0, 2]⟩
def canonicalBox7_721 : BoxKey 7 :=
  ⟨![255360, 60480, 241920, 275520, 107520, 114240, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 60080, 241535, 274960, 108010, 114688, 375760], false⟩

theorem canonicalMatch7_721 :
    canonicalPose7_721.boxKey 188160 (referenceBox7 (!canonicalBox7_721.bump)) = canonicalBox7_721 := by decide +kernel

theorem canonicalDecode7_721 : canonicalBox7_721.toKeyData 188160 = keys7Chunk22.get ⟨17, by decide⟩ := by
  change canonicalBox7_721.toKeyData 188160 = ⟨![(19 / 14), (9 / 28), (9 / 7), (41 / 28), (4 / 7), (17 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_721 : keySolid (keys7Chunk22.get ⟨17, by decide⟩) = canonicalPose7_721.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_721 (box := canonicalBox7_721) (k := keys7Chunk22.get ⟨17, by decide⟩) (canonicalMatch7_721) (canonicalDecode7_721)

def canonicalPose7_722 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, false, false, false, true, false], ![2, 0, 1, 1, 0, 2, 0]⟩
def canonicalBox7_722 : BoxKey 7 :=
  ⟨![376320, 120960, 315840, 322560, 100800, 268800, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 121380, 316240, 322945, 101360, 268310, 114688], true⟩

theorem canonicalMatch7_722 :
    canonicalPose7_722.boxKey 188160 (referenceBox7 (!canonicalBox7_722.bump)) = canonicalBox7_722 := by decide +kernel

theorem canonicalDecode7_722 : canonicalBox7_722.toKeyData 188160 = keys7Chunk22.get ⟨18, by decide⟩ := by
  change canonicalBox7_722.toKeyData 188160 = ⟨![2, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (10 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_722 : keySolid (keys7Chunk22.get ⟨18, by decide⟩) = canonicalPose7_722.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_722 (box := canonicalBox7_722) (k := keys7Chunk22.get ⟨18, by decide⟩) (canonicalMatch7_722) (canonicalDecode7_722)

def canonicalPose7_723 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, true, true, true, false, true, true], ![2, 0, 2, 2, 0, 2, 1]⟩
def canonicalBox7_723 : BoxKey 7 :=
  ⟨![255360, 0, 262080, 268800, 100800, 241920, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, -560, 261632, 268310, 101360, 241535, 60080], true⟩

theorem canonicalMatch7_723 :
    canonicalPose7_723.boxKey 188160 (referenceBox7 (!canonicalBox7_723.bump)) = canonicalBox7_723 := by decide +kernel

theorem canonicalDecode7_723 : canonicalBox7_723.toKeyData 188160 = keys7Chunk22.get ⟨19, by decide⟩ := by
  change canonicalBox7_723.toKeyData 188160 = ⟨![(19 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (9 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (-1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_723 : keySolid (keys7Chunk22.get ⟨19, by decide⟩) = canonicalPose7_723.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_723 (box := canonicalBox7_723) (k := keys7Chunk22.get ⟨19, by decide⟩) (canonicalMatch7_723) (canonicalDecode7_723)

def canonicalPose7_724 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, false, true, true, false, false, false], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_724 : BoxKey 7 :=
  ⟨![309120, 114240, 376320, 268800, 100800, 322560, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 114688, 375760, 268310, 101360, 322945, 128080], false⟩

theorem canonicalMatch7_724 :
    canonicalPose7_724.boxKey 188160 (referenceBox7 (!canonicalBox7_724.bump)) = canonicalBox7_724 := by decide +kernel

theorem canonicalDecode7_724 : canonicalBox7_724.toKeyData 188160 = keys7Chunk22.get ⟨20, by decide⟩ := by
  change canonicalBox7_724.toKeyData 188160 = ⟨![(23 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (12 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (64 / 105), (671 / 336), (3833 / 2688), (181 / 336), (9227 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_724 : keySolid (keys7Chunk22.get ⟨20, by decide⟩) = canonicalPose7_724.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_724 (box := canonicalBox7_724) (k := keys7Chunk22.get ⟨20, by decide⟩) (canonicalMatch7_724) (canonicalDecode7_724)

def canonicalPose7_725 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, false, true, false, false, false, false], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_725 : BoxKey 7 :=
  ⟨![322560, 100800, 268800, 376320, 114240, 309120, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 101360, 268310, 376880, 114688, 309540, 128080], true⟩

theorem canonicalMatch7_725 :
    canonicalPose7_725.boxKey 188160 (referenceBox7 (!canonicalBox7_725.bump)) = canonicalBox7_725 := by decide +kernel

theorem canonicalDecode7_725 : canonicalBox7_725.toKeyData 188160 = keys7Chunk22.get ⟨21, by decide⟩ := by
  change canonicalBox7_725.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (23 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (3833 / 2688), (673 / 336), (64 / 105), (737 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_725 : keySolid (keys7Chunk22.get ⟨21, by decide⟩) = canonicalPose7_725.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_725 (box := canonicalBox7_725) (k := keys7Chunk22.get ⟨21, by decide⟩) (canonicalMatch7_725) (canonicalDecode7_725)

def canonicalPose7_726 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, true, true, false, true, true], ![2, 0, 2, 2, 0, 2, 1]⟩
def canonicalBox7_726 : BoxKey 7 :=
  ⟨![241920, 100800, 268800, 262080, 0, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 101360, 268310, 261632, 560, 254940, 60080], false⟩

theorem canonicalMatch7_726 :
    canonicalPose7_726.boxKey 188160 (referenceBox7 (!canonicalBox7_726.bump)) = canonicalBox7_726 := by decide +kernel

theorem canonicalDecode7_726 : canonicalBox7_726.toKeyData 188160 = keys7Chunk22.get ⟨22, by decide⟩ := by
  change canonicalBox7_726.toKeyData 188160 = ⟨![(9 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (1 / 336), (607 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_726 : keySolid (keys7Chunk22.get ⟨22, by decide⟩) = canonicalPose7_726.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_726 (box := canonicalBox7_726) (k := keys7Chunk22.get ⟨22, by decide⟩) (canonicalMatch7_726) (canonicalDecode7_726)

def canonicalPose7_727 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, false, false, true, false], ![2, 0, 1, 1, 0, 2, 0]⟩
def canonicalBox7_727 : BoxKey 7 :=
  ⟨![268800, 100800, 322560, 315840, 120960, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 322945, 316240, 121380, 375760, 114688], false⟩

theorem canonicalMatch7_727 :
    canonicalPose7_727.boxKey 188160 (referenceBox7 (!canonicalBox7_727.bump)) = canonicalBox7_727 := by decide +kernel

theorem canonicalDecode7_727 : canonicalBox7_727.toKeyData 188160 = keys7Chunk22.get ⟨23, by decide⟩ := by
  change canonicalBox7_727.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_727 : keySolid (keys7Chunk22.get ⟨23, by decide⟩) = canonicalPose7_727.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_727 (box := canonicalBox7_727) (k := keys7Chunk22.get ⟨23, by decide⟩) (canonicalMatch7_727) (canonicalDecode7_727)

def canonicalPose7_728 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, true, false, false, false], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_728 : BoxKey 7 :=
  ⟨![302400, 107520, 275520, 241920, 127680, 309120, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![302848, 108010, 274960, 241535, 128080, 309540, 560], false⟩

theorem canonicalMatch7_728 :
    canonicalPose7_728.boxKey 188160 (referenceBox7 (!canonicalBox7_728.bump)) = canonicalBox7_728 := by decide +kernel

theorem canonicalDecode7_728 : canonicalBox7_728.toKeyData 188160 = keys7Chunk22.get ⟨24, by decide⟩ := by
  change canonicalBox7_728.toKeyData 188160 = ⟨![(45 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28), (23 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352), (737 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_728 : keySolid (keys7Chunk22.get ⟨24, by decide⟩) = canonicalPose7_728.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_728 (box := canonicalBox7_728) (k := keys7Chunk22.get ⟨24, by decide⟩) (canonicalMatch7_728) (canonicalDecode7_728)

def canonicalPose7_729 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, true, true, false, false, true], ![1, 0, 2, 2, 0, 1, 0]⟩
def canonicalBox7_729 : BoxKey 7 :=
  ⟨![309120, 127680, 241920, 275520, 107520, 302400, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![309540, 128080, 241535, 274960, 108010, 302848, -560], true⟩

theorem canonicalMatch7_729 :
    canonicalPose7_729.boxKey 188160 (referenceBox7 (!canonicalBox7_729.bump)) = canonicalBox7_729 := by decide +kernel

theorem canonicalDecode7_729 : canonicalBox7_729.toKeyData 188160 = keys7Chunk22.get ⟨25, by decide⟩ := by
  change canonicalBox7_729.toKeyData 188160 = ⟨![(23 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7), (45 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (169 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_729 : keySolid (keys7Chunk22.get ⟨25, by decide⟩) = canonicalPose7_729.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_729 (box := canonicalBox7_729) (k := keys7Chunk22.get ⟨25, by decide⟩) (canonicalMatch7_729) (canonicalDecode7_729)

def canonicalPose7_730 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, false, false, true, true], ![2, 0, 1, 1, 0, 2, 2]⟩
def canonicalBox7_730 : BoxKey 7 :=
  ⟨![376320, 120960, 315840, 322560, 100800, 268800, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![375760, 121380, 316240, 322945, 101360, 268310, 261632], false⟩

theorem canonicalMatch7_730 :
    canonicalPose7_730.boxKey 188160 (referenceBox7 (!canonicalBox7_730.bump)) = canonicalBox7_730 := by decide +kernel

theorem canonicalDecode7_730 : canonicalBox7_730.toKeyData 188160 = keys7Chunk22.get ⟨26, by decide⟩ := by
  change canonicalBox7_730.toKeyData 188160 = ⟨![2, (9 / 14), (47 / 28), (12 / 7), (15 / 28), (10 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(671 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_730 : keySolid (keys7Chunk22.get ⟨26, by decide⟩) = canonicalPose7_730.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_730 (box := canonicalBox7_730) (k := keys7Chunk22.get ⟨26, by decide⟩) (canonicalMatch7_730) (canonicalDecode7_730)

def canonicalPose7_731 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, true, false, true, false], ![2, 0, 2, 2, 0, 2, 1]⟩
def canonicalBox7_731 : BoxKey 7 :=
  ⟨![255360, 0, 262080, 268800, 100800, 241920, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![254940, 560, 261632, 268310, 101360, 241535, 316240], false⟩

theorem canonicalMatch7_731 :
    canonicalPose7_731.boxKey 188160 (referenceBox7 (!canonicalBox7_731.bump)) = canonicalBox7_731 := by decide +kernel

theorem canonicalDecode7_731 : canonicalBox7_731.toKeyData 188160 = keys7Chunk22.get ⟨27, by decide⟩ := by
  change canonicalBox7_731.toKeyData 188160 = ⟨![(19 / 14), 0, (39 / 28), (10 / 7), (15 / 28), (9 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(607 / 448), (1 / 336), (146 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_731 : keySolid (keys7Chunk22.get ⟨27, by decide⟩) = canonicalPose7_731.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_731 (box := canonicalBox7_731) (k := keys7Chunk22.get ⟨27, by decide⟩) (canonicalMatch7_731) (canonicalDecode7_731)

def canonicalPose7_732 : Pose 7 :=
  ⟨canonicalPerm7_12, ![false, false, false, true, false, false, true], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_732 : BoxKey 7 :=
  ⟨![309120, 114240, 376320, 268800, 100800, 322560, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![309540, 114688, 376880, 268310, 101360, 322945, 248240], true⟩

theorem canonicalMatch7_732 :
    canonicalPose7_732.boxKey 188160 (referenceBox7 (!canonicalBox7_732.bump)) = canonicalBox7_732 := by decide +kernel

theorem canonicalDecode7_732 : canonicalBox7_732.toKeyData 188160 = keys7Chunk22.get ⟨28, by decide⟩ := by
  change canonicalBox7_732.toKeyData 188160 = ⟨![(23 / 14), (17 / 28), 2, (10 / 7), (15 / 28), (12 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (64 / 105), (673 / 336), (3833 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_732 : keySolid (keys7Chunk22.get ⟨28, by decide⟩) = canonicalPose7_732.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_732 (box := canonicalBox7_732) (k := keys7Chunk22.get ⟨28, by decide⟩) (canonicalMatch7_732) (canonicalDecode7_732)

def canonicalPose7_733 : Pose 7 :=
  ⟨canonicalPerm7_21, ![false, false, true, true, false, false, true], ![1, 0, 2, 2, 0, 1, 2]⟩
def canonicalBox7_733 : BoxKey 7 :=
  ⟨![322560, 100800, 268800, 376320, 114240, 309120, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![322945, 101360, 268310, 375760, 114688, 309540, 248240], false⟩

theorem canonicalMatch7_733 :
    canonicalPose7_733.boxKey 188160 (referenceBox7 (!canonicalBox7_733.bump)) = canonicalBox7_733 := by decide +kernel

theorem canonicalDecode7_733 : canonicalBox7_733.toKeyData 188160 = keys7Chunk22.get ⟨29, by decide⟩ := by
  change canonicalBox7_733.toKeyData 188160 = ⟨![(12 / 7), (15 / 28), (10 / 7), 2, (17 / 28), (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(9227 / 5376), (181 / 336), (3833 / 2688), (671 / 336), (64 / 105), (737 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_733 : keySolid (keys7Chunk22.get ⟨29, by decide⟩) = canonicalPose7_733.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_733 (box := canonicalBox7_733) (k := keys7Chunk22.get ⟨29, by decide⟩) (canonicalMatch7_733) (canonicalDecode7_733)

def canonicalPose7_734 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, true, true, true, true, false], ![2, 0, 2, 2, 0, 2, 1]⟩
def canonicalBox7_734 : BoxKey 7 :=
  ⟨![241920, 100800, 268800, 262080, 0, 255360, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 101360, 268310, 261632, -560, 254940, 316240], true⟩

theorem canonicalMatch7_734 :
    canonicalPose7_734.boxKey 188160 (referenceBox7 (!canonicalBox7_734.bump)) = canonicalBox7_734 := by decide +kernel

theorem canonicalDecode7_734 : canonicalBox7_734.toKeyData 188160 = keys7Chunk22.get ⟨30, by decide⟩ := by
  change canonicalBox7_734.toKeyData 188160 = ⟨![(9 / 7), (15 / 28), (10 / 7), (39 / 28), 0, (19 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (-1 / 336), (607 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_734 : keySolid (keys7Chunk22.get ⟨30, by decide⟩) = canonicalPose7_734.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_734 (box := canonicalBox7_734) (k := keys7Chunk22.get ⟨30, by decide⟩) (canonicalMatch7_734) (canonicalDecode7_734)

def canonicalPose7_735 : Pose 7 :=
  ⟨canonicalPerm7_5, ![true, false, false, false, false, false, true], ![2, 0, 1, 1, 0, 2, 2]⟩
def canonicalBox7_735 : BoxKey 7 :=
  ⟨![268800, 100800, 322560, 315840, 120960, 376320, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![268310, 101360, 322945, 316240, 121380, 376880, 261632], true⟩

theorem canonicalMatch7_735 :
    canonicalPose7_735.boxKey 188160 (referenceBox7 (!canonicalBox7_735.bump)) = canonicalBox7_735 := by decide +kernel

theorem canonicalDecode7_735 : canonicalBox7_735.toKeyData 188160 = keys7Chunk22.get ⟨31, by decide⟩ := by
  change canonicalBox7_735.toKeyData 188160 = ⟨![(10 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14), 2, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448), (673 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_735 : keySolid (keys7Chunk22.get ⟨31, by decide⟩) = canonicalPose7_735.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_735 (box := canonicalBox7_735) (k := keys7Chunk22.get ⟨31, by decide⟩) (canonicalMatch7_735) (canonicalDecode7_735)

theorem keys7Chunk22_canonical : ∀ k ∈ keys7Chunk22,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk22, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_704, canonicalSolid7_704⟩
  · exact ⟨canonicalPose7_705, canonicalSolid7_705⟩
  · exact ⟨canonicalPose7_706, canonicalSolid7_706⟩
  · exact ⟨canonicalPose7_707, canonicalSolid7_707⟩
  · exact ⟨canonicalPose7_708, canonicalSolid7_708⟩
  · exact ⟨canonicalPose7_709, canonicalSolid7_709⟩
  · exact ⟨canonicalPose7_710, canonicalSolid7_710⟩
  · exact ⟨canonicalPose7_711, canonicalSolid7_711⟩
  · exact ⟨canonicalPose7_712, canonicalSolid7_712⟩
  · exact ⟨canonicalPose7_713, canonicalSolid7_713⟩
  · exact ⟨canonicalPose7_714, canonicalSolid7_714⟩
  · exact ⟨canonicalPose7_715, canonicalSolid7_715⟩
  · exact ⟨canonicalPose7_716, canonicalSolid7_716⟩
  · exact ⟨canonicalPose7_717, canonicalSolid7_717⟩
  · exact ⟨canonicalPose7_718, canonicalSolid7_718⟩
  · exact ⟨canonicalPose7_719, canonicalSolid7_719⟩
  · exact ⟨canonicalPose7_720, canonicalSolid7_720⟩
  · exact ⟨canonicalPose7_721, canonicalSolid7_721⟩
  · exact ⟨canonicalPose7_722, canonicalSolid7_722⟩
  · exact ⟨canonicalPose7_723, canonicalSolid7_723⟩
  · exact ⟨canonicalPose7_724, canonicalSolid7_724⟩
  · exact ⟨canonicalPose7_725, canonicalSolid7_725⟩
  · exact ⟨canonicalPose7_726, canonicalSolid7_726⟩
  · exact ⟨canonicalPose7_727, canonicalSolid7_727⟩
  · exact ⟨canonicalPose7_728, canonicalSolid7_728⟩
  · exact ⟨canonicalPose7_729, canonicalSolid7_729⟩
  · exact ⟨canonicalPose7_730, canonicalSolid7_730⟩
  · exact ⟨canonicalPose7_731, canonicalSolid7_731⟩
  · exact ⟨canonicalPose7_732, canonicalSolid7_732⟩
  · exact ⟨canonicalPose7_733, canonicalSolid7_733⟩
  · exact ⟨canonicalPose7_734, canonicalSolid7_734⟩
  · exact ⟨canonicalPose7_735, canonicalSolid7_735⟩

#print axioms keys7Chunk22_canonical

end SparseMonotiles.Canonical
