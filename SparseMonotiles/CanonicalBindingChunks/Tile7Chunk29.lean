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

def canonicalPose7_928 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, false, true, true, false, true, false], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_928 : BoxKey 7 :=
  ⟨![248640, 309120, 262080, 0, 107520, 275520, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 309540, 261632, -560, 108010, 274960, 322945], true⟩

theorem canonicalMatch7_928 :
    canonicalPose7_928.boxKey 188160 (referenceBox7 (!canonicalBox7_928.bump)) = canonicalBox7_928 := by decide +kernel

theorem canonicalDecode7_928 : canonicalBox7_928.toKeyData 188160 = keys7Chunk29.get ⟨0, by decide⟩ := by
  change canonicalBox7_928.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (146 / 105), (-1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_928 : keySolid (keys7Chunk29.get ⟨0, by decide⟩) = canonicalPose7_928.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_928 (box := canonicalBox7_928) (k := keys7Chunk29.get ⟨0, by decide⟩) (canonicalMatch7_928) (canonicalDecode7_928)

def canonicalPose7_929 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, false, true, false, false, true, false], ![2, 1, 2, 0, 0, 2, 1]⟩
def canonicalBox7_929 : BoxKey 7 :=
  ⟨![248640, 322560, 275520, 107520, 0, 262080, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 322945, 274960, 108010, 560, 261632, 309540], false⟩

theorem canonicalMatch7_929 :
    canonicalPose7_929.boxKey 188160 (referenceBox7 (!canonicalBox7_929.bump)) = canonicalBox7_929 := by decide +kernel

theorem canonicalDecode7_929 : canonicalBox7_929.toKeyData 188160 = keys7Chunk29.get ⟨1, by decide⟩ := by
  change canonicalBox7_929.toKeyData 188160 = ⟨![(37 / 28), (12 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (1 / 336), (146 / 105), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_929 : keySolid (keys7Chunk29.get ⟨1, by decide⟩) = canonicalPose7_929.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_929 (box := canonicalBox7_929) (k := keys7Chunk29.get ⟨1, by decide⟩) (canonicalMatch7_929) (canonicalDecode7_929)

def canonicalPose7_930 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, false, false, false, true], ![1, 2, 2, 0, 0, 2, 2]⟩
def canonicalBox7_930 : BoxKey 7 :=
  ⟨![315840, 241920, 275520, 107520, 114240, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 241535, 274960, 108010, 114688, 376880, 254940], true⟩

theorem canonicalMatch7_930 :
    canonicalPose7_930.boxKey 188160 (referenceBox7 (!canonicalBox7_930.bump)) = canonicalBox7_930 := by decide +kernel

theorem canonicalDecode7_930 : canonicalBox7_930.toKeyData 188160 = keys7Chunk29.get ⟨2, by decide⟩ := by
  change canonicalBox7_930.toKeyData 188160 = ⟨![(47 / 28), (9 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (673 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_930 : keySolid (keys7Chunk29.get ⟨2, by decide⟩) = canonicalPose7_930.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_930 (box := canonicalBox7_930) (k := keys7Chunk29.get ⟨2, by decide⟩) (canonicalMatch7_930) (canonicalDecode7_930)

def canonicalPose7_931 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, true, true, true, true, false], ![2, 2, 2, 1, 1, 2, 2]⟩
def canonicalBox7_931 : BoxKey 7 :=
  ⟨![262080, 268800, 275520, 53760, 60480, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 274960, 53375, 60080, 254940, 376880], true⟩

theorem canonicalMatch7_931 :
    canonicalPose7_931.boxKey 188160 (referenceBox7 (!canonicalBox7_931.bump)) = canonicalBox7_931 := by decide +kernel

theorem canonicalDecode7_931 : canonicalBox7_931.toKeyData 188160 = keys7Chunk29.get ⟨3, by decide⟩ := by
  change canonicalBox7_931.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_931 : keySolid (keys7Chunk29.get ⟨3, by decide⟩) = canonicalPose7_931.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_931 (box := canonicalBox7_931) (k := keys7Chunk29.get ⟨3, by decide⟩) (canonicalMatch7_931) (canonicalDecode7_931)

def canonicalPose7_932 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, false, true, false, true, false, true], ![2, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_932 : BoxKey 7 :=
  ⟨![376320, 302400, 268800, 100800, 241920, 127680, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![375760, 302848, 268310, 101360, 241535, 128080, 66780], false⟩

theorem canonicalMatch7_932 :
    canonicalPose7_932.boxKey 188160 (referenceBox7 (!canonicalBox7_932.bump)) = canonicalBox7_932 := by decide +kernel

theorem canonicalDecode7_932 : canonicalBox7_932.toKeyData 188160 = keys7Chunk29.get ⟨4, by decide⟩ := by
  change canonicalBox7_932.toKeyData 188160 = ⟨![2, (45 / 28), (10 / 7), (15 / 28), (9 / 7), (19 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(671 / 336), (169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_932 : keySolid (keys7Chunk29.get ⟨4, by decide⟩) = canonicalPose7_932.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_932 (box := canonicalBox7_932) (k := keys7Chunk29.get ⟨4, by decide⟩) (canonicalMatch7_932) (canonicalDecode7_932)

def canonicalPose7_933 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, true, false, true, false, true], ![2, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_933 : BoxKey 7 :=
  ⟨![376320, 309120, 248640, 134400, 275520, 107520, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![376880, 309540, 248240, 134785, 274960, 108010, 73472], true⟩

theorem canonicalMatch7_933 :
    canonicalPose7_933.boxKey 188160 (referenceBox7 (!canonicalBox7_933.bump)) = canonicalBox7_933 := by decide +kernel

theorem canonicalDecode7_933 : canonicalBox7_933.toKeyData 188160 = keys7Chunk29.get ⟨5, by decide⟩ := by
  change canonicalBox7_933.toKeyData 188160 = ⟨![2, (23 / 14), (37 / 28), (5 / 7), (41 / 28), (4 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(673 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_933 : keySolid (keys7Chunk29.get ⟨5, by decide⟩) = canonicalPose7_933.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_933 (box := canonicalBox7_933) (k := keys7Chunk29.get ⟨5, by decide⟩) (canonicalMatch7_933) (canonicalDecode7_933)

def canonicalPose7_934 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, false, true, true, false, false, false], ![2, 2, 2, 1, 1, 0, 0]⟩
def canonicalBox7_934 : BoxKey 7 :=
  ⟨![262080, 376320, 255360, 60480, 322560, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 376880, 254940, 60080, 322945, 101360, 108010], true⟩

theorem canonicalMatch7_934 :
    canonicalPose7_934.boxKey 188160 (referenceBox7 (!canonicalBox7_934.bump)) = canonicalBox7_934 := by decide +kernel

theorem canonicalDecode7_934 : canonicalBox7_934.toKeyData 188160 = keys7Chunk29.get ⟨6, by decide⟩ := by
  change canonicalBox7_934.toKeyData 188160 = ⟨![(39 / 28), 2, (19 / 14), (9 / 28), (12 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (673 / 336), (607 / 448), (751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_934 : keySolid (keys7Chunk29.get ⟨6, by decide⟩) = canonicalPose7_934.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_934 (box := canonicalBox7_934) (k := keys7Chunk29.get ⟨6, by decide⟩) (canonicalMatch7_934) (canonicalDecode7_934)

def canonicalPose7_935 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, false, false, true, false, false], ![1, 2, 2, 0, 2, 0, 0]⟩
def canonicalBox7_935 : BoxKey 7 :=
  ⟨![315840, 255360, 376320, 114240, 268800, 100800, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 254940, 376880, 114688, 268310, 101360, 134785], true⟩

theorem canonicalMatch7_935 :
    canonicalPose7_935.boxKey 188160 (referenceBox7 (!canonicalBox7_935.bump)) = canonicalBox7_935 := by decide +kernel

theorem canonicalDecode7_935 : canonicalBox7_935.toKeyData 188160 = keys7Chunk29.get ⟨7, by decide⟩ := by
  change canonicalBox7_935.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (15 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (673 / 336), (64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_935 : keySolid (keys7Chunk29.get ⟨7, by decide⟩) = canonicalPose7_935.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_935 (box := canonicalBox7_935) (k := keys7Chunk29.get ⟨7, by decide⟩) (canonicalMatch7_935) (canonicalDecode7_935)

def canonicalPose7_936 : Pose 7 :=
  ⟨canonicalPerm7_16, ![true, false, true, false, true, false, true], ![2, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_936 : BoxKey 7 :=
  ⟨![248640, 309120, 262080, 0, 268800, 100800, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![248240, 309540, 261632, 560, 268310, 101360, 53375], false⟩

theorem canonicalMatch7_936 :
    canonicalPose7_936.boxKey 188160 (referenceBox7 (!canonicalBox7_936.bump)) = canonicalBox7_936 := by decide +kernel

theorem canonicalDecode7_936 : canonicalBox7_936.toKeyData 188160 = keys7Chunk29.get ⟨8, by decide⟩ := by
  change canonicalBox7_936.toKeyData 188160 = ⟨![(37 / 28), (23 / 14), (39 / 28), 0, (10 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(3103 / 2352), (737 / 448), (146 / 105), (1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_936 : keySolid (keys7Chunk29.get ⟨8, by decide⟩) = canonicalPose7_936.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_936 (box := canonicalBox7_936) (k := keys7Chunk29.get ⟨8, by decide⟩) (canonicalMatch7_936) (canonicalDecode7_936)

def canonicalPose7_937 : Pose 7 :=
  ⟨canonicalPerm7_19, ![true, false, true, false, false, false, true], ![2, 1, 2, 0, 2, 0, 1]⟩
def canonicalBox7_937 : BoxKey 7 :=
  ⟨![248640, 322560, 275520, 107520, 376320, 114240, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![248240, 322945, 274960, 108010, 376880, 114688, 66780], true⟩

theorem canonicalMatch7_937 :
    canonicalPose7_937.boxKey 188160 (referenceBox7 (!canonicalBox7_937.bump)) = canonicalBox7_937 := by decide +kernel

theorem canonicalDecode7_937 : canonicalBox7_937.toKeyData 188160 = keys7Chunk29.get ⟨9, by decide⟩ := by
  change canonicalBox7_937.toKeyData 188160 = ⟨![(37 / 28), (12 / 7), (41 / 28), (4 / 7), 2, (17 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (673 / 336), (64 / 105), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_937 : keySolid (keys7Chunk29.get ⟨9, by decide⟩) = canonicalPose7_937.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_937 (box := canonicalBox7_937) (k := keys7Chunk29.get ⟨9, by decide⟩) (canonicalMatch7_937) (canonicalDecode7_937)

def canonicalPose7_938 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, true, true, false, true, false, false], ![1, 2, 2, 0, 2, 0, 0]⟩
def canonicalBox7_938 : BoxKey 7 :=
  ⟨![315840, 241920, 275520, 107520, 262080, 0, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 241535, 274960, 108010, 261632, 560, 121380], false⟩

theorem canonicalMatch7_938 :
    canonicalPose7_938.boxKey 188160 (referenceBox7 (!canonicalBox7_938.bump)) = canonicalBox7_938 := by decide +kernel

theorem canonicalDecode7_938 : canonicalBox7_938.toKeyData 188160 = keys7Chunk29.get ⟨10, by decide⟩ := by
  change canonicalBox7_938.toKeyData 188160 = ⟨![(47 / 28), (9 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_938 : keySolid (keys7Chunk29.get ⟨10, by decide⟩) = canonicalPose7_938.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_938 (box := canonicalBox7_938) (k := keys7Chunk29.get ⟨10, by decide⟩) (canonicalMatch7_938) (canonicalDecode7_938)

def canonicalPose7_939 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, true, true, false, false, false], ![2, 2, 2, 1, 1, 0, 0]⟩
def canonicalBox7_939 : BoxKey 7 :=
  ⟨![262080, 268800, 275520, 53760, 315840, 120960, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 274960, 53375, 316240, 121380, 560], false⟩

theorem canonicalMatch7_939 :
    canonicalPose7_939.boxKey 188160 (referenceBox7 (!canonicalBox7_939.bump)) = canonicalBox7_939 := by decide +kernel

theorem canonicalDecode7_939 : canonicalBox7_939.toKeyData 188160 = keys7Chunk29.get ⟨11, by decide⟩ := by
  change canonicalBox7_939.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (41 / 28), (2 / 7), (47 / 28), (9 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352), (289 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_939 : keySolid (keys7Chunk29.get ⟨11, by decide⟩) = canonicalPose7_939.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_939 (box := canonicalBox7_939) (k := keys7Chunk29.get ⟨11, by decide⟩) (canonicalMatch7_939) (canonicalDecode7_939)

def canonicalPose7_940 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, true, true, true, true, true, true], ![2, 2, 2, 1, 2, 1, 2]⟩
def canonicalBox7_940 : BoxKey 7 :=
  ⟨![376320, 268800, 275520, 53760, 248640, 67200, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![376880, 268310, 274960, 53375, 248240, 66780, 261632], true⟩

theorem canonicalMatch7_940 :
    canonicalPose7_940.boxKey 188160 (referenceBox7 (!canonicalBox7_940.bump)) = canonicalBox7_940 := by decide +kernel

theorem canonicalDecode7_940 : canonicalBox7_940.toKeyData 188160 = keys7Chunk29.get ⟨12, by decide⟩ := by
  change canonicalBox7_940.toKeyData 188160 = ⟨![2, (10 / 7), (41 / 28), (2 / 7), (37 / 28), (5 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(673 / 336), (3833 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352), (159 / 448), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_940 : keySolid (keys7Chunk29.get ⟨12, by decide⟩) = canonicalPose7_940.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_940 (box := canonicalBox7_940) (k := keys7Chunk29.get ⟨12, by decide⟩) (canonicalMatch7_940) (canonicalDecode7_940)

def canonicalPose7_941 : Pose 7 :=
  ⟨canonicalPerm7_7, ![true, true, true, true, true, true, true], ![2, 2, 2, 1, 2, 1, 2]⟩
def canonicalBox7_941 : BoxKey 7 :=
  ⟨![268800, 376320, 262080, 67200, 248640, 53760, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![268310, 375760, 261632, 66780, 248240, 53375, 274960], false⟩

theorem canonicalMatch7_941 :
    canonicalPose7_941.boxKey 188160 (referenceBox7 (!canonicalBox7_941.bump)) = canonicalBox7_941 := by decide +kernel

theorem canonicalDecode7_941 : canonicalBox7_941.toKeyData 188160 = keys7Chunk29.get ⟨13, by decide⟩ := by
  change canonicalBox7_941.toKeyData 188160 = ⟨![(10 / 7), 2, (39 / 28), (5 / 14), (37 / 28), (2 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (671 / 336), (146 / 105), (159 / 448), (3103 / 2352), (1525 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_941 : keySolid (keys7Chunk29.get ⟨13, by decide⟩) = canonicalPose7_941.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_941 (box := canonicalBox7_941) (k := keys7Chunk29.get ⟨13, by decide⟩) (canonicalMatch7_941) (canonicalDecode7_941)

def canonicalPose7_942 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, false, false, false, false, true], ![2, 2, 2, 0, 1, 0, 2]⟩
def canonicalBox7_942 : BoxKey 7 :=
  ⟨![268800, 262080, 376320, 120960, 315840, 134400, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 376880, 121380, 316240, 134785, 274960], true⟩

theorem canonicalMatch7_942 :
    canonicalPose7_942.boxKey 188160 (referenceBox7 (!canonicalBox7_942.bump)) = canonicalBox7_942 := by decide +kernel

theorem canonicalDecode7_942 : canonicalBox7_942.toKeyData 188160 = keys7Chunk29.get ⟨14, by decide⟩ := by
  change canonicalBox7_942.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 2, (9 / 14), (47 / 28), (5 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (673 / 336), (289 / 448), (3953 / 2352), (3851 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_942 : keySolid (keys7Chunk29.get ⟨14, by decide⟩) = canonicalPose7_942.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_942 (box := canonicalBox7_942) (k := keys7Chunk29.get ⟨14, by decide⟩) (canonicalMatch7_942) (canonicalDecode7_942)

def canonicalPose7_943 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, true, true, true, false, true], ![1, 1, 2, 0, 2, 0, 2]⟩
def canonicalBox7_943 : BoxKey 7 :=
  ⟨![322560, 315840, 255360, 0, 262080, 107520, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![322945, 316240, 254940, -560, 261632, 108010, 274960], true⟩

theorem canonicalMatch7_943 :
    canonicalPose7_943.boxKey 188160 (referenceBox7 (!canonicalBox7_943.bump)) = canonicalBox7_943 := by decide +kernel

theorem canonicalDecode7_943 : canonicalBox7_943.toKeyData 188160 = keys7Chunk29.get ⟨15, by decide⟩ := by
  change canonicalBox7_943.toKeyData 188160 = ⟨![(12 / 7), (47 / 28), (19 / 14), 0, (39 / 28), (4 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(9227 / 5376), (3953 / 2352), (607 / 448), (-1 / 336), (146 / 105), (1543 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_943 : keySolid (keys7Chunk29.get ⟨15, by decide⟩) = canonicalPose7_943.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_943 (box := canonicalBox7_943) (k := keys7Chunk29.get ⟨15, by decide⟩) (canonicalMatch7_943) (canonicalDecode7_943)

def canonicalPose7_944 : Pose 7 :=
  ⟨canonicalPerm7_3, ![true, true, true, true, false, true, true], ![2, 2, 2, 1, 2, 1, 2]⟩
def canonicalBox7_944 : BoxKey 7 :=
  ⟨![275520, 241920, 248640, 67200, 376320, 73920, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![274960, 241535, 248240, 66780, 376880, 73472, 268310], true⟩

theorem canonicalMatch7_944 :
    canonicalPose7_944.boxKey 188160 (referenceBox7 (!canonicalBox7_944.bump)) = canonicalBox7_944 := by decide +kernel

theorem canonicalDecode7_944 : canonicalBox7_944.toKeyData 188160 = keys7Chunk29.get ⟨16, by decide⟩ := by
  change canonicalBox7_944.toKeyData 188160 = ⟨![(41 / 28), (9 / 7), (37 / 28), (5 / 14), 2, (11 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448), (673 / 336), (41 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_944 : keySolid (keys7Chunk29.get ⟨16, by decide⟩) = canonicalPose7_944.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_944 (box := canonicalBox7_944) (k := keys7Chunk29.get ⟨16, by decide⟩) (canonicalMatch7_944) (canonicalDecode7_944)

def canonicalPose7_945 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, true, true, true, true, true], ![2, 2, 2, 1, 2, 1, 2]⟩
def canonicalBox7_945 : BoxKey 7 :=
  ⟨![241920, 275520, 268800, 73920, 376320, 67200, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![241535, 274960, 268310, 73472, 375760, 66780, 248240], false⟩

theorem canonicalMatch7_945 :
    canonicalPose7_945.boxKey 188160 (referenceBox7 (!canonicalBox7_945.bump)) = canonicalBox7_945 := by decide +kernel

theorem canonicalDecode7_945 : canonicalBox7_945.toKeyData 188160 = keys7Chunk29.get ⟨17, by decide⟩ := by
  change canonicalBox7_945.toKeyData 188160 = ⟨![(9 / 7), (41 / 28), (10 / 7), (11 / 28), 2, (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105), (671 / 336), (159 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_945 : keySolid (keys7Chunk29.get ⟨17, by decide⟩) = canonicalPose7_945.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_945 (box := canonicalBox7_945) (k := keys7Chunk29.get ⟨17, by decide⟩) (canonicalMatch7_945) (canonicalDecode7_945)

def canonicalPose7_946 : Pose 7 :=
  ⟨canonicalPerm7_18, ![false, false, true, false, true, false, true], ![1, 1, 2, 0, 2, 0, 2]⟩
def canonicalBox7_946 : BoxKey 7 :=
  ⟨![315840, 322560, 275520, 107520, 262080, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![316240, 322945, 274960, 108010, 261632, 560, 254940], false⟩

theorem canonicalMatch7_946 :
    canonicalPose7_946.boxKey 188160 (referenceBox7 (!canonicalBox7_946.bump)) = canonicalBox7_946 := by decide +kernel

theorem canonicalDecode7_946 : canonicalBox7_946.toKeyData 188160 = keys7Chunk29.get ⟨18, by decide⟩ := by
  change canonicalBox7_946.toKeyData 188160 = ⟨![(47 / 28), (12 / 7), (41 / 28), (4 / 7), (39 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (146 / 105), (1 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_946 : keySolid (keys7Chunk29.get ⟨18, by decide⟩) = canonicalPose7_946.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_946 (box := canonicalBox7_946) (k := keys7Chunk29.get ⟨18, by decide⟩) (canonicalMatch7_946) (canonicalDecode7_946)

def canonicalPose7_947 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, true, false, false, false, true], ![2, 2, 2, 0, 1, 0, 2]⟩
def canonicalBox7_947 : BoxKey 7 :=
  ⟨![262080, 268800, 275520, 134400, 315840, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![261632, 268310, 274960, 134785, 316240, 121380, 375760], false⟩

theorem canonicalMatch7_947 :
    canonicalPose7_947.boxKey 188160 (referenceBox7 (!canonicalBox7_947.bump)) = canonicalBox7_947 := by decide +kernel

theorem canonicalDecode7_947 : canonicalBox7_947.toKeyData 188160 = keys7Chunk29.get ⟨19, by decide⟩ := by
  change canonicalBox7_947.toKeyData 188160 = ⟨![(39 / 28), (10 / 7), (41 / 28), (5 / 7), (47 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352), (289 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_947 : keySolid (keys7Chunk29.get ⟨19, by decide⟩) = canonicalPose7_947.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_947 (box := canonicalBox7_947) (k := keys7Chunk29.get ⟨19, by decide⟩) (canonicalMatch7_947) (canonicalDecode7_947)

def canonicalPose7_948 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, false, false, false, false], ![2, 2, 2, 0, 1, 1, 0]⟩
def canonicalBox7_948 : BoxKey 7 :=
  ⟨![376320, 262080, 268800, 100800, 322560, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![376880, 261632, 268310, 101360, 322945, 316240, 121380], true⟩

theorem canonicalMatch7_948 :
    canonicalPose7_948.boxKey 188160 (referenceBox7 (!canonicalBox7_948.bump)) = canonicalBox7_948 := by decide +kernel

theorem canonicalDecode7_948 : canonicalBox7_948.toKeyData 188160 = keys7Chunk29.get ⟨20, by decide⟩ := by
  change canonicalBox7_948.toKeyData 188160 = ⟨![2, (39 / 28), (10 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(673 / 336), (146 / 105), (3833 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_948 : keySolid (keys7Chunk29.get ⟨20, by decide⟩) = canonicalPose7_948.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_948 (box := canonicalBox7_948) (k := keys7Chunk29.get ⟨20, by decide⟩) (canonicalMatch7_948) (canonicalDecode7_948)

def canonicalPose7_949 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, false, true, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_949 : BoxKey 7 :=
  ⟨![302400, 376320, 309120, 127680, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![302848, 375760, 309540, 128080, 241535, 274960, 108010], false⟩

theorem canonicalMatch7_949 :
    canonicalPose7_949.boxKey 188160 (referenceBox7 (!canonicalBox7_949.bump)) = canonicalBox7_949 := by decide +kernel

theorem canonicalDecode7_949 : canonicalBox7_949.toKeyData 188160 = keys7Chunk29.get ⟨21, by decide⟩ := by
  change canonicalBox7_949.toKeyData 188160 = ⟨![(45 / 28), 2, (23 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(169 / 105), (671 / 336), (737 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_949 : keySolid (keys7Chunk29.get ⟨21, by decide⟩) = canonicalPose7_949.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_949 (box := canonicalBox7_949) (k := keys7Chunk29.get ⟨21, by decide⟩) (canonicalMatch7_949) (canonicalDecode7_949)

def canonicalPose7_950 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, false, true, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_950 : BoxKey 7 :=
  ⟨![309120, 376320, 302400, 107520, 275520, 241920, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![309540, 376880, 302848, 108010, 274960, 241535, 128080], true⟩

theorem canonicalMatch7_950 :
    canonicalPose7_950.boxKey 188160 (referenceBox7 (!canonicalBox7_950.bump)) = canonicalBox7_950 := by decide +kernel

theorem canonicalDecode7_950 : canonicalBox7_950.toKeyData 188160 = keys7Chunk29.get ⟨22, by decide⟩ := by
  change canonicalBox7_950.toKeyData 188160 = ⟨![(23 / 14), 2, (45 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(737 / 448), (673 / 336), (169 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_950 : keySolid (keys7Chunk29.get ⟨22, by decide⟩) = canonicalPose7_950.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_950 (box := canonicalBox7_950) (k := keys7Chunk29.get ⟨22, by decide⟩) (canonicalMatch7_950) (canonicalDecode7_950)

def canonicalPose7_951 : Pose 7 :=
  ⟨canonicalPerm7_6, ![true, true, true, false, false, false, false], ![2, 2, 2, 0, 1, 1, 0]⟩
def canonicalBox7_951 : BoxKey 7 :=
  ⟨![268800, 262080, 376320, 120960, 315840, 322560, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![268310, 261632, 375760, 121380, 316240, 322945, 101360], false⟩

theorem canonicalMatch7_951 :
    canonicalPose7_951.boxKey 188160 (referenceBox7 (!canonicalBox7_951.bump)) = canonicalBox7_951 := by decide +kernel

theorem canonicalDecode7_951 : canonicalBox7_951.toKeyData 188160 = keys7Chunk29.get ⟨23, by decide⟩ := by
  change canonicalBox7_951.toKeyData 188160 = ⟨![(10 / 7), (39 / 28), 2, (9 / 14), (47 / 28), (12 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_951 : keySolid (keys7Chunk29.get ⟨23, by decide⟩) = canonicalPose7_951.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_951 (box := canonicalBox7_951) (k := keys7Chunk29.get ⟨23, by decide⟩) (canonicalMatch7_951) (canonicalDecode7_951)

def canonicalPose7_952 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, true, false, true, true, false], ![2, 1, 2, 0, 2, 2, 0]⟩
def canonicalBox7_952 : BoxKey 7 :=
  ⟨![241920, 315840, 255360, 0, 262080, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![241535, 316240, 254940, 560, 261632, 268310, 101360], false⟩

theorem canonicalMatch7_952 :
    canonicalPose7_952.boxKey 188160 (referenceBox7 (!canonicalBox7_952.bump)) = canonicalBox7_952 := by decide +kernel

theorem canonicalDecode7_952 : canonicalBox7_952.toKeyData 188160 = keys7Chunk29.get ⟨24, by decide⟩ := by
  change canonicalBox7_952.toKeyData 188160 = ⟨![(9 / 7), (47 / 28), (19 / 14), 0, (39 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (146 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_952 : keySolid (keys7Chunk29.get ⟨24, by decide⟩) = canonicalPose7_952.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_952 (box := canonicalBox7_952) (k := keys7Chunk29.get ⟨24, by decide⟩) (canonicalMatch7_952) (canonicalDecode7_952)

def canonicalPose7_953 : Pose 7 :=
  ⟨canonicalPerm7_22, ![false, true, false, false, false, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_953 : BoxKey 7 :=
  ⟨![322560, 248640, 309120, 114240, 376320, 268800, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![322945, 248240, 309540, 114688, 376880, 268310, 101360], true⟩

theorem canonicalMatch7_953 :
    canonicalPose7_953.boxKey 188160 (referenceBox7 (!canonicalBox7_953.bump)) = canonicalBox7_953 := by decide +kernel

theorem canonicalDecode7_953 : canonicalBox7_953.toKeyData 188160 = keys7Chunk29.get ⟨25, by decide⟩ := by
  change canonicalBox7_953.toKeyData 188160 = ⟨![(12 / 7), (37 / 28), (23 / 14), (17 / 28), 2, (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105), (673 / 336), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_953 : keySolid (keys7Chunk29.get ⟨25, by decide⟩) = canonicalPose7_953.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_953 (box := canonicalBox7_953) (k := keys7Chunk29.get ⟨25, by decide⟩) (canonicalMatch7_953) (canonicalDecode7_953)

def canonicalPose7_954 : Pose 7 :=
  ⟨canonicalPerm7_14, ![false, true, false, false, true, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_954 : BoxKey 7 :=
  ⟨![309120, 248640, 322560, 100800, 268800, 376320, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![309540, 248240, 322945, 101360, 268310, 375760, 114688], false⟩

theorem canonicalMatch7_954 :
    canonicalPose7_954.boxKey 188160 (referenceBox7 (!canonicalBox7_954.bump)) = canonicalBox7_954 := by decide +kernel

theorem canonicalDecode7_954 : canonicalBox7_954.toKeyData 188160 = keys7Chunk29.get ⟨26, by decide⟩ := by
  change canonicalBox7_954.toKeyData 188160 = ⟨![(23 / 14), (37 / 28), (12 / 7), (15 / 28), (10 / 7), 2, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336), (3833 / 2688), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_954 : keySolid (keys7Chunk29.get ⟨26, by decide⟩) = canonicalPose7_954.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_954 (box := canonicalBox7_954) (k := keys7Chunk29.get ⟨26, by decide⟩) (canonicalMatch7_954) (canonicalDecode7_954)

def canonicalPose7_955 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, false, true, false, true, true, true], ![2, 1, 2, 0, 2, 2, 0]⟩
def canonicalBox7_955 : BoxKey 7 :=
  ⟨![255360, 315840, 241920, 100800, 268800, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![254940, 316240, 241535, 101360, 268310, 261632, -560], true⟩

theorem canonicalMatch7_955 :
    canonicalPose7_955.boxKey 188160 (referenceBox7 (!canonicalBox7_955.bump)) = canonicalBox7_955 := by decide +kernel

theorem canonicalDecode7_955 : canonicalBox7_955.toKeyData 188160 = keys7Chunk29.get ⟨27, by decide⟩ := by
  change canonicalBox7_955.toKeyData 188160 = ⟨![(19 / 14), (47 / 28), (9 / 7), (15 / 28), (10 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_955 : keySolid (keys7Chunk29.get ⟨27, by decide⟩) = canonicalPose7_955.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_955 (box := canonicalBox7_955) (k := keys7Chunk29.get ⟨27, by decide⟩) (canonicalMatch7_955) (canonicalDecode7_955)

def canonicalPose7_956 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, true, false, false, false, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_956 : BoxKey 7 :=
  ⟨![376320, 262080, 309120, 127680, 322560, 275520, 268800], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![376880, 261632, 309540, 128080, 322945, 274960, 268310], true⟩

theorem canonicalMatch7_956 :
    canonicalPose7_956.boxKey 188160 (referenceBox7 (!canonicalBox7_956.bump)) = canonicalBox7_956 := by decide +kernel

theorem canonicalDecode7_956 : canonicalBox7_956.toKeyData 188160 = keys7Chunk29.get ⟨28, by decide⟩ := by
  change canonicalBox7_956.toKeyData 188160 = ⟨![2, (39 / 28), (23 / 14), (19 / 28), (12 / 7), (41 / 28), (10 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(673 / 336), (146 / 105), (737 / 448), (1601 / 2352), (9227 / 5376), (491 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_956 : keySolid (keys7Chunk29.get ⟨28, by decide⟩) = canonicalPose7_956.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_956 (box := canonicalBox7_956) (k := keys7Chunk29.get ⟨28, by decide⟩) (canonicalMatch7_956) (canonicalDecode7_956)

def canonicalPose7_957 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, true, true, true, true], ![2, 2, 2, 1, 2, 2, 2]⟩
def canonicalBox7_957 : BoxKey 7 :=
  ⟨![262080, 376320, 255360, 60480, 241920, 275520, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![261632, 375760, 254940, 60080, 241535, 274960, 268310], false⟩

theorem canonicalMatch7_957 :
    canonicalPose7_957.boxKey 188160 (referenceBox7 (!canonicalBox7_957.bump)) = canonicalBox7_957 := by decide +kernel

theorem canonicalDecode7_957 : canonicalBox7_957.toKeyData 188160 = keys7Chunk29.get ⟨29, by decide⟩ := by
  change canonicalBox7_957.toKeyData 188160 = ⟨![(39 / 28), 2, (19 / 14), (9 / 28), (9 / 7), (41 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(146 / 105), (671 / 336), (607 / 448), (751 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_957 : keySolid (keys7Chunk29.get ⟨29, by decide⟩) = canonicalPose7_957.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_957 (box := canonicalBox7_957) (k := keys7Chunk29.get ⟨29, by decide⟩) (canonicalMatch7_957) (canonicalDecode7_957)

def canonicalPose7_958 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, true, false, true, true, false], ![1, 2, 2, 0, 2, 2, 1]⟩
def canonicalBox7_958 : BoxKey 7 :=
  ⟨![315840, 255360, 376320, 114240, 268800, 275520, 322560], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![316240, 254940, 375760, 114688, 268310, 274960, 322945], false⟩

theorem canonicalMatch7_958 :
    canonicalPose7_958.boxKey 188160 (referenceBox7 (!canonicalBox7_958.bump)) = canonicalBox7_958 := by decide +kernel

theorem canonicalDecode7_958 : canonicalBox7_958.toKeyData 188160 = keys7Chunk29.get ⟨30, by decide⟩ := by
  change canonicalBox7_958.toKeyData 188160 = ⟨![(47 / 28), (19 / 14), 2, (17 / 28), (10 / 7), (41 / 28), (12 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(3953 / 2352), (607 / 448), (671 / 336), (64 / 105), (3833 / 2688), (491 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_958 : keySolid (keys7Chunk29.get ⟨30, by decide⟩) = canonicalPose7_958.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_958 (box := canonicalBox7_958) (k := keys7Chunk29.get ⟨30, by decide⟩) (canonicalMatch7_958) (canonicalDecode7_958)

def canonicalPose7_959 : Pose 7 :=
  ⟨canonicalPerm7_0, ![true, true, false, true, false, true, true], ![2, 2, 1, 0, 1, 2, 2]⟩
def canonicalBox7_959 : BoxKey 7 :=
  ⟨![275520, 268800, 302400, 0, 309120, 248640, 241920], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![274960, 268310, 302848, -560, 309540, 248240, 241535], true⟩

theorem canonicalMatch7_959 :
    canonicalPose7_959.boxKey 188160 (referenceBox7 (!canonicalBox7_959.bump)) = canonicalBox7_959 := by decide +kernel

theorem canonicalDecode7_959 : canonicalBox7_959.toKeyData 188160 = keys7Chunk29.get ⟨31, by decide⟩ := by
  change canonicalBox7_959.toKeyData 188160 = ⟨![(41 / 28), (10 / 7), (45 / 28), 0, (23 / 14), (37 / 28), (9 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(491 / 336), (3833 / 2688), (169 / 105), (-1 / 336), (737 / 448), (3103 / 2352), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_959 : keySolid (keys7Chunk29.get ⟨31, by decide⟩) = canonicalPose7_959.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_959 (box := canonicalBox7_959) (k := keys7Chunk29.get ⟨31, by decide⟩) (canonicalMatch7_959) (canonicalDecode7_959)

theorem keys7Chunk29_canonical : ∀ k ∈ keys7Chunk29,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk29, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_928, canonicalSolid7_928⟩
  · exact ⟨canonicalPose7_929, canonicalSolid7_929⟩
  · exact ⟨canonicalPose7_930, canonicalSolid7_930⟩
  · exact ⟨canonicalPose7_931, canonicalSolid7_931⟩
  · exact ⟨canonicalPose7_932, canonicalSolid7_932⟩
  · exact ⟨canonicalPose7_933, canonicalSolid7_933⟩
  · exact ⟨canonicalPose7_934, canonicalSolid7_934⟩
  · exact ⟨canonicalPose7_935, canonicalSolid7_935⟩
  · exact ⟨canonicalPose7_936, canonicalSolid7_936⟩
  · exact ⟨canonicalPose7_937, canonicalSolid7_937⟩
  · exact ⟨canonicalPose7_938, canonicalSolid7_938⟩
  · exact ⟨canonicalPose7_939, canonicalSolid7_939⟩
  · exact ⟨canonicalPose7_940, canonicalSolid7_940⟩
  · exact ⟨canonicalPose7_941, canonicalSolid7_941⟩
  · exact ⟨canonicalPose7_942, canonicalSolid7_942⟩
  · exact ⟨canonicalPose7_943, canonicalSolid7_943⟩
  · exact ⟨canonicalPose7_944, canonicalSolid7_944⟩
  · exact ⟨canonicalPose7_945, canonicalSolid7_945⟩
  · exact ⟨canonicalPose7_946, canonicalSolid7_946⟩
  · exact ⟨canonicalPose7_947, canonicalSolid7_947⟩
  · exact ⟨canonicalPose7_948, canonicalSolid7_948⟩
  · exact ⟨canonicalPose7_949, canonicalSolid7_949⟩
  · exact ⟨canonicalPose7_950, canonicalSolid7_950⟩
  · exact ⟨canonicalPose7_951, canonicalSolid7_951⟩
  · exact ⟨canonicalPose7_952, canonicalSolid7_952⟩
  · exact ⟨canonicalPose7_953, canonicalSolid7_953⟩
  · exact ⟨canonicalPose7_954, canonicalSolid7_954⟩
  · exact ⟨canonicalPose7_955, canonicalSolid7_955⟩
  · exact ⟨canonicalPose7_956, canonicalSolid7_956⟩
  · exact ⟨canonicalPose7_957, canonicalSolid7_957⟩
  · exact ⟨canonicalPose7_958, canonicalSolid7_958⟩
  · exact ⟨canonicalPose7_959, canonicalSolid7_959⟩

#print axioms keys7Chunk29_canonical

end SparseMonotiles.Canonical
