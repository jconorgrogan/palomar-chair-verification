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

def canonicalPose7_256 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, false, true, true, false], ![0, 2, 0, 0, 1, 1, 0]⟩
def canonicalBox7_256 : BoxKey 7 :=
  ⟨![0, 262080, 107520, 100800, 53760, 60480, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 261632, 108010, 101360, 53375, 60080, 121380], true⟩

theorem canonicalMatch7_256 :
    canonicalPose7_256.boxKey 188160 (referenceBox7 (!canonicalBox7_256.bump)) = canonicalBox7_256 := by decide +kernel

theorem canonicalDecode7_256 : canonicalBox7_256.toKeyData 188160 = keys7Chunk8.get ⟨0, by decide⟩ := by
  change canonicalBox7_256.toKeyData 188160 = ⟨![0, (39 / 28), (4 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (146 / 105), (1543 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_256 : keySolid (keys7Chunk8.get ⟨0, by decide⟩) = canonicalPose7_256.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_256 (box := canonicalBox7_256) (k := keys7Chunk8.get ⟨0, by decide⟩) (canonicalMatch7_256) (canonicalDecode7_256)

def canonicalPose7_257 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, false, false, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_257 : BoxKey 7 :=
  ⟨![73920, 376320, 67200, 127680, 134400, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, 375760, 66780, 128080, 134785, 101360, 108010], false⟩

theorem canonicalMatch7_257 :
    canonicalPose7_257.boxKey 188160 (referenceBox7 (!canonicalBox7_257.bump)) = canonicalBox7_257 := by decide +kernel

theorem canonicalDecode7_257 : canonicalBox7_257.toKeyData 188160 = keys7Chunk8.get ⟨1, by decide⟩ := by
  change canonicalBox7_257.toKeyData 188160 = ⟨![(11 / 28), 2, (5 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (671 / 336), (159 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_257 : keySolid (keys7Chunk8.get ⟨1, by decide⟩) = canonicalPose7_257.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_257 (box := canonicalBox7_257) (k := keys7Chunk8.get ⟨1, by decide⟩) (canonicalMatch7_257) (canonicalDecode7_257)

def canonicalPose7_258 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, false, false, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_258 : BoxKey 7 :=
  ⟨![67200, 376320, 73920, 107520, 100800, 134400, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 376880, 73472, 108010, 101360, 134785, 128080], true⟩

theorem canonicalMatch7_258 :
    canonicalPose7_258.boxKey 188160 (referenceBox7 (!canonicalBox7_258.bump)) = canonicalBox7_258 := by decide +kernel

theorem canonicalDecode7_258 : canonicalBox7_258.toKeyData 188160 = keys7Chunk8.get ⟨2, by decide⟩ := by
  change canonicalBox7_258.toKeyData 188160 = ⟨![(5 / 14), 2, (11 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (673 / 336), (41 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_258 : keySolid (keys7Chunk8.get ⟨2, by decide⟩) = canonicalPose7_258.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_258 (box := canonicalBox7_258) (k := keys7Chunk8.get ⟨2, by decide⟩) (canonicalMatch7_258) (canonicalDecode7_258)

def canonicalPose7_259 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, false, true, true, false], ![0, 2, 0, 0, 1, 1, 0]⟩
def canonicalBox7_259 : BoxKey 7 :=
  ⟨![107520, 262080, 0, 120960, 60480, 53760, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 261632, 560, 121380, 60080, 53375, 101360], false⟩

theorem canonicalMatch7_259 :
    canonicalPose7_259.boxKey 188160 (referenceBox7 (!canonicalBox7_259.bump)) = canonicalBox7_259 := by decide +kernel

theorem canonicalDecode7_259 : canonicalBox7_259.toKeyData 188160 = keys7Chunk8.get ⟨3, by decide⟩ := by
  change canonicalBox7_259.toKeyData 188160 = ⟨![(4 / 7), (39 / 28), 0, (9 / 14), (9 / 28), (2 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_259 : keySolid (keys7Chunk8.get ⟨3, by decide⟩) = canonicalPose7_259.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_259 (box := canonicalBox7_259) (k := keys7Chunk8.get ⟨3, by decide⟩) (canonicalMatch7_259) (canonicalDecode7_259)

def canonicalPose7_260 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, false, false, false, false], ![0, 1, 0, 0, 0, 0, 0]⟩
def canonicalBox7_260 : BoxKey 7 :=
  ⟨![134400, 315840, 120960, 0, 114240, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 316240, 121380, 560, 114688, 108010, 101360], false⟩

theorem canonicalMatch7_260 :
    canonicalPose7_260.boxKey 188160 (referenceBox7 (!canonicalBox7_260.bump)) = canonicalBox7_260 := by decide +kernel

theorem canonicalDecode7_260 : canonicalBox7_260.toKeyData 188160 = keys7Chunk8.get ⟨4, by decide⟩ := by
  change canonicalBox7_260.toKeyData 188160 = ⟨![(5 / 7), (47 / 28), (9 / 14), 0, (17 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (64 / 105), (1543 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_260 : keySolid (keys7Chunk8.get ⟨4, by decide⟩) = canonicalPose7_260.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_260 (box := canonicalBox7_260) (k := keys7Chunk8.get ⟨4, by decide⟩) (canonicalMatch7_260) (canonicalDecode7_260)

def canonicalPose7_261 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, true, true, false, true, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_261 : BoxKey 7 :=
  ⟨![53760, 248640, 67200, 114240, 0, 107520, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 248240, 66780, 114688, -560, 108010, 101360], true⟩

theorem canonicalMatch7_261 :
    canonicalPose7_261.boxKey 188160 (referenceBox7 (!canonicalBox7_261.bump)) = canonicalBox7_261 := by decide +kernel

theorem canonicalDecode7_261 : canonicalBox7_261.toKeyData 188160 = keys7Chunk8.get ⟨5, by decide⟩ := by
  change canonicalBox7_261.toKeyData 188160 = ⟨![(2 / 7), (37 / 28), (5 / 14), (17 / 28), 0, (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (-1 / 336), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_261 : keySolid (keys7Chunk8.get ⟨5, by decide⟩) = canonicalPose7_261.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_261 (box := canonicalBox7_261) (k := keys7Chunk8.get ⟨5, by decide⟩) (canonicalMatch7_261) (canonicalDecode7_261)

def canonicalPose7_262 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, true, true, false, false, false, false], ![1, 2, 1, 0, 0, 0, 0]⟩
def canonicalBox7_262 : BoxKey 7 :=
  ⟨![67200, 248640, 53760, 100800, 107520, 0, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 248240, 53375, 101360, 108010, 560, 114688], false⟩

theorem canonicalMatch7_262 :
    canonicalPose7_262.boxKey 188160 (referenceBox7 (!canonicalBox7_262.bump)) = canonicalBox7_262 := by decide +kernel

theorem canonicalDecode7_262 : canonicalBox7_262.toKeyData 188160 = keys7Chunk8.get ⟨6, by decide⟩ := by
  change canonicalBox7_262.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (2 / 7), (15 / 28), (4 / 7), 0, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (1543 / 2688), (1 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_262 : keySolid (keys7Chunk8.get ⟨6, by decide⟩) = canonicalPose7_262.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_262 (box := canonicalBox7_262) (k := keys7Chunk8.get ⟨6, by decide⟩) (canonicalMatch7_262) (canonicalDecode7_262)

def canonicalPose7_263 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, false, false, true], ![0, 1, 0, 0, 0, 0, 0]⟩
def canonicalBox7_263 : BoxKey 7 :=
  ⟨![120960, 315840, 134400, 100800, 107520, 114240, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 134785, 101360, 108010, 114688, -560], true⟩

theorem canonicalMatch7_263 :
    canonicalPose7_263.boxKey 188160 (referenceBox7 (!canonicalBox7_263.bump)) = canonicalBox7_263 := by decide +kernel

theorem canonicalDecode7_263 : canonicalBox7_263.toKeyData 188160 = keys7Chunk8.get ⟨7, by decide⟩ := by
  change canonicalBox7_263.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (5 / 7), (15 / 28), (4 / 7), (17 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_263 : keySolid (keys7Chunk8.get ⟨7, by decide⟩) = canonicalPose7_263.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_263 (box := canonicalBox7_263) (k := keys7Chunk8.get ⟨7, by decide⟩) (canonicalMatch7_263) (canonicalDecode7_263)

def canonicalPose7_264 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, false, false, false, false, false, false], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_264 : BoxKey 7 :=
  ⟨![0, 302400, 107520, 100800, 134400, 127680, 309120], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 302848, 108010, 101360, 134785, 128080, 309540], false⟩

theorem canonicalMatch7_264 :
    canonicalPose7_264.boxKey 188160 (referenceBox7 (!canonicalBox7_264.bump)) = canonicalBox7_264 := by decide +kernel

theorem canonicalDecode7_264 : canonicalBox7_264.toKeyData 188160 = keys7Chunk8.get ⟨8, by decide⟩ := by
  change canonicalBox7_264.toKeyData 188160 = ⟨![0, (45 / 28), (4 / 7), (15 / 28), (5 / 7), (19 / 28), (23 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (169 / 105), (1543 / 2688), (181 / 336), (3851 / 5376), (1601 / 2352), (737 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_264 : keySolid (keys7Chunk8.get ⟨8, by decide⟩) = canonicalPose7_264.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_264 (box := canonicalBox7_264) (k := keys7Chunk8.get ⟨8, by decide⟩) (canonicalMatch7_264) (canonicalDecode7_264)

def canonicalPose7_265 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, false, false, false, false, false, false], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_265 : BoxKey 7 :=
  ⟨![0, 309120, 127680, 134400, 100800, 107520, 302400], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 309540, 128080, 134785, 101360, 108010, 302848], true⟩

theorem canonicalMatch7_265 :
    canonicalPose7_265.boxKey 188160 (referenceBox7 (!canonicalBox7_265.bump)) = canonicalBox7_265 := by decide +kernel

theorem canonicalDecode7_265 : canonicalBox7_265.toKeyData 188160 = keys7Chunk8.get ⟨9, by decide⟩ := by
  change canonicalBox7_265.toKeyData 188160 = ⟨![0, (23 / 14), (19 / 28), (5 / 7), (15 / 28), (4 / 7), (45 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (737 / 448), (1601 / 2352), (3851 / 5376), (181 / 336), (1543 / 2688), (169 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_265 : keySolid (keys7Chunk8.get ⟨9, by decide⟩) = canonicalPose7_265.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_265 (box := canonicalBox7_265) (k := keys7Chunk8.get ⟨9, by decide⟩) (canonicalMatch7_265) (canonicalDecode7_265)

def canonicalPose7_266 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, false, false, true, true, false, true], ![0, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_266 : BoxKey 7 :=
  ⟨![114240, 376320, 120960, 60480, 53760, 100800, 268800], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 376880, 121380, 60080, 53375, 101360, 268310], true⟩

theorem canonicalMatch7_266 :
    canonicalPose7_266.boxKey 188160 (referenceBox7 (!canonicalBox7_266.bump)) = canonicalBox7_266 := by decide +kernel

theorem canonicalDecode7_266 : canonicalBox7_266.toKeyData 188160 = keys7Chunk8.get ⟨10, by decide⟩ := by
  change canonicalBox7_266.toKeyData 188160 = ⟨![(17 / 28), 2, (9 / 14), (9 / 28), (2 / 7), (15 / 28), (10 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (673 / 336), (289 / 448), (751 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_266 : keySolid (keys7Chunk8.get ⟨10, by decide⟩) = canonicalPose7_266.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_266 (box := canonicalBox7_266) (k := keys7Chunk8.get ⟨10, by decide⟩) (canonicalMatch7_266) (canonicalDecode7_266)

def canonicalPose7_267 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, true, false, false, false, true], ![1, 2, 0, 0, 0, 0, 2]⟩
def canonicalBox7_267 : BoxKey 7 :=
  ⟨![60480, 255360, 0, 114240, 107520, 100800, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, -560, 114688, 108010, 101360, 241535], true⟩

theorem canonicalMatch7_267 :
    canonicalPose7_267.boxKey 188160 (referenceBox7 (!canonicalBox7_267.bump)) = canonicalBox7_267 := by decide +kernel

theorem canonicalDecode7_267 : canonicalBox7_267.toKeyData 188160 = keys7Chunk8.get ⟨11, by decide⟩ := by
  change canonicalBox7_267.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (15 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (-1 / 336), (64 / 105), (1543 / 2688), (181 / 336), (6901 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_267 : keySolid (keys7Chunk8.get ⟨11, by decide⟩) = canonicalPose7_267.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_267 (box := canonicalBox7_267) (k := keys7Chunk8.get ⟨11, by decide⟩) (canonicalMatch7_267) (canonicalDecode7_267)

def canonicalPose7_268 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, false, false, false, false, false, false], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_268 : BoxKey 7 :=
  ⟨![127680, 309120, 114240, 0, 107520, 100800, 322560], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 309540, 114688, 560, 108010, 101360, 322945], false⟩

theorem canonicalMatch7_268 :
    canonicalPose7_268.boxKey 188160 (referenceBox7 (!canonicalBox7_268.bump)) = canonicalBox7_268 := by decide +kernel

theorem canonicalDecode7_268 : canonicalBox7_268.toKeyData 188160 = keys7Chunk8.get ⟨12, by decide⟩ := by
  change canonicalBox7_268.toKeyData 188160 = ⟨![(19 / 28), (23 / 14), (17 / 28), 0, (4 / 7), (15 / 28), (12 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (737 / 448), (64 / 105), (1 / 336), (1543 / 2688), (181 / 336), (9227 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_268 : keySolid (keys7Chunk8.get ⟨12, by decide⟩) = canonicalPose7_268.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_268 (box := canonicalBox7_268) (k := keys7Chunk8.get ⟨12, by decide⟩) (canonicalMatch7_268) (canonicalDecode7_268)

def canonicalPose7_269 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, false, false, false, true, false, false], ![0, 1, 0, 0, 0, 0, 1]⟩
def canonicalBox7_269 : BoxKey 7 :=
  ⟨![127680, 322560, 100800, 107520, 0, 114240, 309120], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 322945, 101360, 108010, -560, 114688, 309540], true⟩

theorem canonicalMatch7_269 :
    canonicalPose7_269.boxKey 188160 (referenceBox7 (!canonicalBox7_269.bump)) = canonicalBox7_269 := by decide +kernel

theorem canonicalDecode7_269 : canonicalBox7_269.toKeyData 188160 = keys7Chunk8.get ⟨13, by decide⟩ := by
  change canonicalBox7_269.toKeyData 188160 = ⟨![(19 / 28), (12 / 7), (15 / 28), (4 / 7), 0, (17 / 28), (23 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (-1 / 336), (64 / 105), (737 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_269 : keySolid (keys7Chunk8.get ⟨13, by decide⟩) = canonicalPose7_269.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_269 (box := canonicalBox7_269) (k := keys7Chunk8.get ⟨13, by decide⟩) (canonicalMatch7_269) (canonicalDecode7_269)

def canonicalPose7_270 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, false, false, false, false, true], ![1, 2, 0, 0, 0, 0, 2]⟩
def canonicalBox7_270 : BoxKey 7 :=
  ⟨![60480, 241920, 100800, 107520, 114240, 0, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 241535, 101360, 108010, 114688, 560, 254940], false⟩

theorem canonicalMatch7_270 :
    canonicalPose7_270.boxKey 188160 (referenceBox7 (!canonicalBox7_270.bump)) = canonicalBox7_270 := by decide +kernel

theorem canonicalDecode7_270 : canonicalBox7_270.toKeyData 188160 = keys7Chunk8.get ⟨14, by decide⟩ := by
  change canonicalBox7_270.toKeyData 188160 = ⟨![(9 / 28), (9 / 7), (15 / 28), (4 / 7), (17 / 28), 0, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (1 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_270 : keySolid (keys7Chunk8.get ⟨14, by decide⟩) = canonicalPose7_270.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_270 (box := canonicalBox7_270) (k := keys7Chunk8.get ⟨14, by decide⟩) (canonicalMatch7_270) (canonicalDecode7_270)

def canonicalPose7_271 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, true, true, false, true], ![0, 2, 0, 1, 1, 0, 2]⟩
def canonicalBox7_271 : BoxKey 7 :=
  ⟨![114240, 268800, 100800, 53760, 60480, 120960, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 268310, 101360, 53375, 60080, 121380, 375760], false⟩

theorem canonicalMatch7_271 :
    canonicalPose7_271.boxKey 188160 (referenceBox7 (!canonicalBox7_271.bump)) = canonicalBox7_271 := by decide +kernel

theorem canonicalDecode7_271 : canonicalBox7_271.toKeyData 188160 = keys7Chunk8.get ⟨15, by decide⟩ := by
  change canonicalBox7_271.toKeyData 188160 = ⟨![(17 / 28), (10 / 7), (15 / 28), (2 / 7), (9 / 28), (9 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (3833 / 2688), (181 / 336), (1525 / 5376), (751 / 2352), (289 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_271 : keySolid (keys7Chunk8.get ⟨15, by decide⟩) = canonicalPose7_271.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_271 (box := canonicalBox7_271) (k := keys7Chunk8.get ⟨15, by decide⟩) (canonicalMatch7_271) (canonicalDecode7_271)

def canonicalPose7_272 : Pose 7 :=
  ⟨canonicalPerm7_26, ![true, true, true, false, true, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_272 : BoxKey 7 :=
  ⟨![0, 262080, 67200, 127680, 53760, 275520, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![-560, 261632, 66780, 128080, 53375, 274960, 108010], true⟩

theorem canonicalMatch7_272 :
    canonicalPose7_272.boxKey 188160 (referenceBox7 (!canonicalBox7_272.bump)) = canonicalBox7_272 := by decide +kernel

theorem canonicalDecode7_272 : canonicalBox7_272.toKeyData 188160 = keys7Chunk8.get ⟨16, by decide⟩ := by
  change canonicalBox7_272.toKeyData 188160 = ⟨![0, (39 / 28), (5 / 14), (19 / 28), (2 / 7), (41 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(-1 / 336), (146 / 105), (159 / 448), (1601 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_272 : keySolid (keys7Chunk8.get ⟨16, by decide⟩) = canonicalPose7_272.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_272 (box := canonicalBox7_272) (k := keys7Chunk8.get ⟨16, by decide⟩) (canonicalMatch7_272) (canonicalDecode7_272)

def canonicalPose7_273 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, false, true, false, true, false], ![0, 2, 0, 1, 0, 2, 0]⟩
def canonicalBox7_273 : BoxKey 7 :=
  ⟨![114240, 376320, 120960, 60480, 134400, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, 375760, 121380, 60080, 134785, 274960, 108010], false⟩

theorem canonicalMatch7_273 :
    canonicalPose7_273.boxKey 188160 (referenceBox7 (!canonicalBox7_273.bump)) = canonicalBox7_273 := by decide +kernel

theorem canonicalDecode7_273 : canonicalBox7_273.toKeyData 188160 = keys7Chunk8.get ⟨17, by decide⟩ := by
  change canonicalBox7_273.toKeyData 188160 = ⟨![(17 / 28), 2, (9 / 14), (9 / 28), (5 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (671 / 336), (289 / 448), (751 / 2352), (3851 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_273 : keySolid (keys7Chunk8.get ⟨17, by decide⟩) = canonicalPose7_273.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_273 (box := canonicalBox7_273) (k := keys7Chunk8.get ⟨17, by decide⟩) (canonicalMatch7_273) (canonicalDecode7_273)

def canonicalPose7_274 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, true, false, false, false, true, true], ![1, 2, 0, 0, 0, 2, 1]⟩
def canonicalBox7_274 : BoxKey 7 :=
  ⟨![60480, 255360, 0, 114240, 107520, 275520, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 254940, 560, 114688, 108010, 274960, 53375], false⟩

theorem canonicalMatch7_274 :
    canonicalPose7_274.boxKey 188160 (referenceBox7 (!canonicalBox7_274.bump)) = canonicalBox7_274 := by decide +kernel

theorem canonicalDecode7_274 : canonicalBox7_274.toKeyData 188160 = keys7Chunk8.get ⟨18, by decide⟩ := by
  change canonicalBox7_274.toKeyData 188160 = ⟨![(9 / 28), (19 / 14), 0, (17 / 28), (4 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (607 / 448), (1 / 336), (64 / 105), (1543 / 2688), (491 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_274 : keySolid (keys7Chunk8.get ⟨18, by decide⟩) = canonicalPose7_274.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_274 (box := canonicalBox7_274) (k := keys7Chunk8.get ⟨18, by decide⟩) (canonicalMatch7_274) (canonicalDecode7_274)

def canonicalPose7_275 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, true, true, true, true, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_275 : BoxKey 7 :=
  ⟨![100800, 268800, 73920, 0, 67200, 248640, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 268310, 73472, -560, 66780, 248240, 134785], true⟩

theorem canonicalMatch7_275 :
    canonicalPose7_275.boxKey 188160 (referenceBox7 (!canonicalBox7_275.bump)) = canonicalBox7_275 := by decide +kernel

theorem canonicalDecode7_275 : canonicalBox7_275.toKeyData 188160 = keys7Chunk8.get ⟨19, by decide⟩ := by
  change canonicalBox7_275.toKeyData 188160 = ⟨![(15 / 28), (10 / 7), (11 / 28), 0, (5 / 14), (37 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (3833 / 2688), (41 / 105), (-1 / 336), (159 / 448), (3103 / 2352), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_275 : keySolid (keys7Chunk8.get ⟨19, by decide⟩) = canonicalPose7_275.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_275 (box := canonicalBox7_275) (k := keys7Chunk8.get ⟨19, by decide⟩) (canonicalMatch7_275) (canonicalDecode7_275)

def canonicalPose7_276 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, true, true, false, true, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_276 : BoxKey 7 :=
  ⟨![134400, 248640, 67200, 0, 73920, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 248240, 66780, 560, 73472, 268310, 101360], false⟩

theorem canonicalMatch7_276 :
    canonicalPose7_276.boxKey 188160 (referenceBox7 (!canonicalBox7_276.bump)) = canonicalBox7_276 := by decide +kernel

theorem canonicalDecode7_276 : canonicalBox7_276.toKeyData 188160 = keys7Chunk8.get ⟨20, by decide⟩ := by
  change canonicalBox7_276.toKeyData 188160 = ⟨![(5 / 7), (37 / 28), (5 / 14), 0, (11 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3103 / 2352), (159 / 448), (1 / 336), (41 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_276 : keySolid (keys7Chunk8.get ⟨20, by decide⟩) = canonicalPose7_276.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_276 (box := canonicalBox7_276) (k := keys7Chunk8.get ⟨20, by decide⟩) (canonicalMatch7_276) (canonicalDecode7_276)

def canonicalPose7_277 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, true, false, false, true, true, true], ![1, 2, 0, 0, 0, 2, 1]⟩
def canonicalBox7_277 : BoxKey 7 :=
  ⟨![53760, 275520, 107520, 114240, 0, 255360, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 274960, 108010, 114688, -560, 254940, 60080], true⟩

theorem canonicalMatch7_277 :
    canonicalPose7_277.boxKey 188160 (referenceBox7 (!canonicalBox7_277.bump)) = canonicalBox7_277 := by decide +kernel

theorem canonicalDecode7_277 : canonicalBox7_277.toKeyData 188160 = keys7Chunk8.get ⟨21, by decide⟩ := by
  change canonicalBox7_277.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (4 / 7), (17 / 28), 0, (19 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (-1 / 336), (607 / 448), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_277 : keySolid (keys7Chunk8.get ⟨21, by decide⟩) = canonicalPose7_277.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_277 (box := canonicalBox7_277) (k := keys7Chunk8.get ⟨21, by decide⟩) (canonicalMatch7_277) (canonicalDecode7_277)

def canonicalPose7_278 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, false, true, false, false, false], ![0, 2, 0, 1, 0, 2, 0]⟩
def canonicalBox7_278 : BoxKey 7 :=
  ⟨![107520, 275520, 134400, 60480, 120960, 376320, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 134785, 60080, 121380, 376880, 114688], true⟩

theorem canonicalMatch7_278 :
    canonicalPose7_278.boxKey 188160 (referenceBox7 (!canonicalBox7_278.bump)) = canonicalBox7_278 := by decide +kernel

theorem canonicalDecode7_278 : canonicalBox7_278.toKeyData 188160 = keys7Chunk8.get ⟨22, by decide⟩ := by
  change canonicalBox7_278.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (5 / 7), (9 / 28), (9 / 14), 2, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (3851 / 5376), (751 / 2352), (289 / 448), (673 / 336), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_278 : keySolid (keys7Chunk8.get ⟨22, by decide⟩) = canonicalPose7_278.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_278 (box := canonicalBox7_278) (k := keys7Chunk8.get ⟨22, by decide⟩) (canonicalMatch7_278) (canonicalDecode7_278)

def canonicalPose7_279 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, true, true, false, true, true, false], ![0, 2, 1, 0, 1, 2, 0]⟩
def canonicalBox7_279 : BoxKey 7 :=
  ⟨![107520, 275520, 53760, 127680, 67200, 262080, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 274960, 53375, 128080, 66780, 261632, 560], false⟩

theorem canonicalMatch7_279 :
    canonicalPose7_279.boxKey 188160 (referenceBox7 (!canonicalBox7_279.bump)) = canonicalBox7_279 := by decide +kernel

theorem canonicalDecode7_279 : canonicalBox7_279.toKeyData 188160 = keys7Chunk8.get ⟨23, by decide⟩ := by
  change canonicalBox7_279.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (2 / 7), (19 / 28), (5 / 14), (39 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352), (159 / 448), (146 / 105), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_279 : keySolid (keys7Chunk8.get ⟨23, by decide⟩) = canonicalPose7_279.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_279 (box := canonicalBox7_279) (k := keys7Chunk8.get ⟨23, by decide⟩) (canonicalMatch7_279) (canonicalDecode7_279)

def canonicalPose7_280 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, true, false, true, false, false, true], ![0, 2, 0, 1, 0, 1, 2]⟩
def canonicalBox7_280 : BoxKey 7 :=
  ⟨![0, 268800, 100800, 53760, 127680, 309120, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![-560, 268310, 101360, 53375, 128080, 309540, 261632], true⟩

theorem canonicalMatch7_280 :
    canonicalPose7_280.boxKey 188160 (referenceBox7 (!canonicalBox7_280.bump)) = canonicalBox7_280 := by decide +kernel

theorem canonicalDecode7_280 : canonicalBox7_280.toKeyData 188160 = keys7Chunk8.get ⟨24, by decide⟩ := by
  change canonicalBox7_280.toKeyData 188160 = ⟨![0, (10 / 7), (15 / 28), (2 / 7), (19 / 28), (23 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(-1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (1601 / 2352), (737 / 448), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_280 : keySolid (keys7Chunk8.get ⟨24, by decide⟩) = canonicalPose7_280.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_280 (box := canonicalBox7_280) (k := keys7Chunk8.get ⟨24, by decide⟩) (canonicalMatch7_280) (canonicalDecode7_280)

def canonicalPose7_281 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, true, false, true, false, false, true], ![0, 2, 0, 1, 0, 1, 2]⟩
def canonicalBox7_281 : BoxKey 7 :=
  ⟨![107520, 376320, 114240, 67200, 127680, 322560, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, 375760, 114688, 66780, 128080, 322945, 274960], false⟩

theorem canonicalMatch7_281 :
    canonicalPose7_281.boxKey 188160 (referenceBox7 (!canonicalBox7_281.bump)) = canonicalBox7_281 := by decide +kernel

theorem canonicalDecode7_281 : canonicalBox7_281.toKeyData 188160 = keys7Chunk8.get ⟨25, by decide⟩ := by
  change canonicalBox7_281.toKeyData 188160 = ⟨![(4 / 7), 2, (17 / 28), (5 / 14), (19 / 28), (12 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (671 / 336), (64 / 105), (159 / 448), (1601 / 2352), (9227 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_281 : keySolid (keys7Chunk8.get ⟨25, by decide⟩) = canonicalPose7_281.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_281 (box := canonicalBox7_281) (k := keys7Chunk8.get ⟨25, by decide⟩) (canonicalMatch7_281) (canonicalDecode7_281)

def canonicalPose7_282 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, true, false, true, true, true], ![0, 2, 0, 0, 1, 2, 2]⟩
def canonicalBox7_282 : BoxKey 7 :=
  ⟨![107520, 262080, 0, 120960, 60480, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 261632, -560, 121380, 60080, 241535, 274960], true⟩

theorem canonicalMatch7_282 :
    canonicalPose7_282.boxKey 188160 (referenceBox7 (!canonicalBox7_282.bump)) = canonicalBox7_282 := by decide +kernel

theorem canonicalDecode7_282 : canonicalBox7_282.toKeyData 188160 = keys7Chunk8.get ⟨26, by decide⟩ := by
  change canonicalBox7_282.toKeyData 188160 = ⟨![(4 / 7), (39 / 28), 0, (9 / 14), (9 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (146 / 105), (-1 / 336), (289 / 448), (751 / 2352), (6901 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_282 : keySolid (keys7Chunk8.get ⟨26, by decide⟩) = canonicalPose7_282.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_282 (box := canonicalBox7_282) (k := keys7Chunk8.get ⟨26, by decide⟩) (canonicalMatch7_282) (canonicalDecode7_282)

def canonicalPose7_283 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, false, true, false, true, true], ![1, 1, 0, 0, 0, 2, 2]⟩
def canonicalBox7_283 : BoxKey 7 :=
  ⟨![53760, 315840, 120960, 0, 114240, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 316240, 121380, -560, 114688, 268310, 274960], true⟩

theorem canonicalMatch7_283 :
    canonicalPose7_283.boxKey 188160 (referenceBox7 (!canonicalBox7_283.bump)) = canonicalBox7_283 := by decide +kernel

theorem canonicalDecode7_283 : canonicalBox7_283.toKeyData 188160 = keys7Chunk8.get ⟨27, by decide⟩ := by
  change canonicalBox7_283.toKeyData 188160 = ⟨![(2 / 7), (47 / 28), (9 / 14), 0, (17 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (3953 / 2352), (289 / 448), (-1 / 336), (64 / 105), (3833 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_283 : keySolid (keys7Chunk8.get ⟨27, by decide⟩) = canonicalPose7_283.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_283 (box := canonicalBox7_283) (k := keys7Chunk8.get ⟨27, by decide⟩) (canonicalMatch7_283) (canonicalDecode7_283)

def canonicalPose7_284 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, false, true, true, false, true], ![0, 2, 0, 1, 0, 1, 2]⟩
def canonicalBox7_284 : BoxKey 7 :=
  ⟨![100800, 241920, 127680, 67200, 0, 302400, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 241535, 128080, 66780, -560, 302848, 268310], true⟩

theorem canonicalMatch7_284 :
    canonicalPose7_284.boxKey 188160 (referenceBox7 (!canonicalBox7_284.bump)) = canonicalBox7_284 := by decide +kernel

theorem canonicalDecode7_284 : canonicalBox7_284.toKeyData 188160 = keys7Chunk8.get ⟨28, by decide⟩ := by
  change canonicalBox7_284.toKeyData 188160 = ⟨![(15 / 28), (9 / 7), (19 / 28), (5 / 14), 0, (45 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (-1 / 336), (169 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_284 : keySolid (keys7Chunk8.get ⟨28, by decide⟩) = canonicalPose7_284.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_284 (box := canonicalBox7_284) (k := keys7Chunk8.get ⟨28, by decide⟩) (canonicalMatch7_284) (canonicalDecode7_284)

def canonicalPose7_285 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, false, true, false, false, true], ![0, 2, 0, 1, 0, 1, 2]⟩
def canonicalBox7_285 : BoxKey 7 :=
  ⟨![134400, 275520, 107520, 73920, 0, 309120, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 274960, 108010, 73472, 560, 309540, 248240], false⟩

theorem canonicalMatch7_285 :
    canonicalPose7_285.boxKey 188160 (referenceBox7 (!canonicalBox7_285.bump)) = canonicalBox7_285 := by decide +kernel

theorem canonicalDecode7_285 : canonicalBox7_285.toKeyData 188160 = keys7Chunk8.get ⟨29, by decide⟩ := by
  change canonicalBox7_285.toKeyData 188160 = ⟨![(5 / 7), (41 / 28), (4 / 7), (11 / 28), 0, (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (1 / 336), (737 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_285 : keySolid (keys7Chunk8.get ⟨29, by decide⟩) = canonicalPose7_285.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_285 (box := canonicalBox7_285) (k := keys7Chunk8.get ⟨29, by decide⟩) (canonicalMatch7_285) (canonicalDecode7_285)

def canonicalPose7_286 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, false, false, true, true], ![1, 1, 0, 0, 0, 2, 2]⟩
def canonicalBox7_286 : BoxKey 7 :=
  ⟨![60480, 322560, 100800, 107520, 114240, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 322945, 101360, 108010, 114688, 375760, 254940], false⟩

theorem canonicalMatch7_286 :
    canonicalPose7_286.boxKey 188160 (referenceBox7 (!canonicalBox7_286.bump)) = canonicalBox7_286 := by decide +kernel

theorem canonicalDecode7_286 : canonicalBox7_286.toKeyData 188160 = keys7Chunk8.get ⟨30, by decide⟩ := by
  change canonicalBox7_286.toKeyData 188160 = ⟨![(9 / 28), (12 / 7), (15 / 28), (4 / 7), (17 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (64 / 105), (671 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_286 : keySolid (keys7Chunk8.get ⟨30, by decide⟩) = canonicalPose7_286.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_286 (box := canonicalBox7_286) (k := keys7Chunk8.get ⟨30, by decide⟩) (canonicalMatch7_286) (canonicalDecode7_286)

def canonicalPose7_287 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, false, true, true, true], ![0, 2, 0, 0, 1, 2, 2]⟩
def canonicalBox7_287 : BoxKey 7 :=
  ⟨![114240, 268800, 100800, 134400, 60480, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 268310, 101360, 134785, 60080, 254940, 375760], false⟩

theorem canonicalMatch7_287 :
    canonicalPose7_287.boxKey 188160 (referenceBox7 (!canonicalBox7_287.bump)) = canonicalBox7_287 := by decide +kernel

theorem canonicalDecode7_287 : canonicalBox7_287.toKeyData 188160 = keys7Chunk8.get ⟨31, by decide⟩ := by
  change canonicalBox7_287.toKeyData 188160 = ⟨![(17 / 28), (10 / 7), (15 / 28), (5 / 7), (9 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (751 / 2352), (607 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_287 : keySolid (keys7Chunk8.get ⟨31, by decide⟩) = canonicalPose7_287.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_287 (box := canonicalBox7_287) (k := keys7Chunk8.get ⟨31, by decide⟩) (canonicalMatch7_287) (canonicalDecode7_287)

theorem keys7Chunk8_canonical : ∀ k ∈ keys7Chunk8,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk8, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_256, canonicalSolid7_256⟩
  · exact ⟨canonicalPose7_257, canonicalSolid7_257⟩
  · exact ⟨canonicalPose7_258, canonicalSolid7_258⟩
  · exact ⟨canonicalPose7_259, canonicalSolid7_259⟩
  · exact ⟨canonicalPose7_260, canonicalSolid7_260⟩
  · exact ⟨canonicalPose7_261, canonicalSolid7_261⟩
  · exact ⟨canonicalPose7_262, canonicalSolid7_262⟩
  · exact ⟨canonicalPose7_263, canonicalSolid7_263⟩
  · exact ⟨canonicalPose7_264, canonicalSolid7_264⟩
  · exact ⟨canonicalPose7_265, canonicalSolid7_265⟩
  · exact ⟨canonicalPose7_266, canonicalSolid7_266⟩
  · exact ⟨canonicalPose7_267, canonicalSolid7_267⟩
  · exact ⟨canonicalPose7_268, canonicalSolid7_268⟩
  · exact ⟨canonicalPose7_269, canonicalSolid7_269⟩
  · exact ⟨canonicalPose7_270, canonicalSolid7_270⟩
  · exact ⟨canonicalPose7_271, canonicalSolid7_271⟩
  · exact ⟨canonicalPose7_272, canonicalSolid7_272⟩
  · exact ⟨canonicalPose7_273, canonicalSolid7_273⟩
  · exact ⟨canonicalPose7_274, canonicalSolid7_274⟩
  · exact ⟨canonicalPose7_275, canonicalSolid7_275⟩
  · exact ⟨canonicalPose7_276, canonicalSolid7_276⟩
  · exact ⟨canonicalPose7_277, canonicalSolid7_277⟩
  · exact ⟨canonicalPose7_278, canonicalSolid7_278⟩
  · exact ⟨canonicalPose7_279, canonicalSolid7_279⟩
  · exact ⟨canonicalPose7_280, canonicalSolid7_280⟩
  · exact ⟨canonicalPose7_281, canonicalSolid7_281⟩
  · exact ⟨canonicalPose7_282, canonicalSolid7_282⟩
  · exact ⟨canonicalPose7_283, canonicalSolid7_283⟩
  · exact ⟨canonicalPose7_284, canonicalSolid7_284⟩
  · exact ⟨canonicalPose7_285, canonicalSolid7_285⟩
  · exact ⟨canonicalPose7_286, canonicalSolid7_286⟩
  · exact ⟨canonicalPose7_287, canonicalSolid7_287⟩

#print axioms keys7Chunk8_canonical

end SparseMonotiles.Canonical
