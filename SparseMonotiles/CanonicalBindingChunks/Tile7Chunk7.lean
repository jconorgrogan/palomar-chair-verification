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

def canonicalPose7_224 : Pose 7 :=
  ⟨canonicalPerm7_26, ![false, false, false, true, false, false, false], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_224 : BoxKey 7 :=
  ⟨![0, 114240, 309120, 248640, 322560, 100800, 107520], ![0, 2240, 2520, 2800, 3080, 1680, 1960], ![560, 114688, 309540, 248240, 322945, 101360, 108010], false⟩

theorem canonicalMatch7_224 :
    canonicalPose7_224.boxKey 188160 (referenceBox7 (!canonicalBox7_224.bump)) = canonicalBox7_224 := by decide +kernel

theorem canonicalDecode7_224 : canonicalBox7_224.toKeyData 188160 = keys7Chunk7.get ⟨0, by decide⟩ := by
  change canonicalBox7_224.toKeyData 188160 = ⟨![0, (17 / 28), (23 / 14), (37 / 28), (12 / 7), (15 / 28), (4 / 7)], ![0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(1 / 336), (64 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_224 : keySolid (keys7Chunk7.get ⟨0, by decide⟩) = canonicalPose7_224.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_224 (box := canonicalBox7_224) (k := keys7Chunk7.get ⟨0, by decide⟩) (canonicalMatch7_224) (canonicalDecode7_224)

def canonicalPose7_225 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, true, false, true, false, false], ![0, 0, 2, 1, 2, 0, 0]⟩
def canonicalBox7_225 : BoxKey 7 :=
  ⟨![114240, 0, 255360, 315840, 241920, 100800, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, -560, 254940, 316240, 241535, 101360, 108010], true⟩

theorem canonicalMatch7_225 :
    canonicalPose7_225.boxKey 188160 (referenceBox7 (!canonicalBox7_225.bump)) = canonicalBox7_225 := by decide +kernel

theorem canonicalDecode7_225 : canonicalBox7_225.toKeyData 188160 = keys7Chunk7.get ⟨1, by decide⟩ := by
  change canonicalBox7_225.toKeyData 188160 = ⟨![(17 / 28), 0, (19 / 14), (47 / 28), (9 / 7), (15 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (181 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_225 : keySolid (keys7Chunk7.get ⟨1, by decide⟩) = canonicalPose7_225.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_225 (box := canonicalBox7_225) (k := keys7Chunk7.get ⟨1, by decide⟩) (canonicalMatch7_225) (canonicalDecode7_225)

def canonicalPose7_226 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, false, true, true, false, true], ![1, 0, 2, 2, 2, 0, 1]⟩
def canonicalBox7_226 : BoxKey 7 :=
  ⟨![60480, 120960, 376320, 262080, 268800, 100800, 53760], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, 376880, 261632, 268310, 101360, 53375], true⟩

theorem canonicalMatch7_226 :
    canonicalPose7_226.boxKey 188160 (referenceBox7 (!canonicalBox7_226.bump)) = canonicalBox7_226 := by decide +kernel

theorem canonicalDecode7_226 : canonicalBox7_226.toKeyData 188160 = keys7Chunk7.get ⟨2, by decide⟩ := by
  change canonicalBox7_226.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (15 / 28), (2 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (181 / 336), (1525 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_226 : keySolid (keys7Chunk7.get ⟨2, by decide⟩) = canonicalPose7_226.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_226 (box := canonicalBox7_226) (k := keys7Chunk7.get ⟨2, by decide⟩) (canonicalMatch7_226) (canonicalDecode7_226)

def canonicalPose7_227 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, false, true, false, false, false], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_227 : BoxKey 7 :=
  ⟨![100800, 107520, 302400, 376320, 309120, 127680, 134400], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 302848, 375760, 309540, 128080, 134785], false⟩

theorem canonicalMatch7_227 :
    canonicalPose7_227.boxKey 188160 (referenceBox7 (!canonicalBox7_227.bump)) = canonicalBox7_227 := by decide +kernel

theorem canonicalDecode7_227 : canonicalBox7_227.toKeyData 188160 = keys7Chunk7.get ⟨3, by decide⟩ := by
  change canonicalBox7_227.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (45 / 28), 2, (23 / 14), (19 / 28), (5 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (169 / 105), (671 / 336), (737 / 448), (1601 / 2352), (3851 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_227 : keySolid (keys7Chunk7.get ⟨3, by decide⟩) = canonicalPose7_227.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_227 (box := canonicalBox7_227) (k := keys7Chunk7.get ⟨3, by decide⟩) (canonicalMatch7_227) (canonicalDecode7_227)

def canonicalPose7_228 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, false, false, false, false], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_228 : BoxKey 7 :=
  ⟨![134400, 127680, 309120, 376320, 302400, 107520, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 128080, 309540, 376880, 302848, 108010, 101360], true⟩

theorem canonicalMatch7_228 :
    canonicalPose7_228.boxKey 188160 (referenceBox7 (!canonicalBox7_228.bump)) = canonicalBox7_228 := by decide +kernel

theorem canonicalDecode7_228 : canonicalBox7_228.toKeyData 188160 = keys7Chunk7.get ⟨4, by decide⟩ := by
  change canonicalBox7_228.toKeyData 188160 = ⟨![(5 / 7), (19 / 28), (23 / 14), 2, (45 / 28), (4 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (1601 / 2352), (737 / 448), (673 / 336), (169 / 105), (1543 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_228 : keySolid (keys7Chunk7.get ⟨4, by decide⟩) = canonicalPose7_228.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_228 (box := canonicalBox7_228) (k := keys7Chunk7.get ⟨4, by decide⟩) (canonicalMatch7_228) (canonicalDecode7_228)

def canonicalPose7_229 : Pose 7 :=
  ⟨canonicalPerm7_20, ![true, false, true, true, true, false, true], ![1, 0, 2, 2, 2, 0, 1]⟩
def canonicalBox7_229 : BoxKey 7 :=
  ⟨![53760, 100800, 268800, 262080, 376320, 120960, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![53375, 101360, 268310, 261632, 375760, 121380, 60080], false⟩

theorem canonicalMatch7_229 :
    canonicalPose7_229.boxKey 188160 (referenceBox7 (!canonicalBox7_229.bump)) = canonicalBox7_229 := by decide +kernel

theorem canonicalDecode7_229 : canonicalBox7_229.toKeyData 188160 = keys7Chunk7.get ⟨5, by decide⟩ := by
  change canonicalBox7_229.toKeyData 188160 = ⟨![(2 / 7), (15 / 28), (10 / 7), (39 / 28), 2, (9 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(1525 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_229 : keySolid (keys7Chunk7.get ⟨5, by decide⟩) = canonicalPose7_229.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_229 (box := canonicalBox7_229) (k := keys7Chunk7.get ⟨5, by decide⟩) (canonicalMatch7_229) (canonicalDecode7_229)

def canonicalPose7_230 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, false, true, false, true, false, false], ![0, 0, 2, 1, 2, 0, 0]⟩
def canonicalBox7_230 : BoxKey 7 :=
  ⟨![107520, 100800, 241920, 315840, 255360, 0, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 101360, 241535, 316240, 254940, 560, 114688], false⟩

theorem canonicalMatch7_230 :
    canonicalPose7_230.boxKey 188160 (referenceBox7 (!canonicalBox7_230.bump)) = canonicalBox7_230 := by decide +kernel

theorem canonicalDecode7_230 : canonicalBox7_230.toKeyData 188160 = keys7Chunk7.get ⟨6, by decide⟩ := by
  change canonicalBox7_230.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (9 / 7), (47 / 28), (19 / 14), 0, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (181 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (1 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_230 : keySolid (keys7Chunk7.get ⟨6, by decide⟩) = canonicalPose7_230.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_230 (box := canonicalBox7_230) (k := keys7Chunk7.get ⟨6, by decide⟩) (canonicalMatch7_230) (canonicalDecode7_230)

def canonicalPose7_231 : Pose 7 :=
  ⟨canonicalPerm7_4, ![false, false, false, true, false, false, true], ![0, 0, 1, 2, 1, 0, 0]⟩
def canonicalBox7_231 : BoxKey 7 :=
  ⟨![107520, 100800, 322560, 248640, 309120, 114240, 0], ![1960, 1680, 3080, 2800, 2520, 2240, 0], ![108010, 101360, 322945, 248240, 309540, 114688, -560], true⟩

theorem canonicalMatch7_231 :
    canonicalPose7_231.boxKey 188160 (referenceBox7 (!canonicalBox7_231.bump)) = canonicalBox7_231 := by decide +kernel

theorem canonicalDecode7_231 : canonicalBox7_231.toKeyData 188160 = keys7Chunk7.get ⟨7, by decide⟩ := by
  change canonicalBox7_231.toKeyData 188160 = ⟨![(4 / 7), (15 / 28), (12 / 7), (37 / 28), (23 / 14), (17 / 28), 0], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0], ![(1543 / 2688), (181 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (64 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_231 : keySolid (keys7Chunk7.get ⟨7, by decide⟩) = canonicalPose7_231.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_231 (box := canonicalBox7_231) (k := keys7Chunk7.get ⟨7, by decide⟩) (canonicalMatch7_231) (canonicalDecode7_231)

def canonicalPose7_232 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, false, false, true, true, false, true], ![0, 0, 1, 2, 2, 0, 2]⟩
def canonicalBox7_232 : BoxKey 7 :=
  ⟨![0, 120960, 315840, 241920, 275520, 107520, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 121380, 316240, 241535, 274960, 108010, 261632], false⟩

theorem canonicalMatch7_232 :
    canonicalPose7_232.boxKey 188160 (referenceBox7 (!canonicalBox7_232.bump)) = canonicalBox7_232 := by decide +kernel

theorem canonicalDecode7_232 : canonicalBox7_232.toKeyData 188160 = keys7Chunk7.get ⟨8, by decide⟩ := by
  change canonicalBox7_232.toKeyData 188160 = ⟨![0, (9 / 14), (47 / 28), (9 / 7), (41 / 28), (4 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (289 / 448), (3953 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_232 : keySolid (keys7Chunk7.get ⟨8, by decide⟩) = canonicalPose7_232.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_232 (box := canonicalBox7_232) (k := keys7Chunk7.get ⟨8, by decide⟩) (canonicalMatch7_232) (canonicalDecode7_232)

def canonicalPose7_233 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 1, 1]⟩
def canonicalBox7_233 : BoxKey 7 :=
  ⟨![120960, 0, 262080, 268800, 275520, 53760, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 560, 261632, 268310, 274960, 53375, 316240], false⟩

theorem canonicalMatch7_233 :
    canonicalPose7_233.boxKey 188160 (referenceBox7 (!canonicalBox7_233.bump)) = canonicalBox7_233 := by decide +kernel

theorem canonicalDecode7_233 : canonicalBox7_233.toKeyData 188160 = keys7Chunk7.get ⟨9, by decide⟩ := by
  change canonicalBox7_233.toKeyData 188160 = ⟨![(9 / 14), 0, (39 / 28), (10 / 7), (41 / 28), (2 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (1 / 336), (146 / 105), (3833 / 2688), (491 / 336), (1525 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_233 : keySolid (keys7Chunk7.get ⟨9, by decide⟩) = canonicalPose7_233.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_233 (box := canonicalBox7_233) (k := keys7Chunk7.get ⟨9, by decide⟩) (canonicalMatch7_233) (canonicalDecode7_233)

def canonicalPose7_234 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, false, true, false, true], ![0, 1, 2, 1, 2, 0, 2]⟩
def canonicalBox7_234 : BoxKey 7 :=
  ⟨![107520, 73920, 376320, 309120, 248640, 134400, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 73472, 376880, 309540, 248240, 134785, 274960], true⟩

theorem canonicalMatch7_234 :
    canonicalPose7_234.boxKey 188160 (referenceBox7 (!canonicalBox7_234.bump)) = canonicalBox7_234 := by decide +kernel

theorem canonicalDecode7_234 : canonicalBox7_234.toKeyData 188160 = keys7Chunk7.get ⟨10, by decide⟩ := by
  change canonicalBox7_234.toKeyData 188160 = ⟨![(4 / 7), (11 / 28), 2, (23 / 14), (37 / 28), (5 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (41 / 105), (673 / 336), (737 / 448), (3103 / 2352), (3851 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_234 : keySolid (keys7Chunk7.get ⟨10, by decide⟩) = canonicalPose7_234.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_234 (box := canonicalBox7_234) (k := keys7Chunk7.get ⟨10, by decide⟩) (canonicalMatch7_234) (canonicalDecode7_234)

def canonicalPose7_235 : Pose 7 :=
  ⟨canonicalPerm7_17, ![false, true, true, false, true, false, true], ![0, 1, 2, 1, 2, 0, 2]⟩
def canonicalBox7_235 : BoxKey 7 :=
  ⟨![127680, 67200, 376320, 302400, 268800, 100800, 241920], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![128080, 66780, 375760, 302848, 268310, 101360, 241535], false⟩

theorem canonicalMatch7_235 :
    canonicalPose7_235.boxKey 188160 (referenceBox7 (!canonicalBox7_235.bump)) = canonicalBox7_235 := by decide +kernel

theorem canonicalDecode7_235 : canonicalBox7_235.toKeyData 188160 = keys7Chunk7.get ⟨11, by decide⟩ := by
  change canonicalBox7_235.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), 2, (45 / 28), (10 / 7), (15 / 28), (9 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (671 / 336), (169 / 105), (3833 / 2688), (181 / 336), (6901 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_235 : keySolid (keys7Chunk7.get ⟨11, by decide⟩) = canonicalPose7_235.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_235 (box := canonicalBox7_235) (k := keys7Chunk7.get ⟨11, by decide⟩) (canonicalMatch7_235) (canonicalDecode7_235)

def canonicalPose7_236 : Pose 7 :=
  ⟨canonicalPerm7_0, ![false, false, true, false, true, true, false], ![0, 0, 2, 2, 2, 1, 1]⟩
def canonicalBox7_236 : BoxKey 7 :=
  ⟨![100800, 107520, 262080, 376320, 255360, 60480, 322560], ![1680, 1960, 2240, 0, 2520, 2800, 3080], ![101360, 108010, 261632, 376880, 254940, 60080, 322945], true⟩

theorem canonicalMatch7_236 :
    canonicalPose7_236.boxKey 188160 (referenceBox7 (!canonicalBox7_236.bump)) = canonicalBox7_236 := by decide +kernel

theorem canonicalDecode7_236 : canonicalBox7_236.toKeyData 188160 = keys7Chunk7.get ⟨12, by decide⟩ := by
  change canonicalBox7_236.toKeyData 188160 = ⟨![(15 / 28), (4 / 7), (39 / 28), 2, (19 / 14), (9 / 28), (12 / 7)], ![(1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672)], ![(181 / 336), (1543 / 2688), (146 / 105), (673 / 336), (607 / 448), (751 / 2352), (9227 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_236 : keySolid (keys7Chunk7.get ⟨12, by decide⟩) = canonicalPose7_236.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_236 (box := canonicalBox7_236) (k := keys7Chunk7.get ⟨12, by decide⟩) (canonicalMatch7_236) (canonicalDecode7_236)

def canonicalPose7_237 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, false, true, false, false, true], ![0, 0, 1, 2, 2, 0, 2]⟩
def canonicalBox7_237 : BoxKey 7 :=
  ⟨![100800, 134400, 315840, 255360, 376320, 114240, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 316240, 254940, 376880, 114688, 268310], true⟩

theorem canonicalMatch7_237 :
    canonicalPose7_237.boxKey 188160 (referenceBox7 (!canonicalBox7_237.bump)) = canonicalBox7_237 := by decide +kernel

theorem canonicalDecode7_237 : canonicalBox7_237.toKeyData 188160 = keys7Chunk7.get ⟨13, by decide⟩ := by
  change canonicalBox7_237.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (47 / 28), (19 / 14), 2, (17 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (3953 / 2352), (607 / 448), (673 / 336), (64 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_237 : keySolid (keys7Chunk7.get ⟨13, by decide⟩) = canonicalPose7_237.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_237 (box := canonicalBox7_237) (k := keys7Chunk7.get ⟨13, by decide⟩) (canonicalMatch7_237) (canonicalDecode7_237)

def canonicalPose7_238 : Pose 7 :=
  ⟨canonicalPerm7_2, ![false, true, true, false, true, false, true], ![0, 1, 2, 1, 2, 0, 2]⟩
def canonicalBox7_238 : BoxKey 7 :=
  ⟨![100800, 53760, 248640, 309120, 262080, 0, 268800], ![1680, 3080, 2800, 2520, 2240, 0, 1960], ![101360, 53375, 248240, 309540, 261632, 560, 268310], false⟩

theorem canonicalMatch7_238 :
    canonicalPose7_238.boxKey 188160 (referenceBox7 (!canonicalBox7_238.bump)) = canonicalBox7_238 := by decide +kernel

theorem canonicalDecode7_238 : canonicalBox7_238.toKeyData 188160 = keys7Chunk7.get ⟨14, by decide⟩ := by
  change canonicalBox7_238.toKeyData 188160 = ⟨![(15 / 28), (2 / 7), (37 / 28), (23 / 14), (39 / 28), 0, (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96)], ![(181 / 336), (1525 / 5376), (3103 / 2352), (737 / 448), (146 / 105), (1 / 336), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_238 : keySolid (keys7Chunk7.get ⟨14, by decide⟩) = canonicalPose7_238.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_238 (box := canonicalBox7_238) (k := keys7Chunk7.get ⟨14, by decide⟩) (canonicalMatch7_238) (canonicalDecode7_238)

def canonicalPose7_239 : Pose 7 :=
  ⟨canonicalPerm7_9, ![false, true, true, false, true, false, false], ![0, 1, 2, 1, 2, 0, 2]⟩
def canonicalBox7_239 : BoxKey 7 :=
  ⟨![114240, 67200, 248640, 322560, 275520, 107520, 376320], ![2240, 2520, 2800, 3080, 1680, 1960, 0], ![114688, 66780, 248240, 322945, 274960, 108010, 376880], true⟩

theorem canonicalMatch7_239 :
    canonicalPose7_239.boxKey 188160 (referenceBox7 (!canonicalBox7_239.bump)) = canonicalBox7_239 := by decide +kernel

theorem canonicalDecode7_239 : canonicalBox7_239.toKeyData 188160 = keys7Chunk7.get ⟨15, by decide⟩ := by
  change canonicalBox7_239.toKeyData 188160 = ⟨![(17 / 28), (5 / 14), (37 / 28), (12 / 7), (41 / 28), (4 / 7), 2], ![(1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0], ![(64 / 105), (159 / 448), (3103 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_239 : keySolid (keys7Chunk7.get ⟨15, by decide⟩) = canonicalPose7_239.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_239 (box := canonicalBox7_239) (k := keys7Chunk7.get ⟨15, by decide⟩) (canonicalMatch7_239) (canonicalDecode7_239)

def canonicalPose7_240 : Pose 7 :=
  ⟨canonicalPerm7_25, ![false, true, true, true, true, true, true], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_240 : BoxKey 7 :=
  ⟨![0, 73920, 268800, 275520, 241920, 248640, 67200], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![560, 73472, 268310, 274960, 241535, 248240, 66780], false⟩

theorem canonicalMatch7_240 :
    canonicalPose7_240.boxKey 188160 (referenceBox7 (!canonicalBox7_240.bump)) = canonicalBox7_240 := by decide +kernel

theorem canonicalDecode7_240 : canonicalBox7_240.toKeyData 188160 = keys7Chunk7.get ⟨16, by decide⟩ := by
  change canonicalBox7_240.toKeyData 188160 = ⟨![0, (11 / 28), (10 / 7), (41 / 28), (9 / 7), (37 / 28), (5 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(1 / 336), (41 / 105), (3833 / 2688), (491 / 336), (6901 / 5376), (3103 / 2352), (159 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_240 : keySolid (keys7Chunk7.get ⟨16, by decide⟩) = canonicalPose7_240.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_240 (box := canonicalBox7_240) (k := keys7Chunk7.get ⟨16, by decide⟩) (canonicalMatch7_240) (canonicalDecode7_240)

def canonicalPose7_241 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, true, true, true, true], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_241 : BoxKey 7 :=
  ⟨![0, 67200, 248640, 241920, 275520, 268800, 73920], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 66780, 248240, 241535, 274960, 268310, 73472], true⟩

theorem canonicalMatch7_241 :
    canonicalPose7_241.boxKey 188160 (referenceBox7 (!canonicalBox7_241.bump)) = canonicalBox7_241 := by decide +kernel

theorem canonicalDecode7_241 : canonicalBox7_241.toKeyData 188160 = keys7Chunk7.get ⟨17, by decide⟩ := by
  change canonicalBox7_241.toKeyData 188160 = ⟨![0, (5 / 14), (37 / 28), (9 / 7), (41 / 28), (10 / 7), (11 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (159 / 448), (3103 / 2352), (6901 / 5376), (491 / 336), (3833 / 2688), (41 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_241 : keySolid (keys7Chunk7.get ⟨17, by decide⟩) = canonicalPose7_241.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_241 (box := canonicalBox7_241) (k := keys7Chunk7.get ⟨17, by decide⟩) (canonicalMatch7_241) (canonicalDecode7_241)

def canonicalPose7_242 : Pose 7 :=
  ⟨canonicalPerm7_11, ![false, true, true, false, false, true, false], ![0, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_242 : BoxKey 7 :=
  ⟨![114240, 0, 255360, 315840, 322560, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![114688, -560, 254940, 316240, 322945, 274960, 108010], true⟩

theorem canonicalMatch7_242 :
    canonicalPose7_242.boxKey 188160 (referenceBox7 (!canonicalBox7_242.bump)) = canonicalBox7_242 := by decide +kernel

theorem canonicalDecode7_242 : canonicalBox7_242.toKeyData 188160 = keys7Chunk7.get ⟨18, by decide⟩ := by
  change canonicalBox7_242.toKeyData 188160 = ⟨![(17 / 28), 0, (19 / 14), (47 / 28), (12 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(64 / 105), (-1 / 336), (607 / 448), (3953 / 2352), (9227 / 5376), (491 / 336), (1543 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_242 : keySolid (keys7Chunk7.get ⟨18, by decide⟩) = canonicalPose7_242.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_242 (box := canonicalBox7_242) (k := keys7Chunk7.get ⟨18, by decide⟩) (canonicalMatch7_242) (canonicalDecode7_242)

def canonicalPose7_243 : Pose 7 :=
  ⟨canonicalPerm7_17, ![true, false, false, true, true, true, false], ![1, 0, 2, 2, 2, 2, 0]⟩
def canonicalBox7_243 : BoxKey 7 :=
  ⟨![60480, 120960, 376320, 262080, 268800, 275520, 134400], ![2800, 2520, 0, 2240, 1960, 1680, 3080], ![60080, 121380, 376880, 261632, 268310, 274960, 134785], true⟩

theorem canonicalMatch7_243 :
    canonicalPose7_243.boxKey 188160 (referenceBox7 (!canonicalBox7_243.bump)) = canonicalBox7_243 := by decide +kernel

theorem canonicalDecode7_243 : canonicalBox7_243.toKeyData 188160 = keys7Chunk7.get ⟨19, by decide⟩ := by
  change canonicalBox7_243.toKeyData 188160 = ⟨![(9 / 28), (9 / 14), 2, (39 / 28), (10 / 7), (41 / 28), (5 / 7)], ![(5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672)], ![(751 / 2352), (289 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336), (3851 / 5376)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_243 : keySolid (keys7Chunk7.get ⟨19, by decide⟩) = canonicalPose7_243.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_243 (box := canonicalBox7_243) (k := keys7Chunk7.get ⟨19, by decide⟩) (canonicalMatch7_243) (canonicalDecode7_243)

def canonicalPose7_244 : Pose 7 :=
  ⟨canonicalPerm7_16, ![false, true, true, true, true, true, true], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_244 : BoxKey 7 :=
  ⟨![127680, 67200, 262080, 376320, 268800, 275520, 53760], ![2800, 2520, 2240, 0, 1960, 1680, 3080], ![128080, 66780, 261632, 375760, 268310, 274960, 53375], false⟩

theorem canonicalMatch7_244 :
    canonicalPose7_244.boxKey 188160 (referenceBox7 (!canonicalBox7_244.bump)) = canonicalBox7_244 := by decide +kernel

theorem canonicalDecode7_244 : canonicalBox7_244.toKeyData 188160 = keys7Chunk7.get ⟨20, by decide⟩ := by
  change canonicalBox7_244.toKeyData 188160 = ⟨![(19 / 28), (5 / 14), (39 / 28), 2, (10 / 7), (41 / 28), (2 / 7)], ![(5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672)], ![(1601 / 2352), (159 / 448), (146 / 105), (671 / 336), (3833 / 2688), (491 / 336), (1525 / 5376)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_244 : keySolid (keys7Chunk7.get ⟨20, by decide⟩) = canonicalPose7_244.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_244 (box := canonicalBox7_244) (k := keys7Chunk7.get ⟨20, by decide⟩) (canonicalMatch7_244) (canonicalDecode7_244)

def canonicalPose7_245 : Pose 7 :=
  ⟨canonicalPerm7_19, ![false, true, true, true, false, true, true], ![0, 1, 2, 2, 2, 2, 1]⟩
def canonicalBox7_245 : BoxKey 7 :=
  ⟨![127680, 53760, 275520, 268800, 376320, 262080, 67200], ![2800, 3080, 1680, 1960, 0, 2240, 2520], ![128080, 53375, 274960, 268310, 376880, 261632, 66780], true⟩

theorem canonicalMatch7_245 :
    canonicalPose7_245.boxKey 188160 (referenceBox7 (!canonicalBox7_245.bump)) = canonicalBox7_245 := by decide +kernel

theorem canonicalDecode7_245 : canonicalBox7_245.toKeyData 188160 = keys7Chunk7.get ⟨21, by decide⟩ := by
  change canonicalBox7_245.toKeyData 188160 = ⟨![(19 / 28), (2 / 7), (41 / 28), (10 / 7), 2, (39 / 28), (5 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224)], ![(1601 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (673 / 336), (146 / 105), (159 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_245 : keySolid (keys7Chunk7.get ⟨21, by decide⟩) = canonicalPose7_245.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_245 (box := canonicalBox7_245) (k := keys7Chunk7.get ⟨21, by decide⟩) (canonicalMatch7_245) (canonicalDecode7_245)

def canonicalPose7_246 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, true, true, true, true, false], ![1, 0, 2, 2, 2, 2, 0]⟩
def canonicalBox7_246 : BoxKey 7 :=
  ⟨![60480, 134400, 275520, 268800, 262080, 376320, 120960], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 134785, 274960, 268310, 261632, 375760, 121380], false⟩

theorem canonicalMatch7_246 :
    canonicalPose7_246.boxKey 188160 (referenceBox7 (!canonicalBox7_246.bump)) = canonicalBox7_246 := by decide +kernel

theorem canonicalDecode7_246 : canonicalBox7_246.toKeyData 188160 = keys7Chunk7.get ⟨22, by decide⟩ := by
  change canonicalBox7_246.toKeyData 188160 = ⟨![(9 / 28), (5 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (9 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (3851 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (289 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_246 : keySolid (keys7Chunk7.get ⟨22, by decide⟩) = canonicalPose7_246.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_246 (box := canonicalBox7_246) (k := keys7Chunk7.get ⟨22, by decide⟩) (canonicalMatch7_246) (canonicalDecode7_246)

def canonicalPose7_247 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, false, false, true, false], ![0, 0, 2, 1, 1, 2, 0]⟩
def canonicalBox7_247 : BoxKey 7 :=
  ⟨![114240, 107520, 275520, 322560, 315840, 255360, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 274960, 322945, 316240, 254940, 560], false⟩

theorem canonicalMatch7_247 :
    canonicalPose7_247.boxKey 188160 (referenceBox7 (!canonicalBox7_247.bump)) = canonicalBox7_247 := by decide +kernel

theorem canonicalDecode7_247 : canonicalBox7_247.toKeyData 188160 = keys7Chunk7.get ⟨23, by decide⟩ := by
  change canonicalBox7_247.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (41 / 28), (12 / 7), (47 / 28), (19 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (491 / 336), (9227 / 5376), (3953 / 2352), (607 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_247 : keySolid (keys7Chunk7.get ⟨23, by decide⟩) = canonicalPose7_247.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_247 (box := canonicalBox7_247) (k := keys7Chunk7.get ⟨23, by decide⟩) (canonicalMatch7_247) (canonicalDecode7_247)

def canonicalPose7_248 : Pose 7 :=
  ⟨canonicalPerm7_24, ![true, false, true, false, true, false, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_248 : BoxKey 7 :=
  ⟨![0, 107520, 275520, 322560, 248640, 309120, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![-560, 108010, 274960, 322945, 248240, 309540, 261632], true⟩

theorem canonicalMatch7_248 :
    canonicalPose7_248.boxKey 188160 (referenceBox7 (!canonicalBox7_248.bump)) = canonicalBox7_248 := by decide +kernel

theorem canonicalDecode7_248 : canonicalBox7_248.toKeyData 188160 = keys7Chunk7.get ⟨24, by decide⟩ := by
  change canonicalBox7_248.toKeyData 188160 = ⟨![0, (4 / 7), (41 / 28), (12 / 7), (37 / 28), (23 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(-1 / 336), (1543 / 2688), (491 / 336), (9227 / 5376), (3103 / 2352), (737 / 448), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_248 : keySolid (keys7Chunk7.get ⟨24, by decide⟩) = canonicalPose7_248.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_248 (box := canonicalBox7_248) (k := keys7Chunk7.get ⟨24, by decide⟩) (canonicalMatch7_248) (canonicalDecode7_248)

def canonicalPose7_249 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, false, true, false, true, false, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_249 : BoxKey 7 :=
  ⟨![107520, 0, 262080, 309120, 248640, 322560, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, 560, 261632, 309540, 248240, 322945, 274960], false⟩

theorem canonicalMatch7_249 :
    canonicalPose7_249.boxKey 188160 (referenceBox7 (!canonicalBox7_249.bump)) = canonicalBox7_249 := by decide +kernel

theorem canonicalDecode7_249 : canonicalBox7_249.toKeyData 188160 = keys7Chunk7.get ⟨25, by decide⟩ := by
  change canonicalBox7_249.toKeyData 188160 = ⟨![(4 / 7), 0, (39 / 28), (23 / 14), (37 / 28), (12 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (1 / 336), (146 / 105), (737 / 448), (3103 / 2352), (9227 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_249 : keySolid (keys7Chunk7.get ⟨25, by decide⟩) = canonicalPose7_249.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_249 (box := canonicalBox7_249) (k := keys7Chunk7.get ⟨25, by decide⟩) (canonicalMatch7_249) (canonicalDecode7_249)

def canonicalPose7_250 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, false, false, true, false, true, true], ![0, 0, 2, 2, 1, 2, 2]⟩
def canonicalBox7_250 : BoxKey 7 :=
  ⟨![107520, 114240, 376320, 255360, 315840, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 114688, 376880, 254940, 316240, 241535, 274960], true⟩

theorem canonicalMatch7_250 :
    canonicalPose7_250.boxKey 188160 (referenceBox7 (!canonicalBox7_250.bump)) = canonicalBox7_250 := by decide +kernel

theorem canonicalDecode7_250 : canonicalBox7_250.toKeyData 188160 = keys7Chunk7.get ⟨26, by decide⟩ := by
  change canonicalBox7_250.toKeyData 188160 = ⟨![(4 / 7), (17 / 28), 2, (19 / 14), (47 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (64 / 105), (673 / 336), (607 / 448), (3953 / 2352), (6901 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_250 : keySolid (keys7Chunk7.get ⟨26, by decide⟩) = canonicalPose7_250.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_250 (box := canonicalBox7_250) (k := keys7Chunk7.get ⟨26, by decide⟩) (canonicalMatch7_250) (canonicalDecode7_250)

def canonicalPose7_251 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, true, true, false, true, true, true], ![1, 1, 2, 2, 2, 2, 2]⟩
def canonicalBox7_251 : BoxKey 7 :=
  ⟨![53760, 60480, 255360, 376320, 262080, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 60080, 254940, 376880, 261632, 268310, 274960], true⟩

theorem canonicalMatch7_251 :
    canonicalPose7_251.boxKey 188160 (referenceBox7 (!canonicalBox7_251.bump)) = canonicalBox7_251 := by decide +kernel

theorem canonicalDecode7_251 : canonicalBox7_251.toKeyData 188160 = keys7Chunk7.get ⟨27, by decide⟩ := by
  change canonicalBox7_251.toKeyData 188160 = ⟨![(2 / 7), (9 / 28), (19 / 14), 2, (39 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (751 / 2352), (607 / 448), (673 / 336), (146 / 105), (3833 / 2688), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_251 : keySolid (keys7Chunk7.get ⟨27, by decide⟩) = canonicalPose7_251.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_251 (box := canonicalBox7_251) (k := keys7Chunk7.get ⟨27, by decide⟩) (canonicalMatch7_251) (canonicalDecode7_251)

def canonicalPose7_252 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, false, true, false, false, false, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_252 : BoxKey 7 :=
  ⟨![100800, 134400, 248640, 309120, 376320, 302400, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 134785, 248240, 309540, 376880, 302848, 268310], true⟩

theorem canonicalMatch7_252 :
    canonicalPose7_252.boxKey 188160 (referenceBox7 (!canonicalBox7_252.bump)) = canonicalBox7_252 := by decide +kernel

theorem canonicalDecode7_252 : canonicalBox7_252.toKeyData 188160 = keys7Chunk7.get ⟨28, by decide⟩ := by
  change canonicalBox7_252.toKeyData 188160 = ⟨![(15 / 28), (5 / 7), (37 / 28), (23 / 14), 2, (45 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (3851 / 5376), (3103 / 2352), (737 / 448), (673 / 336), (169 / 105), (3833 / 2688)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_252 : keySolid (keys7Chunk7.get ⟨28, by decide⟩) = canonicalPose7_252.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_252 (box := canonicalBox7_252) (k := keys7Chunk7.get ⟨28, by decide⟩) (canonicalMatch7_252) (canonicalDecode7_252)

def canonicalPose7_253 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, false, true, false, true, false, true], ![0, 0, 2, 1, 2, 1, 2]⟩
def canonicalBox7_253 : BoxKey 7 :=
  ⟨![134400, 100800, 268800, 302400, 376320, 309120, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 101360, 268310, 302848, 375760, 309540, 248240], false⟩

theorem canonicalMatch7_253 :
    canonicalPose7_253.boxKey 188160 (referenceBox7 (!canonicalBox7_253.bump)) = canonicalBox7_253 := by decide +kernel

theorem canonicalDecode7_253 : canonicalBox7_253.toKeyData 188160 = keys7Chunk7.get ⟨29, by decide⟩ := by
  change canonicalBox7_253.toKeyData 188160 = ⟨![(5 / 7), (15 / 28), (10 / 7), (45 / 28), 2, (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (181 / 336), (3833 / 2688), (169 / 105), (671 / 336), (737 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_253 : keySolid (keys7Chunk7.get ⟨29, by decide⟩) = canonicalPose7_253.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_253 (box := canonicalBox7_253) (k := keys7Chunk7.get ⟨29, by decide⟩) (canonicalMatch7_253) (canonicalDecode7_253)

def canonicalPose7_254 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, true, true, true, true, true, true], ![1, 1, 2, 2, 2, 2, 2]⟩
def canonicalBox7_254 : BoxKey 7 :=
  ⟨![60480, 53760, 275520, 268800, 262080, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 53375, 274960, 268310, 261632, 375760, 254940], false⟩

theorem canonicalMatch7_254 :
    canonicalPose7_254.boxKey 188160 (referenceBox7 (!canonicalBox7_254.bump)) = canonicalBox7_254 := by decide +kernel

theorem canonicalDecode7_254 : canonicalBox7_254.toKeyData 188160 = keys7Chunk7.get ⟨30, by decide⟩ := by
  change canonicalBox7_254.toKeyData 188160 = ⟨![(9 / 28), (2 / 7), (41 / 28), (10 / 7), (39 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (1525 / 5376), (491 / 336), (3833 / 2688), (146 / 105), (671 / 336), (607 / 448)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_254 : keySolid (keys7Chunk7.get ⟨30, by decide⟩) = canonicalPose7_254.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_254 (box := canonicalBox7_254) (k := keys7Chunk7.get ⟨30, by decide⟩) (canonicalMatch7_254) (canonicalDecode7_254)

def canonicalPose7_255 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, false, true, true, false, true, true], ![0, 0, 2, 2, 1, 2, 2]⟩
def canonicalBox7_255 : BoxKey 7 :=
  ⟨![114240, 107520, 275520, 241920, 315840, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 108010, 274960, 241535, 316240, 254940, 375760], false⟩

theorem canonicalMatch7_255 :
    canonicalPose7_255.boxKey 188160 (referenceBox7 (!canonicalBox7_255.bump)) = canonicalBox7_255 := by decide +kernel

theorem canonicalDecode7_255 : canonicalBox7_255.toKeyData 188160 = keys7Chunk7.get ⟨31, by decide⟩ := by
  change canonicalBox7_255.toKeyData 188160 = ⟨![(17 / 28), (4 / 7), (41 / 28), (9 / 7), (47 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (3953 / 2352), (607 / 448), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_255 : keySolid (keys7Chunk7.get ⟨31, by decide⟩) = canonicalPose7_255.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_255 (box := canonicalBox7_255) (k := keys7Chunk7.get ⟨31, by decide⟩) (canonicalMatch7_255) (canonicalDecode7_255)

theorem keys7Chunk7_canonical : ∀ k ∈ keys7Chunk7,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk7, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_224, canonicalSolid7_224⟩
  · exact ⟨canonicalPose7_225, canonicalSolid7_225⟩
  · exact ⟨canonicalPose7_226, canonicalSolid7_226⟩
  · exact ⟨canonicalPose7_227, canonicalSolid7_227⟩
  · exact ⟨canonicalPose7_228, canonicalSolid7_228⟩
  · exact ⟨canonicalPose7_229, canonicalSolid7_229⟩
  · exact ⟨canonicalPose7_230, canonicalSolid7_230⟩
  · exact ⟨canonicalPose7_231, canonicalSolid7_231⟩
  · exact ⟨canonicalPose7_232, canonicalSolid7_232⟩
  · exact ⟨canonicalPose7_233, canonicalSolid7_233⟩
  · exact ⟨canonicalPose7_234, canonicalSolid7_234⟩
  · exact ⟨canonicalPose7_235, canonicalSolid7_235⟩
  · exact ⟨canonicalPose7_236, canonicalSolid7_236⟩
  · exact ⟨canonicalPose7_237, canonicalSolid7_237⟩
  · exact ⟨canonicalPose7_238, canonicalSolid7_238⟩
  · exact ⟨canonicalPose7_239, canonicalSolid7_239⟩
  · exact ⟨canonicalPose7_240, canonicalSolid7_240⟩
  · exact ⟨canonicalPose7_241, canonicalSolid7_241⟩
  · exact ⟨canonicalPose7_242, canonicalSolid7_242⟩
  · exact ⟨canonicalPose7_243, canonicalSolid7_243⟩
  · exact ⟨canonicalPose7_244, canonicalSolid7_244⟩
  · exact ⟨canonicalPose7_245, canonicalSolid7_245⟩
  · exact ⟨canonicalPose7_246, canonicalSolid7_246⟩
  · exact ⟨canonicalPose7_247, canonicalSolid7_247⟩
  · exact ⟨canonicalPose7_248, canonicalSolid7_248⟩
  · exact ⟨canonicalPose7_249, canonicalSolid7_249⟩
  · exact ⟨canonicalPose7_250, canonicalSolid7_250⟩
  · exact ⟨canonicalPose7_251, canonicalSolid7_251⟩
  · exact ⟨canonicalPose7_252, canonicalSolid7_252⟩
  · exact ⟨canonicalPose7_253, canonicalSolid7_253⟩
  · exact ⟨canonicalPose7_254, canonicalSolid7_254⟩
  · exact ⟨canonicalPose7_255, canonicalSolid7_255⟩

#print axioms keys7Chunk7_canonical

end SparseMonotiles.Canonical
