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

def canonicalPose7_288 : Pose 7 :=
  ⟨canonicalPerm7_27, ![true, true, true, true, true, false, false], ![0, 2, 1, 1, 2, 0, 0]⟩
def canonicalBox7_288 : BoxKey 7 :=
  ⟨![0, 255360, 60480, 53760, 275520, 107520, 114240], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![-560, 254940, 60080, 53375, 274960, 108010, 114688], true⟩

theorem canonicalMatch7_288 :
    canonicalPose7_288.boxKey 188160 (referenceBox7 (!canonicalBox7_288.bump)) = canonicalBox7_288 := by decide +kernel

theorem canonicalDecode7_288 : canonicalBox7_288.toKeyData 188160 = keys7Chunk9.get ⟨0, by decide⟩ := by
  change canonicalBox7_288.toKeyData 188160 = ⟨![0, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (4 / 7), (17 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(-1 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (64 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_288 : keySolid (keys7Chunk9.get ⟨0, by decide⟩) = canonicalPose7_288.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_288 (box := canonicalBox7_288) (k := keys7Chunk9.get ⟨0, by decide⟩) (canonicalMatch7_288) (canonicalDecode7_288)

def canonicalPose7_289 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, false, false, false, true, false, true], ![0, 2, 0, 0, 2, 0, 1]⟩
def canonicalBox7_289 : BoxKey 7 :=
  ⟨![120960, 376320, 114240, 107520, 275520, 134400, 60480], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 376880, 114688, 108010, 274960, 134785, 60080], true⟩

theorem canonicalMatch7_289 :
    canonicalPose7_289.boxKey 188160 (referenceBox7 (!canonicalBox7_289.bump)) = canonicalBox7_289 := by decide +kernel

theorem canonicalDecode7_289 : canonicalBox7_289.toKeyData 188160 = keys7Chunk9.get ⟨1, by decide⟩ := by
  change canonicalBox7_289.toKeyData 188160 = ⟨![(9 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (5 / 7), (9 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (673 / 336), (64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (751 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_289 : keySolid (keys7Chunk9.get ⟨1, by decide⟩) = canonicalPose7_289.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_289 (box := canonicalBox7_289) (k := keys7Chunk9.get ⟨1, by decide⟩) (canonicalMatch7_289) (canonicalDecode7_289)

def canonicalPose7_290 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, true, false, false, true, true, false], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_290 : BoxKey 7 :=
  ⟨![67200, 262080, 0, 107520, 275520, 53760, 127680], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 261632, 560, 108010, 274960, 53375, 128080], false⟩

theorem canonicalMatch7_290 :
    canonicalPose7_290.boxKey 188160 (referenceBox7 (!canonicalBox7_290.bump)) = canonicalBox7_290 := by decide +kernel

theorem canonicalDecode7_290 : canonicalBox7_290.toKeyData 188160 = keys7Chunk9.get ⟨2, by decide⟩ := by
  change canonicalBox7_290.toKeyData 188160 = ⟨![(5 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (2 / 7), (19 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (146 / 105), (1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376), (1601 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_290 : keySolid (keys7Chunk9.get ⟨2, by decide⟩) = canonicalPose7_290.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_290 (box := canonicalBox7_290) (k := keys7Chunk9.get ⟨2, by decide⟩) (canonicalMatch7_290) (canonicalDecode7_290)

def canonicalPose7_291 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, true, false, true, true, true, false], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_291 : BoxKey 7 :=
  ⟨![53760, 275520, 107520, 0, 262080, 67200, 127680], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 274960, 108010, -560, 261632, 66780, 128080], true⟩

theorem canonicalMatch7_291 :
    canonicalPose7_291.boxKey 188160 (referenceBox7 (!canonicalBox7_291.bump)) = canonicalBox7_291 := by decide +kernel

theorem canonicalDecode7_291 : canonicalBox7_291.toKeyData 188160 = keys7Chunk9.get ⟨3, by decide⟩ := by
  change canonicalBox7_291.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (5 / 14), (19 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (1543 / 2688), (-1 / 336), (146 / 105), (159 / 448), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_291 : keySolid (keys7Chunk9.get ⟨3, by decide⟩) = canonicalPose7_291.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_291 (box := canonicalBox7_291) (k := keys7Chunk9.get ⟨3, by decide⟩) (canonicalMatch7_291) (canonicalDecode7_291)

def canonicalPose7_292 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, false, false, true, false, true], ![0, 2, 0, 0, 2, 0, 1]⟩
def canonicalBox7_292 : BoxKey 7 :=
  ⟨![134400, 275520, 107520, 114240, 376320, 120960, 60480], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 274960, 108010, 114688, 375760, 121380, 60080], false⟩

theorem canonicalMatch7_292 :
    canonicalPose7_292.boxKey 188160 (referenceBox7 (!canonicalBox7_292.bump)) = canonicalBox7_292 := by decide +kernel

theorem canonicalDecode7_292 : canonicalBox7_292.toKeyData 188160 = keys7Chunk9.get ⟨4, by decide⟩ := by
  change canonicalBox7_292.toKeyData 188160 = ⟨![(5 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (9 / 14), (9 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (671 / 336), (289 / 448), (751 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_292 : keySolid (keys7Chunk9.get ⟨4, by decide⟩) = canonicalPose7_292.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_292 (box := canonicalBox7_292) (k := keys7Chunk9.get ⟨4, by decide⟩) (canonicalMatch7_292) (canonicalDecode7_292)

def canonicalPose7_293 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, true, true, false, false], ![0, 2, 1, 1, 2, 0, 0]⟩
def canonicalBox7_293 : BoxKey 7 :=
  ⟨![107520, 275520, 53760, 60480, 255360, 0, 114240], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 53375, 60080, 254940, 560, 114688], false⟩

theorem canonicalMatch7_293 :
    canonicalPose7_293.boxKey 188160 (referenceBox7 (!canonicalBox7_293.bump)) = canonicalBox7_293 := by decide +kernel

theorem canonicalDecode7_293 : canonicalBox7_293.toKeyData 188160 = keys7Chunk9.get ⟨5, by decide⟩ := by
  change canonicalBox7_293.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 0, (17 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (1 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_293 : keySolid (keys7Chunk9.get ⟨5, by decide⟩) = canonicalPose7_293.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_293 (box := canonicalBox7_293) (k := keys7Chunk9.get ⟨5, by decide⟩) (canonicalMatch7_293) (canonicalDecode7_293)

def canonicalPose7_294 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, false, true, true, false], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_294 : BoxKey 7 :=
  ⟨![73920, 268800, 100800, 134400, 248640, 67200, 0], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 268310, 101360, 134785, 248240, 66780, 560], false⟩

theorem canonicalMatch7_294 :
    canonicalPose7_294.boxKey 188160 (referenceBox7 (!canonicalBox7_294.bump)) = canonicalBox7_294 := by decide +kernel

theorem canonicalDecode7_294 : canonicalBox7_294.toKeyData 188160 = keys7Chunk9.get ⟨6, by decide⟩ := by
  change canonicalBox7_294.toKeyData 188160 = ⟨![(11 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (5 / 14), 0], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448), (1 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_294 : keySolid (keys7Chunk9.get ⟨6, by decide⟩) = canonicalPose7_294.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_294 (box := canonicalBox7_294) (k := keys7Chunk9.get ⟨6, by decide⟩) (canonicalMatch7_294) (canonicalDecode7_294)

def canonicalPose7_295 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, false, false, true, true, true], ![1, 2, 0, 0, 2, 1, 0]⟩
def canonicalBox7_295 : BoxKey 7 :=
  ⟨![67200, 248640, 134400, 100800, 268800, 73920, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 248240, 134785, 101360, 268310, 73472, -560], true⟩

theorem canonicalMatch7_295 :
    canonicalPose7_295.boxKey 188160 (referenceBox7 (!canonicalBox7_295.bump)) = canonicalBox7_295 := by decide +kernel

theorem canonicalDecode7_295 : canonicalBox7_295.toKeyData 188160 = keys7Chunk9.get ⟨7, by decide⟩ := by
  change canonicalBox7_295.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (11 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_295 : keySolid (keys7Chunk9.get ⟨7, by decide⟩) = canonicalPose7_295.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_295 (box := canonicalBox7_295) (k := keys7Chunk9.get ⟨7, by decide⟩) (canonicalMatch7_295) (canonicalDecode7_295)

def canonicalPose7_296 : Pose 7 :=
  ⟨canonicalPerm7_27, ![false, true, true, true, true, false, true], ![0, 2, 1, 1, 2, 0, 2]⟩
def canonicalBox7_296 : BoxKey 7 :=
  ⟨![0, 255360, 60480, 53760, 275520, 107520, 262080], ![0, 2520, 2800, 3080, 1680, 1960, 2240], ![560, 254940, 60080, 53375, 274960, 108010, 261632], false⟩

theorem canonicalMatch7_296 :
    canonicalPose7_296.boxKey 188160 (referenceBox7 (!canonicalBox7_296.bump)) = canonicalBox7_296 := by decide +kernel

theorem canonicalDecode7_296 : canonicalBox7_296.toKeyData 188160 = keys7Chunk9.get ⟨8, by decide⟩ := by
  change canonicalBox7_296.toKeyData 188160 = ⟨![0, (19 / 14), (9 / 28), (2 / 7), (41 / 28), (4 / 7), (39 / 28)], ![0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84)], ![(1 / 336), (607 / 448), (751 / 2352), (1525 / 5376), (491 / 336), (1543 / 2688), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_296 : keySolid (keys7Chunk9.get ⟨8, by decide⟩) = canonicalPose7_296.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_296 (box := canonicalBox7_296) (k := keys7Chunk9.get ⟨8, by decide⟩) (canonicalMatch7_296) (canonicalDecode7_296)

def canonicalPose7_297 : Pose 7 :=
  ⟨canonicalPerm7_15, ![false, true, false, false, true, false, false], ![0, 2, 0, 0, 2, 0, 1]⟩
def canonicalBox7_297 : BoxKey 7 :=
  ⟨![120960, 376320, 114240, 107520, 275520, 134400, 315840], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![121380, 375760, 114688, 108010, 274960, 134785, 316240], false⟩

theorem canonicalMatch7_297 :
    canonicalPose7_297.boxKey 188160 (referenceBox7 (!canonicalBox7_297.bump)) = canonicalBox7_297 := by decide +kernel

theorem canonicalDecode7_297 : canonicalBox7_297.toKeyData 188160 = keys7Chunk9.get ⟨9, by decide⟩ := by
  change canonicalBox7_297.toKeyData 188160 = ⟨![(9 / 14), 2, (17 / 28), (4 / 7), (41 / 28), (5 / 7), (47 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(289 / 448), (671 / 336), (64 / 105), (1543 / 2688), (491 / 336), (3851 / 5376), (3953 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_297 : keySolid (keys7Chunk9.get ⟨9, by decide⟩) = canonicalPose7_297.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_297 (box := canonicalBox7_297) (k := keys7Chunk9.get ⟨9, by decide⟩) (canonicalMatch7_297) (canonicalDecode7_297)

def canonicalPose7_298 : Pose 7 :=
  ⟨canonicalPerm7_12, ![true, true, true, false, true, true, true], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_298 : BoxKey 7 :=
  ⟨![67200, 262080, 0, 107520, 275520, 53760, 248640], ![2520, 2240, 0, 1960, 1680, 3080, 2800], ![66780, 261632, -560, 108010, 274960, 53375, 248240], true⟩

theorem canonicalMatch7_298 :
    canonicalPose7_298.boxKey 188160 (referenceBox7 (!canonicalBox7_298.bump)) = canonicalBox7_298 := by decide +kernel

theorem canonicalDecode7_298 : canonicalBox7_298.toKeyData 188160 = keys7Chunk9.get ⟨10, by decide⟩ := by
  change canonicalBox7_298.toKeyData 188160 = ⟨![(5 / 14), (39 / 28), 0, (4 / 7), (41 / 28), (2 / 7), (37 / 28)], ![(3 / 224), (1 / 84), 0, (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (146 / 105), (-1 / 336), (1543 / 2688), (491 / 336), (1525 / 5376), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_298 : keySolid (keys7Chunk9.get ⟨10, by decide⟩) = canonicalPose7_298.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_298 (box := canonicalBox7_298) (k := keys7Chunk9.get ⟨10, by decide⟩) (canonicalMatch7_298) (canonicalDecode7_298)

def canonicalPose7_299 : Pose 7 :=
  ⟨canonicalPerm7_21, ![true, true, false, false, true, true, true], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_299 : BoxKey 7 :=
  ⟨![53760, 275520, 107520, 0, 262080, 67200, 248640], ![3080, 1680, 1960, 0, 2240, 2520, 2800], ![53375, 274960, 108010, 560, 261632, 66780, 248240], false⟩

theorem canonicalMatch7_299 :
    canonicalPose7_299.boxKey 188160 (referenceBox7 (!canonicalBox7_299.bump)) = canonicalBox7_299 := by decide +kernel

theorem canonicalDecode7_299 : canonicalBox7_299.toKeyData 188160 = keys7Chunk9.get ⟨11, by decide⟩ := by
  change canonicalBox7_299.toKeyData 188160 = ⟨![(2 / 7), (41 / 28), (4 / 7), 0, (39 / 28), (5 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), 0, (1 / 84), (3 / 224), (5 / 336)], ![(1525 / 5376), (491 / 336), (1543 / 2688), (1 / 336), (146 / 105), (159 / 448), (3103 / 2352)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_299 : keySolid (keys7Chunk9.get ⟨11, by decide⟩) = canonicalPose7_299.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_299 (box := canonicalBox7_299) (k := keys7Chunk9.get ⟨11, by decide⟩) (canonicalMatch7_299) (canonicalDecode7_299)

def canonicalPose7_300 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, false, false, false, false, false], ![0, 2, 0, 0, 2, 0, 1]⟩
def canonicalBox7_300 : BoxKey 7 :=
  ⟨![134400, 275520, 107520, 114240, 376320, 120960, 315840], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 274960, 108010, 114688, 376880, 121380, 316240], true⟩

theorem canonicalMatch7_300 :
    canonicalPose7_300.boxKey 188160 (referenceBox7 (!canonicalBox7_300.bump)) = canonicalBox7_300 := by decide +kernel

theorem canonicalDecode7_300 : canonicalBox7_300.toKeyData 188160 = keys7Chunk9.get ⟨12, by decide⟩ := by
  change canonicalBox7_300.toKeyData 188160 = ⟨![(5 / 7), (41 / 28), (4 / 7), (17 / 28), 2, (9 / 14), (47 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (491 / 336), (1543 / 2688), (64 / 105), (673 / 336), (289 / 448), (3953 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_300 : keySolid (keys7Chunk9.get ⟨12, by decide⟩) = canonicalPose7_300.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_300 (box := canonicalBox7_300) (k := keys7Chunk9.get ⟨12, by decide⟩) (canonicalMatch7_300) (canonicalDecode7_300)

def canonicalPose7_301 : Pose 7 :=
  ⟨canonicalPerm7_5, ![false, true, true, true, true, true, true], ![0, 2, 1, 1, 2, 0, 2]⟩
def canonicalBox7_301 : BoxKey 7 :=
  ⟨![107520, 275520, 53760, 60480, 255360, 0, 262080], ![1960, 1680, 3080, 2800, 2520, 0, 2240], ![108010, 274960, 53375, 60080, 254940, -560, 261632], true⟩

theorem canonicalMatch7_301 :
    canonicalPose7_301.boxKey 188160 (referenceBox7 (!canonicalBox7_301.bump)) = canonicalBox7_301 := by decide +kernel

theorem canonicalDecode7_301 : canonicalBox7_301.toKeyData 188160 = keys7Chunk9.get ⟨13, by decide⟩ := by
  change canonicalBox7_301.toKeyData 188160 = ⟨![(4 / 7), (41 / 28), (2 / 7), (9 / 28), (19 / 14), 0, (39 / 28)], ![(1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84)], ![(1543 / 2688), (491 / 336), (1525 / 5376), (751 / 2352), (607 / 448), (-1 / 336), (146 / 105)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_301 : keySolid (keys7Chunk9.get ⟨13, by decide⟩) = canonicalPose7_301.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_301 (box := canonicalBox7_301) (k := keys7Chunk9.get ⟨13, by decide⟩) (canonicalMatch7_301) (canonicalDecode7_301)

def canonicalPose7_302 : Pose 7 :=
  ⟨canonicalPerm7_8, ![true, true, false, false, true, true, false], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_302 : BoxKey 7 :=
  ⟨![73920, 268800, 100800, 134400, 248640, 67200, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![73472, 268310, 101360, 134785, 248240, 66780, 376880], true⟩

theorem canonicalMatch7_302 :
    canonicalPose7_302.boxKey 188160 (referenceBox7 (!canonicalBox7_302.bump)) = canonicalBox7_302 := by decide +kernel

theorem canonicalDecode7_302 : canonicalBox7_302.toKeyData 188160 = keys7Chunk9.get ⟨14, by decide⟩ := by
  change canonicalBox7_302.toKeyData 188160 = ⟨![(11 / 28), (10 / 7), (15 / 28), (5 / 7), (37 / 28), (5 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(41 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3103 / 2352), (159 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_302 : keySolid (keys7Chunk9.get ⟨14, by decide⟩) = canonicalPose7_302.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_302 (box := canonicalBox7_302) (k := keys7Chunk9.get ⟨14, by decide⟩) (canonicalMatch7_302) (canonicalDecode7_302)

def canonicalPose7_303 : Pose 7 :=
  ⟨canonicalPerm7_13, ![true, true, false, false, true, true, true], ![1, 2, 0, 0, 2, 1, 2]⟩
def canonicalBox7_303 : BoxKey 7 :=
  ⟨![67200, 248640, 134400, 100800, 268800, 73920, 376320], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![66780, 248240, 134785, 101360, 268310, 73472, 375760], false⟩

theorem canonicalMatch7_303 :
    canonicalPose7_303.boxKey 188160 (referenceBox7 (!canonicalBox7_303.bump)) = canonicalBox7_303 := by decide +kernel

theorem canonicalDecode7_303 : canonicalBox7_303.toKeyData 188160 = keys7Chunk9.get ⟨15, by decide⟩ := by
  change canonicalBox7_303.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (5 / 7), (15 / 28), (10 / 7), (11 / 28), 2], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(159 / 448), (3103 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (41 / 105), (671 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_303 : keySolid (keys7Chunk9.get ⟨15, by decide⟩) = canonicalPose7_303.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_303 (box := canonicalBox7_303) (k := keys7Chunk9.get ⟨15, by decide⟩) (canonicalMatch7_303) (canonicalDecode7_303)

def canonicalPose7_304 : Pose 7 :=
  ⟨canonicalPerm7_25, ![true, true, false, false, false, false, false], ![0, 2, 0, 0, 1, 1, 0]⟩
def canonicalBox7_304 : BoxKey 7 :=
  ⟨![0, 262080, 107520, 100800, 322560, 315840, 120960], ![0, 2240, 1960, 1680, 3080, 2800, 2520], ![-560, 261632, 108010, 101360, 322945, 316240, 121380], true⟩

theorem canonicalMatch7_304 :
    canonicalPose7_304.boxKey 188160 (referenceBox7 (!canonicalBox7_304.bump)) = canonicalBox7_304 := by decide +kernel

theorem canonicalDecode7_304 : canonicalBox7_304.toKeyData 188160 = keys7Chunk9.get ⟨16, by decide⟩ := by
  change canonicalBox7_304.toKeyData 188160 = ⟨![0, (39 / 28), (4 / 7), (15 / 28), (12 / 7), (47 / 28), (9 / 14)], ![0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224)], ![(-1 / 336), (146 / 105), (1543 / 2688), (181 / 336), (9227 / 5376), (3953 / 2352), (289 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_304 : keySolid (keys7Chunk9.get ⟨16, by decide⟩) = canonicalPose7_304.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_304 (box := canonicalBox7_304) (k := keys7Chunk9.get ⟨16, by decide⟩) (canonicalMatch7_304) (canonicalDecode7_304)

def canonicalPose7_305 : Pose 7 :=
  ⟨canonicalPerm7_11, ![true, true, true, false, true, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_305 : BoxKey 7 :=
  ⟨![73920, 376320, 67200, 127680, 241920, 275520, 107520], ![2240, 0, 2520, 2800, 3080, 1680, 1960], ![73472, 375760, 66780, 128080, 241535, 274960, 108010], false⟩

theorem canonicalMatch7_305 :
    canonicalPose7_305.boxKey 188160 (referenceBox7 (!canonicalBox7_305.bump)) = canonicalBox7_305 := by decide +kernel

theorem canonicalDecode7_305 : canonicalBox7_305.toKeyData 188160 = keys7Chunk9.get ⟨17, by decide⟩ := by
  change canonicalBox7_305.toKeyData 188160 = ⟨![(11 / 28), 2, (5 / 14), (19 / 28), (9 / 7), (41 / 28), (4 / 7)], ![(1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96)], ![(41 / 105), (671 / 336), (159 / 448), (1601 / 2352), (6901 / 5376), (491 / 336), (1543 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_305 : keySolid (keys7Chunk9.get ⟨17, by decide⟩) = canonicalPose7_305.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_305 (box := canonicalBox7_305) (k := keys7Chunk9.get ⟨17, by decide⟩) (canonicalMatch7_305) (canonicalDecode7_305)

def canonicalPose7_306 : Pose 7 :=
  ⟨canonicalPerm7_15, ![true, false, true, false, true, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_306 : BoxKey 7 :=
  ⟨![67200, 376320, 73920, 107520, 275520, 241920, 127680], ![2520, 0, 2240, 1960, 1680, 3080, 2800], ![66780, 376880, 73472, 108010, 274960, 241535, 128080], true⟩

theorem canonicalMatch7_306 :
    canonicalPose7_306.boxKey 188160 (referenceBox7 (!canonicalBox7_306.bump)) = canonicalBox7_306 := by decide +kernel

theorem canonicalDecode7_306 : canonicalBox7_306.toKeyData 188160 = keys7Chunk9.get ⟨18, by decide⟩ := by
  change canonicalBox7_306.toKeyData 188160 = ⟨![(5 / 14), 2, (11 / 28), (4 / 7), (41 / 28), (9 / 7), (19 / 28)], ![(3 / 224), 0, (1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336)], ![(159 / 448), (673 / 336), (41 / 105), (1543 / 2688), (491 / 336), (6901 / 5376), (1601 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_306 : keySolid (keys7Chunk9.get ⟨18, by decide⟩) = canonicalPose7_306.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_306 (box := canonicalBox7_306) (k := keys7Chunk9.get ⟨18, by decide⟩) (canonicalMatch7_306) (canonicalDecode7_306)

def canonicalPose7_307 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, false, false, false, false], ![0, 2, 0, 0, 1, 1, 0]⟩
def canonicalBox7_307 : BoxKey 7 :=
  ⟨![107520, 262080, 0, 120960, 315840, 322560, 100800], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 261632, 560, 121380, 316240, 322945, 101360], false⟩

theorem canonicalMatch7_307 :
    canonicalPose7_307.boxKey 188160 (referenceBox7 (!canonicalBox7_307.bump)) = canonicalBox7_307 := by decide +kernel

theorem canonicalDecode7_307 : canonicalBox7_307.toKeyData 188160 = keys7Chunk9.get ⟨19, by decide⟩ := by
  change canonicalBox7_307.toKeyData 188160 = ⟨![(4 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (12 / 7), (15 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (3953 / 2352), (9227 / 5376), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_307 : keySolid (keys7Chunk9.get ⟨19, by decide⟩) = canonicalPose7_307.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_307 (box := canonicalBox7_307) (k := keys7Chunk9.get ⟨19, by decide⟩) (canonicalMatch7_307) (canonicalDecode7_307)

def canonicalPose7_308 : Pose 7 :=
  ⟨canonicalPerm7_23, ![false, false, false, false, true, true, false], ![0, 1, 0, 0, 2, 2, 0]⟩
def canonicalBox7_308 : BoxKey 7 :=
  ⟨![134400, 315840, 120960, 0, 262080, 268800, 100800], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![134785, 316240, 121380, 560, 261632, 268310, 101360], false⟩

theorem canonicalMatch7_308 :
    canonicalPose7_308.boxKey 188160 (referenceBox7 (!canonicalBox7_308.bump)) = canonicalBox7_308 := by decide +kernel

theorem canonicalDecode7_308 : canonicalBox7_308.toKeyData 188160 = keys7Chunk9.get ⟨20, by decide⟩ := by
  change canonicalBox7_308.toKeyData 188160 = ⟨![(5 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(3851 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (146 / 105), (3833 / 2688), (181 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_308 : keySolid (keys7Chunk9.get ⟨20, by decide⟩) = canonicalPose7_308.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_308 (box := canonicalBox7_308) (k := keys7Chunk9.get ⟨20, by decide⟩) (canonicalMatch7_308) (canonicalDecode7_308)

def canonicalPose7_309 : Pose 7 :=
  ⟨canonicalPerm7_22, ![true, true, true, false, false, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_309 : BoxKey 7 :=
  ⟨![53760, 248640, 67200, 114240, 376320, 268800, 100800], ![3080, 2800, 2520, 2240, 0, 1960, 1680], ![53375, 248240, 66780, 114688, 376880, 268310, 101360], true⟩

theorem canonicalMatch7_309 :
    canonicalPose7_309.boxKey 188160 (referenceBox7 (!canonicalBox7_309.bump)) = canonicalBox7_309 := by decide +kernel

theorem canonicalDecode7_309 : canonicalBox7_309.toKeyData 188160 = keys7Chunk9.get ⟨21, by decide⟩ := by
  change canonicalBox7_309.toKeyData 188160 = ⟨![(2 / 7), (37 / 28), (5 / 14), (17 / 28), 2, (10 / 7), (15 / 28)], ![(11 / 672), (5 / 336), (3 / 224), (1 / 84), 0, (1 / 96), (1 / 112)], ![(1525 / 5376), (3103 / 2352), (159 / 448), (64 / 105), (673 / 336), (3833 / 2688), (181 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_309 : keySolid (keys7Chunk9.get ⟨21, by decide⟩) = canonicalPose7_309.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_309 (box := canonicalBox7_309) (k := keys7Chunk9.get ⟨21, by decide⟩) (canonicalMatch7_309) (canonicalDecode7_309)

def canonicalPose7_310 : Pose 7 :=
  ⟨canonicalPerm7_14, ![true, true, true, false, true, true, false], ![1, 2, 1, 0, 2, 2, 0]⟩
def canonicalBox7_310 : BoxKey 7 :=
  ⟨![67200, 248640, 53760, 100800, 268800, 376320, 114240], ![2520, 2800, 3080, 1680, 1960, 0, 2240], ![66780, 248240, 53375, 101360, 268310, 375760, 114688], false⟩

theorem canonicalMatch7_310 :
    canonicalPose7_310.boxKey 188160 (referenceBox7 (!canonicalBox7_310.bump)) = canonicalBox7_310 := by decide +kernel

theorem canonicalDecode7_310 : canonicalBox7_310.toKeyData 188160 = keys7Chunk9.get ⟨22, by decide⟩ := by
  change canonicalBox7_310.toKeyData 188160 = ⟨![(5 / 14), (37 / 28), (2 / 7), (15 / 28), (10 / 7), 2, (17 / 28)], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), 0, (1 / 84)], ![(159 / 448), (3103 / 2352), (1525 / 5376), (181 / 336), (3833 / 2688), (671 / 336), (64 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_310 : keySolid (keys7Chunk9.get ⟨22, by decide⟩) = canonicalPose7_310.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_310 (box := canonicalBox7_310) (k := keys7Chunk9.get ⟨22, by decide⟩) (canonicalMatch7_310) (canonicalDecode7_310)

def canonicalPose7_311 : Pose 7 :=
  ⟨canonicalPerm7_13, ![false, false, false, false, true, true, true], ![0, 1, 0, 0, 2, 2, 0]⟩
def canonicalBox7_311 : BoxKey 7 :=
  ⟨![120960, 315840, 134400, 100800, 268800, 262080, 0], ![2520, 2800, 3080, 1680, 1960, 2240, 0], ![121380, 316240, 134785, 101360, 268310, 261632, -560], true⟩

theorem canonicalMatch7_311 :
    canonicalPose7_311.boxKey 188160 (referenceBox7 (!canonicalBox7_311.bump)) = canonicalBox7_311 := by decide +kernel

theorem canonicalDecode7_311 : canonicalBox7_311.toKeyData 188160 = keys7Chunk9.get ⟨23, by decide⟩ := by
  change canonicalBox7_311.toKeyData 188160 = ⟨![(9 / 14), (47 / 28), (5 / 7), (15 / 28), (10 / 7), (39 / 28), 0], ![(3 / 224), (5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0], ![(289 / 448), (3953 / 2352), (3851 / 5376), (181 / 336), (3833 / 2688), (146 / 105), (-1 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_311 : keySolid (keys7Chunk9.get ⟨23, by decide⟩) = canonicalPose7_311.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_311 (box := canonicalBox7_311) (k := keys7Chunk9.get ⟨23, by decide⟩) (canonicalMatch7_311) (canonicalDecode7_311)

def canonicalPose7_312 : Pose 7 :=
  ⟨canonicalPerm7_24, ![false, true, false, true, true, false, true], ![0, 2, 0, 1, 2, 1, 2]⟩
def canonicalBox7_312 : BoxKey 7 :=
  ⟨![0, 268800, 100800, 53760, 248640, 309120, 262080], ![0, 1960, 1680, 3080, 2800, 2520, 2240], ![560, 268310, 101360, 53375, 248240, 309540, 261632], false⟩

theorem canonicalMatch7_312 :
    canonicalPose7_312.boxKey 188160 (referenceBox7 (!canonicalBox7_312.bump)) = canonicalBox7_312 := by decide +kernel

theorem canonicalDecode7_312 : canonicalBox7_312.toKeyData 188160 = keys7Chunk9.get ⟨24, by decide⟩ := by
  change canonicalBox7_312.toKeyData 188160 = ⟨![0, (10 / 7), (15 / 28), (2 / 7), (37 / 28), (23 / 14), (39 / 28)], ![0, (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), (1 / 84)], ![(1 / 336), (3833 / 2688), (181 / 336), (1525 / 5376), (3103 / 2352), (737 / 448), (146 / 105)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_312 : keySolid (keys7Chunk9.get ⟨24, by decide⟩) = canonicalPose7_312.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_312 (box := canonicalBox7_312) (k := keys7Chunk9.get ⟨24, by decide⟩) (canonicalMatch7_312) (canonicalDecode7_312)

def canonicalPose7_313 : Pose 7 :=
  ⟨canonicalPerm7_7, ![false, false, false, true, true, false, true], ![0, 2, 0, 1, 2, 1, 2]⟩
def canonicalBox7_313 : BoxKey 7 :=
  ⟨![107520, 376320, 114240, 67200, 248640, 322560, 275520], ![1960, 0, 2240, 2520, 2800, 3080, 1680], ![108010, 376880, 114688, 66780, 248240, 322945, 274960], true⟩

theorem canonicalMatch7_313 :
    canonicalPose7_313.boxKey 188160 (referenceBox7 (!canonicalBox7_313.bump)) = canonicalBox7_313 := by decide +kernel

theorem canonicalDecode7_313 : canonicalBox7_313.toKeyData 188160 = keys7Chunk9.get ⟨25, by decide⟩ := by
  change canonicalBox7_313.toKeyData 188160 = ⟨![(4 / 7), 2, (17 / 28), (5 / 14), (37 / 28), (12 / 7), (41 / 28)], ![(1 / 96), 0, (1 / 84), (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (673 / 336), (64 / 105), (159 / 448), (3103 / 2352), (9227 / 5376), (491 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_313 : keySolid (keys7Chunk9.get ⟨25, by decide⟩) = canonicalPose7_313.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_313 (box := canonicalBox7_313) (k := keys7Chunk9.get ⟨25, by decide⟩) (canonicalMatch7_313) (canonicalDecode7_313)

def canonicalPose7_314 : Pose 7 :=
  ⟨canonicalPerm7_6, ![false, true, false, false, false, true, true], ![0, 2, 0, 0, 1, 2, 2]⟩
def canonicalBox7_314 : BoxKey 7 :=
  ⟨![107520, 262080, 0, 120960, 315840, 241920, 275520], ![1960, 2240, 0, 2520, 2800, 3080, 1680], ![108010, 261632, 560, 121380, 316240, 241535, 274960], false⟩

theorem canonicalMatch7_314 :
    canonicalPose7_314.boxKey 188160 (referenceBox7 (!canonicalBox7_314.bump)) = canonicalBox7_314 := by decide +kernel

theorem canonicalDecode7_314 : canonicalBox7_314.toKeyData 188160 = keys7Chunk9.get ⟨26, by decide⟩ := by
  change canonicalBox7_314.toKeyData 188160 = ⟨![(4 / 7), (39 / 28), 0, (9 / 14), (47 / 28), (9 / 7), (41 / 28)], ![(1 / 96), (1 / 84), 0, (3 / 224), (5 / 336), (11 / 672), (1 / 112)], ![(1543 / 2688), (146 / 105), (1 / 336), (289 / 448), (3953 / 2352), (6901 / 5376), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_314 : keySolid (keys7Chunk9.get ⟨26, by decide⟩) = canonicalPose7_314.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_314 (box := canonicalBox7_314) (k := keys7Chunk9.get ⟨26, by decide⟩) (canonicalMatch7_314) (canonicalDecode7_314)

def canonicalPose7_315 : Pose 7 :=
  ⟨canonicalPerm7_23, ![true, false, false, false, true, true, true], ![1, 1, 0, 0, 2, 2, 2]⟩
def canonicalBox7_315 : BoxKey 7 :=
  ⟨![53760, 315840, 120960, 0, 262080, 268800, 275520], ![3080, 2800, 2520, 0, 2240, 1960, 1680], ![53375, 316240, 121380, 560, 261632, 268310, 274960], false⟩

theorem canonicalMatch7_315 :
    canonicalPose7_315.boxKey 188160 (referenceBox7 (!canonicalBox7_315.bump)) = canonicalBox7_315 := by decide +kernel

theorem canonicalDecode7_315 : canonicalBox7_315.toKeyData 188160 = keys7Chunk9.get ⟨27, by decide⟩ := by
  change canonicalBox7_315.toKeyData 188160 = ⟨![(2 / 7), (47 / 28), (9 / 14), 0, (39 / 28), (10 / 7), (41 / 28)], ![(11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96), (1 / 112)], ![(1525 / 5376), (3953 / 2352), (289 / 448), (1 / 336), (146 / 105), (3833 / 2688), (491 / 336)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_315 : keySolid (keys7Chunk9.get ⟨27, by decide⟩) = canonicalPose7_315.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_315 (box := canonicalBox7_315) (k := keys7Chunk9.get ⟨27, by decide⟩) (canonicalMatch7_315) (canonicalDecode7_315)

def canonicalPose7_316 : Pose 7 :=
  ⟨canonicalPerm7_3, ![false, true, false, true, true, false, true], ![0, 2, 0, 1, 2, 1, 2]⟩
def canonicalBox7_316 : BoxKey 7 :=
  ⟨![100800, 241920, 127680, 67200, 376320, 302400, 268800], ![1680, 3080, 2800, 2520, 0, 2240, 1960], ![101360, 241535, 128080, 66780, 375760, 302848, 268310], false⟩

theorem canonicalMatch7_316 :
    canonicalPose7_316.boxKey 188160 (referenceBox7 (!canonicalBox7_316.bump)) = canonicalBox7_316 := by decide +kernel

theorem canonicalDecode7_316 : canonicalBox7_316.toKeyData 188160 = keys7Chunk9.get ⟨28, by decide⟩ := by
  change canonicalBox7_316.toKeyData 188160 = ⟨![(15 / 28), (9 / 7), (19 / 28), (5 / 14), 2, (45 / 28), (10 / 7)], ![(1 / 112), (11 / 672), (5 / 336), (3 / 224), 0, (1 / 84), (1 / 96)], ![(181 / 336), (6901 / 5376), (1601 / 2352), (159 / 448), (671 / 336), (169 / 105), (3833 / 2688)], false⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_316 : keySolid (keys7Chunk9.get ⟨28, by decide⟩) = canonicalPose7_316.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_316 (box := canonicalBox7_316) (k := keys7Chunk9.get ⟨28, by decide⟩) (canonicalMatch7_316) (canonicalDecode7_316)

def canonicalPose7_317 : Pose 7 :=
  ⟨canonicalPerm7_20, ![false, true, false, true, false, false, true], ![0, 2, 0, 1, 2, 1, 2]⟩
def canonicalBox7_317 : BoxKey 7 :=
  ⟨![134400, 275520, 107520, 73920, 376320, 309120, 248640], ![3080, 1680, 1960, 2240, 0, 2520, 2800], ![134785, 274960, 108010, 73472, 376880, 309540, 248240], true⟩

theorem canonicalMatch7_317 :
    canonicalPose7_317.boxKey 188160 (referenceBox7 (!canonicalBox7_317.bump)) = canonicalBox7_317 := by decide +kernel

theorem canonicalDecode7_317 : canonicalBox7_317.toKeyData 188160 = keys7Chunk9.get ⟨29, by decide⟩ := by
  change canonicalBox7_317.toKeyData 188160 = ⟨![(5 / 7), (41 / 28), (4 / 7), (11 / 28), 2, (23 / 14), (37 / 28)], ![(11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224), (5 / 336)], ![(3851 / 5376), (491 / 336), (1543 / 2688), (41 / 105), (673 / 336), (737 / 448), (3103 / 2352)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_317 : keySolid (keys7Chunk9.get ⟨29, by decide⟩) = canonicalPose7_317.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_317 (box := canonicalBox7_317) (k := keys7Chunk9.get ⟨29, by decide⟩) (canonicalMatch7_317) (canonicalDecode7_317)

def canonicalPose7_318 : Pose 7 :=
  ⟨canonicalPerm7_18, ![true, false, false, false, true, false, true], ![1, 1, 0, 0, 2, 2, 2]⟩
def canonicalBox7_318 : BoxKey 7 :=
  ⟨![60480, 322560, 100800, 107520, 262080, 376320, 255360], ![2800, 3080, 1680, 1960, 2240, 0, 2520], ![60080, 322945, 101360, 108010, 261632, 376880, 254940], true⟩

theorem canonicalMatch7_318 :
    canonicalPose7_318.boxKey 188160 (referenceBox7 (!canonicalBox7_318.bump)) = canonicalBox7_318 := by decide +kernel

theorem canonicalDecode7_318 : canonicalBox7_318.toKeyData 188160 = keys7Chunk9.get ⟨30, by decide⟩ := by
  change canonicalBox7_318.toKeyData 188160 = ⟨![(9 / 28), (12 / 7), (15 / 28), (4 / 7), (39 / 28), 2, (19 / 14)], ![(5 / 336), (11 / 672), (1 / 112), (1 / 96), (1 / 84), 0, (3 / 224)], ![(751 / 2352), (9227 / 5376), (181 / 336), (1543 / 2688), (146 / 105), (673 / 336), (607 / 448)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_318 : keySolid (keys7Chunk9.get ⟨30, by decide⟩) = canonicalPose7_318.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_318 (box := canonicalBox7_318) (k := keys7Chunk9.get ⟨30, by decide⟩) (canonicalMatch7_318) (canonicalDecode7_318)

def canonicalPose7_319 : Pose 7 :=
  ⟨canonicalPerm7_8, ![false, true, false, false, false, true, false], ![0, 2, 0, 0, 1, 2, 2]⟩
def canonicalBox7_319 : BoxKey 7 :=
  ⟨![114240, 268800, 100800, 134400, 315840, 255360, 376320], ![2240, 1960, 1680, 3080, 2800, 2520, 0], ![114688, 268310, 101360, 134785, 316240, 254940, 376880], true⟩

theorem canonicalMatch7_319 :
    canonicalPose7_319.boxKey 188160 (referenceBox7 (!canonicalBox7_319.bump)) = canonicalBox7_319 := by decide +kernel

theorem canonicalDecode7_319 : canonicalBox7_319.toKeyData 188160 = keys7Chunk9.get ⟨31, by decide⟩ := by
  change canonicalBox7_319.toKeyData 188160 = ⟨![(17 / 28), (10 / 7), (15 / 28), (5 / 7), (47 / 28), (19 / 14), 2], ![(1 / 84), (1 / 96), (1 / 112), (11 / 672), (5 / 336), (3 / 224), 0], ![(64 / 105), (3833 / 2688), (181 / 336), (3851 / 5376), (3953 / 2352), (607 / 448), (673 / 336)], true⟩
  apply keyData_ext_of_coordinates <;> decide +kernel

theorem canonicalSolid7_319 : keySolid (keys7Chunk9.get ⟨31, by decide⟩) = canonicalPose7_319.euclidean '' referenceSolid7 :=
  canonical7_of_box_match canonicalPose7_319 (box := canonicalBox7_319) (k := keys7Chunk9.get ⟨31, by decide⟩) (canonicalMatch7_319) (canonicalDecode7_319)

theorem keys7Chunk9_canonical : ∀ k ∈ keys7Chunk9,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  intro k hk
  simp only [keys7Chunk9, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨canonicalPose7_288, canonicalSolid7_288⟩
  · exact ⟨canonicalPose7_289, canonicalSolid7_289⟩
  · exact ⟨canonicalPose7_290, canonicalSolid7_290⟩
  · exact ⟨canonicalPose7_291, canonicalSolid7_291⟩
  · exact ⟨canonicalPose7_292, canonicalSolid7_292⟩
  · exact ⟨canonicalPose7_293, canonicalSolid7_293⟩
  · exact ⟨canonicalPose7_294, canonicalSolid7_294⟩
  · exact ⟨canonicalPose7_295, canonicalSolid7_295⟩
  · exact ⟨canonicalPose7_296, canonicalSolid7_296⟩
  · exact ⟨canonicalPose7_297, canonicalSolid7_297⟩
  · exact ⟨canonicalPose7_298, canonicalSolid7_298⟩
  · exact ⟨canonicalPose7_299, canonicalSolid7_299⟩
  · exact ⟨canonicalPose7_300, canonicalSolid7_300⟩
  · exact ⟨canonicalPose7_301, canonicalSolid7_301⟩
  · exact ⟨canonicalPose7_302, canonicalSolid7_302⟩
  · exact ⟨canonicalPose7_303, canonicalSolid7_303⟩
  · exact ⟨canonicalPose7_304, canonicalSolid7_304⟩
  · exact ⟨canonicalPose7_305, canonicalSolid7_305⟩
  · exact ⟨canonicalPose7_306, canonicalSolid7_306⟩
  · exact ⟨canonicalPose7_307, canonicalSolid7_307⟩
  · exact ⟨canonicalPose7_308, canonicalSolid7_308⟩
  · exact ⟨canonicalPose7_309, canonicalSolid7_309⟩
  · exact ⟨canonicalPose7_310, canonicalSolid7_310⟩
  · exact ⟨canonicalPose7_311, canonicalSolid7_311⟩
  · exact ⟨canonicalPose7_312, canonicalSolid7_312⟩
  · exact ⟨canonicalPose7_313, canonicalSolid7_313⟩
  · exact ⟨canonicalPose7_314, canonicalSolid7_314⟩
  · exact ⟨canonicalPose7_315, canonicalSolid7_315⟩
  · exact ⟨canonicalPose7_316, canonicalSolid7_316⟩
  · exact ⟨canonicalPose7_317, canonicalSolid7_317⟩
  · exact ⟨canonicalPose7_318, canonicalSolid7_318⟩
  · exact ⟨canonicalPose7_319, canonicalSolid7_319⟩

#print axioms keys7Chunk9_canonical

end SparseMonotiles.Canonical
