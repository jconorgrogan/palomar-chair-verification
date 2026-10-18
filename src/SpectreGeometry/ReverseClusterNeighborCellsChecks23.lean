module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration23RootChunk0 : List Cell := (rootCells configuration23).drop 0 |>.take 8
theorem configuration23RootChunk0_checked : configuration23RootChunk0.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk1 : List Cell := (rootCells configuration23).drop 8 |>.take 8
theorem configuration23RootChunk1_checked : configuration23RootChunk1.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk2 : List Cell := (rootCells configuration23).drop 16 |>.take 8
theorem configuration23RootChunk2_checked : configuration23RootChunk2.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk3 : List Cell := (rootCells configuration23).drop 24 |>.take 8
theorem configuration23RootChunk3_checked : configuration23RootChunk3.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk4 : List Cell := (rootCells configuration23).drop 32 |>.take 8
theorem configuration23RootChunk4_checked : configuration23RootChunk4.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk5 : List Cell := (rootCells configuration23).drop 40 |>.take 8
theorem configuration23RootChunk5_checked : configuration23RootChunk5.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk6 : List Cell := (rootCells configuration23).drop 48 |>.take 8
theorem configuration23RootChunk6_checked : configuration23RootChunk6.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk7 : List Cell := (rootCells configuration23).drop 56 |>.take 8
theorem configuration23RootChunk7_checked : configuration23RootChunk7.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk8 : List Cell := (rootCells configuration23).drop 64 |>.take 8
theorem configuration23RootChunk8_checked : configuration23RootChunk8.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

def configuration23RootChunk9 : List Cell := (rootCells configuration23).drop 72 |>.take 8
theorem configuration23RootChunk9_checked : configuration23RootChunk9.all (fun a =>
    (neighborCells configuration23).all (cellPairFastB configuration23.sharedPath a)) = true := by decide

theorem placement23_checked : configurationCheckedB configuration23 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration23.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration23 = configuration23RootChunk0 ++ configuration23RootChunk1 ++ configuration23RootChunk2 ++ configuration23RootChunk3 ++ configuration23RootChunk4 ++ configuration23RootChunk5 ++ configuration23RootChunk6 ++ configuration23RootChunk7 ++ configuration23RootChunk8 ++ configuration23RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration23RootChunk0_checked,configuration23RootChunk1_checked,configuration23RootChunk2_checked,configuration23RootChunk3_checked,configuration23RootChunk4_checked,configuration23RootChunk5_checked,configuration23RootChunk6_checked,configuration23RootChunk7_checked,configuration23RootChunk8_checked,configuration23RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
