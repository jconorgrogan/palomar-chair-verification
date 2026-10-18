module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration13RootChunk0 : List Cell := (rootCells configuration13).drop 0 |>.take 8
theorem configuration13RootChunk0_checked : configuration13RootChunk0.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk1 : List Cell := (rootCells configuration13).drop 8 |>.take 8
theorem configuration13RootChunk1_checked : configuration13RootChunk1.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk2 : List Cell := (rootCells configuration13).drop 16 |>.take 8
theorem configuration13RootChunk2_checked : configuration13RootChunk2.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk3 : List Cell := (rootCells configuration13).drop 24 |>.take 8
theorem configuration13RootChunk3_checked : configuration13RootChunk3.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk4 : List Cell := (rootCells configuration13).drop 32 |>.take 8
theorem configuration13RootChunk4_checked : configuration13RootChunk4.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk5 : List Cell := (rootCells configuration13).drop 40 |>.take 8
theorem configuration13RootChunk5_checked : configuration13RootChunk5.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk6 : List Cell := (rootCells configuration13).drop 48 |>.take 8
theorem configuration13RootChunk6_checked : configuration13RootChunk6.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk7 : List Cell := (rootCells configuration13).drop 56 |>.take 8
theorem configuration13RootChunk7_checked : configuration13RootChunk7.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk8 : List Cell := (rootCells configuration13).drop 64 |>.take 8
theorem configuration13RootChunk8_checked : configuration13RootChunk8.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

def configuration13RootChunk9 : List Cell := (rootCells configuration13).drop 72 |>.take 8
theorem configuration13RootChunk9_checked : configuration13RootChunk9.all (fun a =>
    (neighborCells configuration13).all (cellPairFastB configuration13.sharedPath a)) = true := by decide

theorem placement13_checked : configurationCheckedB configuration13 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration13.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration13 = configuration13RootChunk0 ++ configuration13RootChunk1 ++ configuration13RootChunk2 ++ configuration13RootChunk3 ++ configuration13RootChunk4 ++ configuration13RootChunk5 ++ configuration13RootChunk6 ++ configuration13RootChunk7 ++ configuration13RootChunk8 ++ configuration13RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration13RootChunk0_checked,configuration13RootChunk1_checked,configuration13RootChunk2_checked,configuration13RootChunk3_checked,configuration13RootChunk4_checked,configuration13RootChunk5_checked,configuration13RootChunk6_checked,configuration13RootChunk7_checked,configuration13RootChunk8_checked,configuration13RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
