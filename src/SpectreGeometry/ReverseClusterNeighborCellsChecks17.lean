module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration17RootChunk0 : List Cell := (rootCells configuration17).drop 0 |>.take 8
theorem configuration17RootChunk0_checked : configuration17RootChunk0.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk1 : List Cell := (rootCells configuration17).drop 8 |>.take 8
theorem configuration17RootChunk1_checked : configuration17RootChunk1.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk2 : List Cell := (rootCells configuration17).drop 16 |>.take 8
theorem configuration17RootChunk2_checked : configuration17RootChunk2.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk3 : List Cell := (rootCells configuration17).drop 24 |>.take 8
theorem configuration17RootChunk3_checked : configuration17RootChunk3.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk4 : List Cell := (rootCells configuration17).drop 32 |>.take 8
theorem configuration17RootChunk4_checked : configuration17RootChunk4.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk5 : List Cell := (rootCells configuration17).drop 40 |>.take 8
theorem configuration17RootChunk5_checked : configuration17RootChunk5.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk6 : List Cell := (rootCells configuration17).drop 48 |>.take 8
theorem configuration17RootChunk6_checked : configuration17RootChunk6.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk7 : List Cell := (rootCells configuration17).drop 56 |>.take 8
theorem configuration17RootChunk7_checked : configuration17RootChunk7.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk8 : List Cell := (rootCells configuration17).drop 64 |>.take 8
theorem configuration17RootChunk8_checked : configuration17RootChunk8.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

def configuration17RootChunk9 : List Cell := (rootCells configuration17).drop 72 |>.take 8
theorem configuration17RootChunk9_checked : configuration17RootChunk9.all (fun a =>
    (neighborCells configuration17).all (cellPairFastB configuration17.sharedPath a)) = true := by decide

theorem placement17_checked : configurationCheckedB configuration17 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration17.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration17 = configuration17RootChunk0 ++ configuration17RootChunk1 ++ configuration17RootChunk2 ++ configuration17RootChunk3 ++ configuration17RootChunk4 ++ configuration17RootChunk5 ++ configuration17RootChunk6 ++ configuration17RootChunk7 ++ configuration17RootChunk8 ++ configuration17RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration17RootChunk0_checked,configuration17RootChunk1_checked,configuration17RootChunk2_checked,configuration17RootChunk3_checked,configuration17RootChunk4_checked,configuration17RootChunk5_checked,configuration17RootChunk6_checked,configuration17RootChunk7_checked,configuration17RootChunk8_checked,configuration17RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
