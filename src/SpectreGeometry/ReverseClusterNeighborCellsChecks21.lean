module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration21RootChunk0 : List Cell := (rootCells configuration21).drop 0 |>.take 8
theorem configuration21RootChunk0_checked : configuration21RootChunk0.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk1 : List Cell := (rootCells configuration21).drop 8 |>.take 8
theorem configuration21RootChunk1_checked : configuration21RootChunk1.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk2 : List Cell := (rootCells configuration21).drop 16 |>.take 8
theorem configuration21RootChunk2_checked : configuration21RootChunk2.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk3 : List Cell := (rootCells configuration21).drop 24 |>.take 8
theorem configuration21RootChunk3_checked : configuration21RootChunk3.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk4 : List Cell := (rootCells configuration21).drop 32 |>.take 8
theorem configuration21RootChunk4_checked : configuration21RootChunk4.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk5 : List Cell := (rootCells configuration21).drop 40 |>.take 8
theorem configuration21RootChunk5_checked : configuration21RootChunk5.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk6 : List Cell := (rootCells configuration21).drop 48 |>.take 8
theorem configuration21RootChunk6_checked : configuration21RootChunk6.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk7 : List Cell := (rootCells configuration21).drop 56 |>.take 8
theorem configuration21RootChunk7_checked : configuration21RootChunk7.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk8 : List Cell := (rootCells configuration21).drop 64 |>.take 8
theorem configuration21RootChunk8_checked : configuration21RootChunk8.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

def configuration21RootChunk9 : List Cell := (rootCells configuration21).drop 72 |>.take 8
theorem configuration21RootChunk9_checked : configuration21RootChunk9.all (fun a =>
    (neighborCells configuration21).all (cellPairFastB configuration21.sharedPath a)) = true := by decide

theorem placement21_checked : configurationCheckedB configuration21 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration21.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration21 = configuration21RootChunk0 ++ configuration21RootChunk1 ++ configuration21RootChunk2 ++ configuration21RootChunk3 ++ configuration21RootChunk4 ++ configuration21RootChunk5 ++ configuration21RootChunk6 ++ configuration21RootChunk7 ++ configuration21RootChunk8 ++ configuration21RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration21RootChunk0_checked,configuration21RootChunk1_checked,configuration21RootChunk2_checked,configuration21RootChunk3_checked,configuration21RootChunk4_checked,configuration21RootChunk5_checked,configuration21RootChunk6_checked,configuration21RootChunk7_checked,configuration21RootChunk8_checked,configuration21RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
