module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration26RootChunk0 : List Cell := (rootCells configuration26).drop 0 |>.take 8
theorem configuration26RootChunk0_checked : configuration26RootChunk0.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk1 : List Cell := (rootCells configuration26).drop 8 |>.take 8
theorem configuration26RootChunk1_checked : configuration26RootChunk1.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk2 : List Cell := (rootCells configuration26).drop 16 |>.take 8
theorem configuration26RootChunk2_checked : configuration26RootChunk2.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk3 : List Cell := (rootCells configuration26).drop 24 |>.take 8
theorem configuration26RootChunk3_checked : configuration26RootChunk3.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk4 : List Cell := (rootCells configuration26).drop 32 |>.take 8
theorem configuration26RootChunk4_checked : configuration26RootChunk4.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk5 : List Cell := (rootCells configuration26).drop 40 |>.take 8
theorem configuration26RootChunk5_checked : configuration26RootChunk5.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk6 : List Cell := (rootCells configuration26).drop 48 |>.take 8
theorem configuration26RootChunk6_checked : configuration26RootChunk6.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk7 : List Cell := (rootCells configuration26).drop 56 |>.take 8
theorem configuration26RootChunk7_checked : configuration26RootChunk7.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk8 : List Cell := (rootCells configuration26).drop 64 |>.take 8
theorem configuration26RootChunk8_checked : configuration26RootChunk8.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

def configuration26RootChunk9 : List Cell := (rootCells configuration26).drop 72 |>.take 8
theorem configuration26RootChunk9_checked : configuration26RootChunk9.all (fun a =>
    (neighborCells configuration26).all (cellPairFastB configuration26.sharedPath a)) = true := by decide

theorem placement26_checked : configurationCheckedB configuration26 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration26.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration26 = configuration26RootChunk0 ++ configuration26RootChunk1 ++ configuration26RootChunk2 ++ configuration26RootChunk3 ++ configuration26RootChunk4 ++ configuration26RootChunk5 ++ configuration26RootChunk6 ++ configuration26RootChunk7 ++ configuration26RootChunk8 ++ configuration26RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration26RootChunk0_checked,configuration26RootChunk1_checked,configuration26RootChunk2_checked,configuration26RootChunk3_checked,configuration26RootChunk4_checked,configuration26RootChunk5_checked,configuration26RootChunk6_checked,configuration26RootChunk7_checked,configuration26RootChunk8_checked,configuration26RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
