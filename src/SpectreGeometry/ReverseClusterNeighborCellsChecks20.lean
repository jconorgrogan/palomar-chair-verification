module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration20RootChunk0 : List Cell := (rootCells configuration20).drop 0 |>.take 8
theorem configuration20RootChunk0_checked : configuration20RootChunk0.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk1 : List Cell := (rootCells configuration20).drop 8 |>.take 8
theorem configuration20RootChunk1_checked : configuration20RootChunk1.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk2 : List Cell := (rootCells configuration20).drop 16 |>.take 8
theorem configuration20RootChunk2_checked : configuration20RootChunk2.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk3 : List Cell := (rootCells configuration20).drop 24 |>.take 8
theorem configuration20RootChunk3_checked : configuration20RootChunk3.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk4 : List Cell := (rootCells configuration20).drop 32 |>.take 8
theorem configuration20RootChunk4_checked : configuration20RootChunk4.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk5 : List Cell := (rootCells configuration20).drop 40 |>.take 8
theorem configuration20RootChunk5_checked : configuration20RootChunk5.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk6 : List Cell := (rootCells configuration20).drop 48 |>.take 8
theorem configuration20RootChunk6_checked : configuration20RootChunk6.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk7 : List Cell := (rootCells configuration20).drop 56 |>.take 8
theorem configuration20RootChunk7_checked : configuration20RootChunk7.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk8 : List Cell := (rootCells configuration20).drop 64 |>.take 8
theorem configuration20RootChunk8_checked : configuration20RootChunk8.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

def configuration20RootChunk9 : List Cell := (rootCells configuration20).drop 72 |>.take 8
theorem configuration20RootChunk9_checked : configuration20RootChunk9.all (fun a =>
    (neighborCells configuration20).all (cellPairFastB configuration20.sharedPath a)) = true := by decide

theorem placement20_checked : configurationCheckedB configuration20 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration20.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration20 = configuration20RootChunk0 ++ configuration20RootChunk1 ++ configuration20RootChunk2 ++ configuration20RootChunk3 ++ configuration20RootChunk4 ++ configuration20RootChunk5 ++ configuration20RootChunk6 ++ configuration20RootChunk7 ++ configuration20RootChunk8 ++ configuration20RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration20RootChunk0_checked,configuration20RootChunk1_checked,configuration20RootChunk2_checked,configuration20RootChunk3_checked,configuration20RootChunk4_checked,configuration20RootChunk5_checked,configuration20RootChunk6_checked,configuration20RootChunk7_checked,configuration20RootChunk8_checked,configuration20RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
