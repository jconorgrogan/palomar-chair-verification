module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration1RootChunk0 : List Cell := (rootCells configuration1).drop 0 |>.take 8
theorem configuration1RootChunk0_checked : configuration1RootChunk0.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk1 : List Cell := (rootCells configuration1).drop 8 |>.take 8
theorem configuration1RootChunk1_checked : configuration1RootChunk1.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk2 : List Cell := (rootCells configuration1).drop 16 |>.take 8
theorem configuration1RootChunk2_checked : configuration1RootChunk2.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk3 : List Cell := (rootCells configuration1).drop 24 |>.take 8
theorem configuration1RootChunk3_checked : configuration1RootChunk3.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk4 : List Cell := (rootCells configuration1).drop 32 |>.take 8
theorem configuration1RootChunk4_checked : configuration1RootChunk4.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk5 : List Cell := (rootCells configuration1).drop 40 |>.take 8
theorem configuration1RootChunk5_checked : configuration1RootChunk5.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk6 : List Cell := (rootCells configuration1).drop 48 |>.take 8
theorem configuration1RootChunk6_checked : configuration1RootChunk6.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk7 : List Cell := (rootCells configuration1).drop 56 |>.take 8
theorem configuration1RootChunk7_checked : configuration1RootChunk7.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

def configuration1RootChunk8 : List Cell := (rootCells configuration1).drop 64 |>.take 8
theorem configuration1RootChunk8_checked : configuration1RootChunk8.all (fun a =>
    (neighborCells configuration1).all (cellPairFastB configuration1.sharedPath a)) = true := by decide

theorem placement1_checked : configurationCheckedB configuration1 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration1.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration1 = configuration1RootChunk0 ++ configuration1RootChunk1 ++ configuration1RootChunk2 ++ configuration1RootChunk3 ++ configuration1RootChunk4 ++ configuration1RootChunk5 ++ configuration1RootChunk6 ++ configuration1RootChunk7 ++ configuration1RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration1RootChunk0_checked,configuration1RootChunk1_checked,configuration1RootChunk2_checked,configuration1RootChunk3_checked,configuration1RootChunk4_checked,configuration1RootChunk5_checked,configuration1RootChunk6_checked,configuration1RootChunk7_checked,configuration1RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
