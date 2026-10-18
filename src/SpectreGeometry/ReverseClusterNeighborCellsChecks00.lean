module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration0RootChunk0 : List Cell := (rootCells configuration0).drop 0 |>.take 8
theorem configuration0RootChunk0_checked : configuration0RootChunk0.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk1 : List Cell := (rootCells configuration0).drop 8 |>.take 8
theorem configuration0RootChunk1_checked : configuration0RootChunk1.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk2 : List Cell := (rootCells configuration0).drop 16 |>.take 8
theorem configuration0RootChunk2_checked : configuration0RootChunk2.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk3 : List Cell := (rootCells configuration0).drop 24 |>.take 8
theorem configuration0RootChunk3_checked : configuration0RootChunk3.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk4 : List Cell := (rootCells configuration0).drop 32 |>.take 8
theorem configuration0RootChunk4_checked : configuration0RootChunk4.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk5 : List Cell := (rootCells configuration0).drop 40 |>.take 8
theorem configuration0RootChunk5_checked : configuration0RootChunk5.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk6 : List Cell := (rootCells configuration0).drop 48 |>.take 8
theorem configuration0RootChunk6_checked : configuration0RootChunk6.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk7 : List Cell := (rootCells configuration0).drop 56 |>.take 8
theorem configuration0RootChunk7_checked : configuration0RootChunk7.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

def configuration0RootChunk8 : List Cell := (rootCells configuration0).drop 64 |>.take 8
theorem configuration0RootChunk8_checked : configuration0RootChunk8.all (fun a =>
    (neighborCells configuration0).all (cellPairFastB configuration0.sharedPath a)) = true := by decide

theorem placement0_checked : configurationCheckedB configuration0 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration0.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration0 = configuration0RootChunk0 ++ configuration0RootChunk1 ++ configuration0RootChunk2 ++ configuration0RootChunk3 ++ configuration0RootChunk4 ++ configuration0RootChunk5 ++ configuration0RootChunk6 ++ configuration0RootChunk7 ++ configuration0RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration0RootChunk0_checked,configuration0RootChunk1_checked,configuration0RootChunk2_checked,configuration0RootChunk3_checked,configuration0RootChunk4_checked,configuration0RootChunk5_checked,configuration0RootChunk6_checked,configuration0RootChunk7_checked,configuration0RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
