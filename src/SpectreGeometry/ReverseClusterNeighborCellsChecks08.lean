module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration8RootChunk0 : List Cell := (rootCells configuration8).drop 0 |>.take 8
theorem configuration8RootChunk0_checked : configuration8RootChunk0.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk1 : List Cell := (rootCells configuration8).drop 8 |>.take 8
theorem configuration8RootChunk1_checked : configuration8RootChunk1.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk2 : List Cell := (rootCells configuration8).drop 16 |>.take 8
theorem configuration8RootChunk2_checked : configuration8RootChunk2.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk3 : List Cell := (rootCells configuration8).drop 24 |>.take 8
theorem configuration8RootChunk3_checked : configuration8RootChunk3.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk4 : List Cell := (rootCells configuration8).drop 32 |>.take 8
theorem configuration8RootChunk4_checked : configuration8RootChunk4.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk5 : List Cell := (rootCells configuration8).drop 40 |>.take 8
theorem configuration8RootChunk5_checked : configuration8RootChunk5.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk6 : List Cell := (rootCells configuration8).drop 48 |>.take 8
theorem configuration8RootChunk6_checked : configuration8RootChunk6.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk7 : List Cell := (rootCells configuration8).drop 56 |>.take 8
theorem configuration8RootChunk7_checked : configuration8RootChunk7.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

def configuration8RootChunk8 : List Cell := (rootCells configuration8).drop 64 |>.take 8
theorem configuration8RootChunk8_checked : configuration8RootChunk8.all (fun a =>
    (neighborCells configuration8).all (cellPairFastB configuration8.sharedPath a)) = true := by decide

theorem placement8_checked : configurationCheckedB configuration8 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration8.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration8 = configuration8RootChunk0 ++ configuration8RootChunk1 ++ configuration8RootChunk2 ++ configuration8RootChunk3 ++ configuration8RootChunk4 ++ configuration8RootChunk5 ++ configuration8RootChunk6 ++ configuration8RootChunk7 ++ configuration8RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration8RootChunk0_checked,configuration8RootChunk1_checked,configuration8RootChunk2_checked,configuration8RootChunk3_checked,configuration8RootChunk4_checked,configuration8RootChunk5_checked,configuration8RootChunk6_checked,configuration8RootChunk7_checked,configuration8RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
