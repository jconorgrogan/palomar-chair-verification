module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration5RootChunk0 : List Cell := (rootCells configuration5).drop 0 |>.take 8
theorem configuration5RootChunk0_checked : configuration5RootChunk0.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk1 : List Cell := (rootCells configuration5).drop 8 |>.take 8
theorem configuration5RootChunk1_checked : configuration5RootChunk1.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk2 : List Cell := (rootCells configuration5).drop 16 |>.take 8
theorem configuration5RootChunk2_checked : configuration5RootChunk2.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk3 : List Cell := (rootCells configuration5).drop 24 |>.take 8
theorem configuration5RootChunk3_checked : configuration5RootChunk3.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk4 : List Cell := (rootCells configuration5).drop 32 |>.take 8
theorem configuration5RootChunk4_checked : configuration5RootChunk4.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk5 : List Cell := (rootCells configuration5).drop 40 |>.take 8
theorem configuration5RootChunk5_checked : configuration5RootChunk5.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk6 : List Cell := (rootCells configuration5).drop 48 |>.take 8
theorem configuration5RootChunk6_checked : configuration5RootChunk6.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk7 : List Cell := (rootCells configuration5).drop 56 |>.take 8
theorem configuration5RootChunk7_checked : configuration5RootChunk7.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

def configuration5RootChunk8 : List Cell := (rootCells configuration5).drop 64 |>.take 8
theorem configuration5RootChunk8_checked : configuration5RootChunk8.all (fun a =>
    (neighborCells configuration5).all (cellPairFastB configuration5.sharedPath a)) = true := by decide

theorem placement5_checked : configurationCheckedB configuration5 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration5.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration5 = configuration5RootChunk0 ++ configuration5RootChunk1 ++ configuration5RootChunk2 ++ configuration5RootChunk3 ++ configuration5RootChunk4 ++ configuration5RootChunk5 ++ configuration5RootChunk6 ++ configuration5RootChunk7 ++ configuration5RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration5RootChunk0_checked,configuration5RootChunk1_checked,configuration5RootChunk2_checked,configuration5RootChunk3_checked,configuration5RootChunk4_checked,configuration5RootChunk5_checked,configuration5RootChunk6_checked,configuration5RootChunk7_checked,configuration5RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
