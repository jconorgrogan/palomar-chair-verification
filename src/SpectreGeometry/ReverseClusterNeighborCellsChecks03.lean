module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration3RootChunk0 : List Cell := (rootCells configuration3).drop 0 |>.take 8
theorem configuration3RootChunk0_checked : configuration3RootChunk0.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk1 : List Cell := (rootCells configuration3).drop 8 |>.take 8
theorem configuration3RootChunk1_checked : configuration3RootChunk1.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk2 : List Cell := (rootCells configuration3).drop 16 |>.take 8
theorem configuration3RootChunk2_checked : configuration3RootChunk2.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk3 : List Cell := (rootCells configuration3).drop 24 |>.take 8
theorem configuration3RootChunk3_checked : configuration3RootChunk3.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk4 : List Cell := (rootCells configuration3).drop 32 |>.take 8
theorem configuration3RootChunk4_checked : configuration3RootChunk4.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk5 : List Cell := (rootCells configuration3).drop 40 |>.take 8
theorem configuration3RootChunk5_checked : configuration3RootChunk5.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk6 : List Cell := (rootCells configuration3).drop 48 |>.take 8
theorem configuration3RootChunk6_checked : configuration3RootChunk6.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk7 : List Cell := (rootCells configuration3).drop 56 |>.take 8
theorem configuration3RootChunk7_checked : configuration3RootChunk7.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

def configuration3RootChunk8 : List Cell := (rootCells configuration3).drop 64 |>.take 8
theorem configuration3RootChunk8_checked : configuration3RootChunk8.all (fun a =>
    (neighborCells configuration3).all (cellPairFastB configuration3.sharedPath a)) = true := by decide

theorem placement3_checked : configurationCheckedB configuration3 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration3.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration3 = configuration3RootChunk0 ++ configuration3RootChunk1 ++ configuration3RootChunk2 ++ configuration3RootChunk3 ++ configuration3RootChunk4 ++ configuration3RootChunk5 ++ configuration3RootChunk6 ++ configuration3RootChunk7 ++ configuration3RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration3RootChunk0_checked,configuration3RootChunk1_checked,configuration3RootChunk2_checked,configuration3RootChunk3_checked,configuration3RootChunk4_checked,configuration3RootChunk5_checked,configuration3RootChunk6_checked,configuration3RootChunk7_checked,configuration3RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
