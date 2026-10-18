module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration12RootChunk0 : List Cell := (rootCells configuration12).drop 0 |>.take 8
theorem configuration12RootChunk0_checked : configuration12RootChunk0.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk1 : List Cell := (rootCells configuration12).drop 8 |>.take 8
theorem configuration12RootChunk1_checked : configuration12RootChunk1.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk2 : List Cell := (rootCells configuration12).drop 16 |>.take 8
theorem configuration12RootChunk2_checked : configuration12RootChunk2.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk3 : List Cell := (rootCells configuration12).drop 24 |>.take 8
theorem configuration12RootChunk3_checked : configuration12RootChunk3.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk4 : List Cell := (rootCells configuration12).drop 32 |>.take 8
theorem configuration12RootChunk4_checked : configuration12RootChunk4.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk5 : List Cell := (rootCells configuration12).drop 40 |>.take 8
theorem configuration12RootChunk5_checked : configuration12RootChunk5.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk6 : List Cell := (rootCells configuration12).drop 48 |>.take 8
theorem configuration12RootChunk6_checked : configuration12RootChunk6.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk7 : List Cell := (rootCells configuration12).drop 56 |>.take 8
theorem configuration12RootChunk7_checked : configuration12RootChunk7.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk8 : List Cell := (rootCells configuration12).drop 64 |>.take 8
theorem configuration12RootChunk8_checked : configuration12RootChunk8.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

def configuration12RootChunk9 : List Cell := (rootCells configuration12).drop 72 |>.take 8
theorem configuration12RootChunk9_checked : configuration12RootChunk9.all (fun a =>
    (neighborCells configuration12).all (cellPairFastB configuration12.sharedPath a)) = true := by decide

theorem placement12_checked : configurationCheckedB configuration12 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration12.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration12 = configuration12RootChunk0 ++ configuration12RootChunk1 ++ configuration12RootChunk2 ++ configuration12RootChunk3 ++ configuration12RootChunk4 ++ configuration12RootChunk5 ++ configuration12RootChunk6 ++ configuration12RootChunk7 ++ configuration12RootChunk8 ++ configuration12RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration12RootChunk0_checked,configuration12RootChunk1_checked,configuration12RootChunk2_checked,configuration12RootChunk3_checked,configuration12RootChunk4_checked,configuration12RootChunk5_checked,configuration12RootChunk6_checked,configuration12RootChunk7_checked,configuration12RootChunk8_checked,configuration12RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
