module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration16RootChunk0 : List Cell := (rootCells configuration16).drop 0 |>.take 8
theorem configuration16RootChunk0_checked : configuration16RootChunk0.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk1 : List Cell := (rootCells configuration16).drop 8 |>.take 8
theorem configuration16RootChunk1_checked : configuration16RootChunk1.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk2 : List Cell := (rootCells configuration16).drop 16 |>.take 8
theorem configuration16RootChunk2_checked : configuration16RootChunk2.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk3 : List Cell := (rootCells configuration16).drop 24 |>.take 8
theorem configuration16RootChunk3_checked : configuration16RootChunk3.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk4 : List Cell := (rootCells configuration16).drop 32 |>.take 8
theorem configuration16RootChunk4_checked : configuration16RootChunk4.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk5 : List Cell := (rootCells configuration16).drop 40 |>.take 8
theorem configuration16RootChunk5_checked : configuration16RootChunk5.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk6 : List Cell := (rootCells configuration16).drop 48 |>.take 8
theorem configuration16RootChunk6_checked : configuration16RootChunk6.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk7 : List Cell := (rootCells configuration16).drop 56 |>.take 8
theorem configuration16RootChunk7_checked : configuration16RootChunk7.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk8 : List Cell := (rootCells configuration16).drop 64 |>.take 8
theorem configuration16RootChunk8_checked : configuration16RootChunk8.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

def configuration16RootChunk9 : List Cell := (rootCells configuration16).drop 72 |>.take 8
theorem configuration16RootChunk9_checked : configuration16RootChunk9.all (fun a =>
    (neighborCells configuration16).all (cellPairFastB configuration16.sharedPath a)) = true := by decide

theorem placement16_checked : configurationCheckedB configuration16 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration16.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration16 = configuration16RootChunk0 ++ configuration16RootChunk1 ++ configuration16RootChunk2 ++ configuration16RootChunk3 ++ configuration16RootChunk4 ++ configuration16RootChunk5 ++ configuration16RootChunk6 ++ configuration16RootChunk7 ++ configuration16RootChunk8 ++ configuration16RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration16RootChunk0_checked,configuration16RootChunk1_checked,configuration16RootChunk2_checked,configuration16RootChunk3_checked,configuration16RootChunk4_checked,configuration16RootChunk5_checked,configuration16RootChunk6_checked,configuration16RootChunk7_checked,configuration16RootChunk8_checked,configuration16RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
