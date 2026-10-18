module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration33RootChunk0 : List Cell := (rootCells configuration33).drop 0 |>.take 8
theorem configuration33RootChunk0_checked : configuration33RootChunk0.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk1 : List Cell := (rootCells configuration33).drop 8 |>.take 8
theorem configuration33RootChunk1_checked : configuration33RootChunk1.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk2 : List Cell := (rootCells configuration33).drop 16 |>.take 8
theorem configuration33RootChunk2_checked : configuration33RootChunk2.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk3 : List Cell := (rootCells configuration33).drop 24 |>.take 8
theorem configuration33RootChunk3_checked : configuration33RootChunk3.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk4 : List Cell := (rootCells configuration33).drop 32 |>.take 8
theorem configuration33RootChunk4_checked : configuration33RootChunk4.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk5 : List Cell := (rootCells configuration33).drop 40 |>.take 8
theorem configuration33RootChunk5_checked : configuration33RootChunk5.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk6 : List Cell := (rootCells configuration33).drop 48 |>.take 8
theorem configuration33RootChunk6_checked : configuration33RootChunk6.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk7 : List Cell := (rootCells configuration33).drop 56 |>.take 8
theorem configuration33RootChunk7_checked : configuration33RootChunk7.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk8 : List Cell := (rootCells configuration33).drop 64 |>.take 8
theorem configuration33RootChunk8_checked : configuration33RootChunk8.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

def configuration33RootChunk9 : List Cell := (rootCells configuration33).drop 72 |>.take 8
theorem configuration33RootChunk9_checked : configuration33RootChunk9.all (fun a =>
    (neighborCells configuration33).all (cellPairFastB configuration33.sharedPath a)) = true := by decide

theorem placement33_checked : configurationCheckedB configuration33 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration33.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration33 = configuration33RootChunk0 ++ configuration33RootChunk1 ++ configuration33RootChunk2 ++ configuration33RootChunk3 ++ configuration33RootChunk4 ++ configuration33RootChunk5 ++ configuration33RootChunk6 ++ configuration33RootChunk7 ++ configuration33RootChunk8 ++ configuration33RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration33RootChunk0_checked,configuration33RootChunk1_checked,configuration33RootChunk2_checked,configuration33RootChunk3_checked,configuration33RootChunk4_checked,configuration33RootChunk5_checked,configuration33RootChunk6_checked,configuration33RootChunk7_checked,configuration33RootChunk8_checked,configuration33RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
