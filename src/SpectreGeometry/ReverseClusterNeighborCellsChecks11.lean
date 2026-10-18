module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration11RootChunk0 : List Cell := (rootCells configuration11).drop 0 |>.take 8
theorem configuration11RootChunk0_checked : configuration11RootChunk0.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk1 : List Cell := (rootCells configuration11).drop 8 |>.take 8
theorem configuration11RootChunk1_checked : configuration11RootChunk1.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk2 : List Cell := (rootCells configuration11).drop 16 |>.take 8
theorem configuration11RootChunk2_checked : configuration11RootChunk2.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk3 : List Cell := (rootCells configuration11).drop 24 |>.take 8
theorem configuration11RootChunk3_checked : configuration11RootChunk3.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk4 : List Cell := (rootCells configuration11).drop 32 |>.take 8
theorem configuration11RootChunk4_checked : configuration11RootChunk4.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk5 : List Cell := (rootCells configuration11).drop 40 |>.take 8
theorem configuration11RootChunk5_checked : configuration11RootChunk5.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk6 : List Cell := (rootCells configuration11).drop 48 |>.take 8
theorem configuration11RootChunk6_checked : configuration11RootChunk6.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk7 : List Cell := (rootCells configuration11).drop 56 |>.take 8
theorem configuration11RootChunk7_checked : configuration11RootChunk7.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk8 : List Cell := (rootCells configuration11).drop 64 |>.take 8
theorem configuration11RootChunk8_checked : configuration11RootChunk8.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

def configuration11RootChunk9 : List Cell := (rootCells configuration11).drop 72 |>.take 8
theorem configuration11RootChunk9_checked : configuration11RootChunk9.all (fun a =>
    (neighborCells configuration11).all (cellPairFastB configuration11.sharedPath a)) = true := by decide

theorem placement11_checked : configurationCheckedB configuration11 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration11.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration11 = configuration11RootChunk0 ++ configuration11RootChunk1 ++ configuration11RootChunk2 ++ configuration11RootChunk3 ++ configuration11RootChunk4 ++ configuration11RootChunk5 ++ configuration11RootChunk6 ++ configuration11RootChunk7 ++ configuration11RootChunk8 ++ configuration11RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration11RootChunk0_checked,configuration11RootChunk1_checked,configuration11RootChunk2_checked,configuration11RootChunk3_checked,configuration11RootChunk4_checked,configuration11RootChunk5_checked,configuration11RootChunk6_checked,configuration11RootChunk7_checked,configuration11RootChunk8_checked,configuration11RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
