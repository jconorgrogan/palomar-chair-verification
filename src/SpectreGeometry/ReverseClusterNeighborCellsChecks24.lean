module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration24RootChunk0 : List Cell := (rootCells configuration24).drop 0 |>.take 8
theorem configuration24RootChunk0_checked : configuration24RootChunk0.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk1 : List Cell := (rootCells configuration24).drop 8 |>.take 8
theorem configuration24RootChunk1_checked : configuration24RootChunk1.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk2 : List Cell := (rootCells configuration24).drop 16 |>.take 8
theorem configuration24RootChunk2_checked : configuration24RootChunk2.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk3 : List Cell := (rootCells configuration24).drop 24 |>.take 8
theorem configuration24RootChunk3_checked : configuration24RootChunk3.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk4 : List Cell := (rootCells configuration24).drop 32 |>.take 8
theorem configuration24RootChunk4_checked : configuration24RootChunk4.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk5 : List Cell := (rootCells configuration24).drop 40 |>.take 8
theorem configuration24RootChunk5_checked : configuration24RootChunk5.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk6 : List Cell := (rootCells configuration24).drop 48 |>.take 8
theorem configuration24RootChunk6_checked : configuration24RootChunk6.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk7 : List Cell := (rootCells configuration24).drop 56 |>.take 8
theorem configuration24RootChunk7_checked : configuration24RootChunk7.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk8 : List Cell := (rootCells configuration24).drop 64 |>.take 8
theorem configuration24RootChunk8_checked : configuration24RootChunk8.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

def configuration24RootChunk9 : List Cell := (rootCells configuration24).drop 72 |>.take 8
theorem configuration24RootChunk9_checked : configuration24RootChunk9.all (fun a =>
    (neighborCells configuration24).all (cellPairFastB configuration24.sharedPath a)) = true := by decide

theorem placement24_checked : configurationCheckedB configuration24 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration24.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration24 = configuration24RootChunk0 ++ configuration24RootChunk1 ++ configuration24RootChunk2 ++ configuration24RootChunk3 ++ configuration24RootChunk4 ++ configuration24RootChunk5 ++ configuration24RootChunk6 ++ configuration24RootChunk7 ++ configuration24RootChunk8 ++ configuration24RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration24RootChunk0_checked,configuration24RootChunk1_checked,configuration24RootChunk2_checked,configuration24RootChunk3_checked,configuration24RootChunk4_checked,configuration24RootChunk5_checked,configuration24RootChunk6_checked,configuration24RootChunk7_checked,configuration24RootChunk8_checked,configuration24RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
