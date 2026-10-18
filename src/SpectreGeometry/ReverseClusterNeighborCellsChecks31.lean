module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration31RootChunk0 : List Cell := (rootCells configuration31).drop 0 |>.take 8
theorem configuration31RootChunk0_checked : configuration31RootChunk0.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk1 : List Cell := (rootCells configuration31).drop 8 |>.take 8
theorem configuration31RootChunk1_checked : configuration31RootChunk1.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk2 : List Cell := (rootCells configuration31).drop 16 |>.take 8
theorem configuration31RootChunk2_checked : configuration31RootChunk2.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk3 : List Cell := (rootCells configuration31).drop 24 |>.take 8
theorem configuration31RootChunk3_checked : configuration31RootChunk3.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk4 : List Cell := (rootCells configuration31).drop 32 |>.take 8
theorem configuration31RootChunk4_checked : configuration31RootChunk4.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk5 : List Cell := (rootCells configuration31).drop 40 |>.take 8
theorem configuration31RootChunk5_checked : configuration31RootChunk5.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk6 : List Cell := (rootCells configuration31).drop 48 |>.take 8
theorem configuration31RootChunk6_checked : configuration31RootChunk6.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk7 : List Cell := (rootCells configuration31).drop 56 |>.take 8
theorem configuration31RootChunk7_checked : configuration31RootChunk7.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk8 : List Cell := (rootCells configuration31).drop 64 |>.take 8
theorem configuration31RootChunk8_checked : configuration31RootChunk8.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

def configuration31RootChunk9 : List Cell := (rootCells configuration31).drop 72 |>.take 8
theorem configuration31RootChunk9_checked : configuration31RootChunk9.all (fun a =>
    (neighborCells configuration31).all (cellPairFastB configuration31.sharedPath a)) = true := by decide

theorem placement31_checked : configurationCheckedB configuration31 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration31.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration31 = configuration31RootChunk0 ++ configuration31RootChunk1 ++ configuration31RootChunk2 ++ configuration31RootChunk3 ++ configuration31RootChunk4 ++ configuration31RootChunk5 ++ configuration31RootChunk6 ++ configuration31RootChunk7 ++ configuration31RootChunk8 ++ configuration31RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration31RootChunk0_checked,configuration31RootChunk1_checked,configuration31RootChunk2_checked,configuration31RootChunk3_checked,configuration31RootChunk4_checked,configuration31RootChunk5_checked,configuration31RootChunk6_checked,configuration31RootChunk7_checked,configuration31RootChunk8_checked,configuration31RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
