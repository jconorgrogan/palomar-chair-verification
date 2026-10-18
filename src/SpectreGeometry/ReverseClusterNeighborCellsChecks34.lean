module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration34RootChunk0 : List Cell := (rootCells configuration34).drop 0 |>.take 8
theorem configuration34RootChunk0_checked : configuration34RootChunk0.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk1 : List Cell := (rootCells configuration34).drop 8 |>.take 8
theorem configuration34RootChunk1_checked : configuration34RootChunk1.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk2 : List Cell := (rootCells configuration34).drop 16 |>.take 8
theorem configuration34RootChunk2_checked : configuration34RootChunk2.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk3 : List Cell := (rootCells configuration34).drop 24 |>.take 8
theorem configuration34RootChunk3_checked : configuration34RootChunk3.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk4 : List Cell := (rootCells configuration34).drop 32 |>.take 8
theorem configuration34RootChunk4_checked : configuration34RootChunk4.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk5 : List Cell := (rootCells configuration34).drop 40 |>.take 8
theorem configuration34RootChunk5_checked : configuration34RootChunk5.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk6 : List Cell := (rootCells configuration34).drop 48 |>.take 8
theorem configuration34RootChunk6_checked : configuration34RootChunk6.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk7 : List Cell := (rootCells configuration34).drop 56 |>.take 8
theorem configuration34RootChunk7_checked : configuration34RootChunk7.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk8 : List Cell := (rootCells configuration34).drop 64 |>.take 8
theorem configuration34RootChunk8_checked : configuration34RootChunk8.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

def configuration34RootChunk9 : List Cell := (rootCells configuration34).drop 72 |>.take 8
theorem configuration34RootChunk9_checked : configuration34RootChunk9.all (fun a =>
    (neighborCells configuration34).all (cellPairFastB configuration34.sharedPath a)) = true := by decide

theorem placement34_checked : configurationCheckedB configuration34 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration34.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration34 = configuration34RootChunk0 ++ configuration34RootChunk1 ++ configuration34RootChunk2 ++ configuration34RootChunk3 ++ configuration34RootChunk4 ++ configuration34RootChunk5 ++ configuration34RootChunk6 ++ configuration34RootChunk7 ++ configuration34RootChunk8 ++ configuration34RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration34RootChunk0_checked,configuration34RootChunk1_checked,configuration34RootChunk2_checked,configuration34RootChunk3_checked,configuration34RootChunk4_checked,configuration34RootChunk5_checked,configuration34RootChunk6_checked,configuration34RootChunk7_checked,configuration34RootChunk8_checked,configuration34RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
