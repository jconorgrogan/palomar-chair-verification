module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration29RootChunk0 : List Cell := (rootCells configuration29).drop 0 |>.take 8
theorem configuration29RootChunk0_checked : configuration29RootChunk0.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk1 : List Cell := (rootCells configuration29).drop 8 |>.take 8
theorem configuration29RootChunk1_checked : configuration29RootChunk1.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk2 : List Cell := (rootCells configuration29).drop 16 |>.take 8
theorem configuration29RootChunk2_checked : configuration29RootChunk2.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk3 : List Cell := (rootCells configuration29).drop 24 |>.take 8
theorem configuration29RootChunk3_checked : configuration29RootChunk3.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk4 : List Cell := (rootCells configuration29).drop 32 |>.take 8
theorem configuration29RootChunk4_checked : configuration29RootChunk4.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk5 : List Cell := (rootCells configuration29).drop 40 |>.take 8
theorem configuration29RootChunk5_checked : configuration29RootChunk5.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk6 : List Cell := (rootCells configuration29).drop 48 |>.take 8
theorem configuration29RootChunk6_checked : configuration29RootChunk6.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk7 : List Cell := (rootCells configuration29).drop 56 |>.take 8
theorem configuration29RootChunk7_checked : configuration29RootChunk7.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk8 : List Cell := (rootCells configuration29).drop 64 |>.take 8
theorem configuration29RootChunk8_checked : configuration29RootChunk8.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

def configuration29RootChunk9 : List Cell := (rootCells configuration29).drop 72 |>.take 8
theorem configuration29RootChunk9_checked : configuration29RootChunk9.all (fun a =>
    (neighborCells configuration29).all (cellPairFastB configuration29.sharedPath a)) = true := by decide

theorem placement29_checked : configurationCheckedB configuration29 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration29.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration29 = configuration29RootChunk0 ++ configuration29RootChunk1 ++ configuration29RootChunk2 ++ configuration29RootChunk3 ++ configuration29RootChunk4 ++ configuration29RootChunk5 ++ configuration29RootChunk6 ++ configuration29RootChunk7 ++ configuration29RootChunk8 ++ configuration29RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration29RootChunk0_checked,configuration29RootChunk1_checked,configuration29RootChunk2_checked,configuration29RootChunk3_checked,configuration29RootChunk4_checked,configuration29RootChunk5_checked,configuration29RootChunk6_checked,configuration29RootChunk7_checked,configuration29RootChunk8_checked,configuration29RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
