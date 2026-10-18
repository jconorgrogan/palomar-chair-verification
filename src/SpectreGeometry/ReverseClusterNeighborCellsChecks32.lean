module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration32RootChunk0 : List Cell := (rootCells configuration32).drop 0 |>.take 8
theorem configuration32RootChunk0_checked : configuration32RootChunk0.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk1 : List Cell := (rootCells configuration32).drop 8 |>.take 8
theorem configuration32RootChunk1_checked : configuration32RootChunk1.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk2 : List Cell := (rootCells configuration32).drop 16 |>.take 8
theorem configuration32RootChunk2_checked : configuration32RootChunk2.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk3 : List Cell := (rootCells configuration32).drop 24 |>.take 8
theorem configuration32RootChunk3_checked : configuration32RootChunk3.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk4 : List Cell := (rootCells configuration32).drop 32 |>.take 8
theorem configuration32RootChunk4_checked : configuration32RootChunk4.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk5 : List Cell := (rootCells configuration32).drop 40 |>.take 8
theorem configuration32RootChunk5_checked : configuration32RootChunk5.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk6 : List Cell := (rootCells configuration32).drop 48 |>.take 8
theorem configuration32RootChunk6_checked : configuration32RootChunk6.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk7 : List Cell := (rootCells configuration32).drop 56 |>.take 8
theorem configuration32RootChunk7_checked : configuration32RootChunk7.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk8 : List Cell := (rootCells configuration32).drop 64 |>.take 8
theorem configuration32RootChunk8_checked : configuration32RootChunk8.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

def configuration32RootChunk9 : List Cell := (rootCells configuration32).drop 72 |>.take 8
theorem configuration32RootChunk9_checked : configuration32RootChunk9.all (fun a =>
    (neighborCells configuration32).all (cellPairFastB configuration32.sharedPath a)) = true := by decide

theorem placement32_checked : configurationCheckedB configuration32 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration32.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration32 = configuration32RootChunk0 ++ configuration32RootChunk1 ++ configuration32RootChunk2 ++ configuration32RootChunk3 ++ configuration32RootChunk4 ++ configuration32RootChunk5 ++ configuration32RootChunk6 ++ configuration32RootChunk7 ++ configuration32RootChunk8 ++ configuration32RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration32RootChunk0_checked,configuration32RootChunk1_checked,configuration32RootChunk2_checked,configuration32RootChunk3_checked,configuration32RootChunk4_checked,configuration32RootChunk5_checked,configuration32RootChunk6_checked,configuration32RootChunk7_checked,configuration32RootChunk8_checked,configuration32RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
