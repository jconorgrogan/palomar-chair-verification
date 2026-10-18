module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration27RootChunk0 : List Cell := (rootCells configuration27).drop 0 |>.take 8
theorem configuration27RootChunk0_checked : configuration27RootChunk0.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk1 : List Cell := (rootCells configuration27).drop 8 |>.take 8
theorem configuration27RootChunk1_checked : configuration27RootChunk1.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk2 : List Cell := (rootCells configuration27).drop 16 |>.take 8
theorem configuration27RootChunk2_checked : configuration27RootChunk2.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk3 : List Cell := (rootCells configuration27).drop 24 |>.take 8
theorem configuration27RootChunk3_checked : configuration27RootChunk3.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk4 : List Cell := (rootCells configuration27).drop 32 |>.take 8
theorem configuration27RootChunk4_checked : configuration27RootChunk4.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk5 : List Cell := (rootCells configuration27).drop 40 |>.take 8
theorem configuration27RootChunk5_checked : configuration27RootChunk5.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk6 : List Cell := (rootCells configuration27).drop 48 |>.take 8
theorem configuration27RootChunk6_checked : configuration27RootChunk6.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk7 : List Cell := (rootCells configuration27).drop 56 |>.take 8
theorem configuration27RootChunk7_checked : configuration27RootChunk7.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk8 : List Cell := (rootCells configuration27).drop 64 |>.take 8
theorem configuration27RootChunk8_checked : configuration27RootChunk8.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

def configuration27RootChunk9 : List Cell := (rootCells configuration27).drop 72 |>.take 8
theorem configuration27RootChunk9_checked : configuration27RootChunk9.all (fun a =>
    (neighborCells configuration27).all (cellPairFastB configuration27.sharedPath a)) = true := by decide

theorem placement27_checked : configurationCheckedB configuration27 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration27.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration27 = configuration27RootChunk0 ++ configuration27RootChunk1 ++ configuration27RootChunk2 ++ configuration27RootChunk3 ++ configuration27RootChunk4 ++ configuration27RootChunk5 ++ configuration27RootChunk6 ++ configuration27RootChunk7 ++ configuration27RootChunk8 ++ configuration27RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration27RootChunk0_checked,configuration27RootChunk1_checked,configuration27RootChunk2_checked,configuration27RootChunk3_checked,configuration27RootChunk4_checked,configuration27RootChunk5_checked,configuration27RootChunk6_checked,configuration27RootChunk7_checked,configuration27RootChunk8_checked,configuration27RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
