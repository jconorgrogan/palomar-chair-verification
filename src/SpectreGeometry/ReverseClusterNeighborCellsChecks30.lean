module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration30RootChunk0 : List Cell := (rootCells configuration30).drop 0 |>.take 8
theorem configuration30RootChunk0_checked : configuration30RootChunk0.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk1 : List Cell := (rootCells configuration30).drop 8 |>.take 8
theorem configuration30RootChunk1_checked : configuration30RootChunk1.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk2 : List Cell := (rootCells configuration30).drop 16 |>.take 8
theorem configuration30RootChunk2_checked : configuration30RootChunk2.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk3 : List Cell := (rootCells configuration30).drop 24 |>.take 8
theorem configuration30RootChunk3_checked : configuration30RootChunk3.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk4 : List Cell := (rootCells configuration30).drop 32 |>.take 8
theorem configuration30RootChunk4_checked : configuration30RootChunk4.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk5 : List Cell := (rootCells configuration30).drop 40 |>.take 8
theorem configuration30RootChunk5_checked : configuration30RootChunk5.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk6 : List Cell := (rootCells configuration30).drop 48 |>.take 8
theorem configuration30RootChunk6_checked : configuration30RootChunk6.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk7 : List Cell := (rootCells configuration30).drop 56 |>.take 8
theorem configuration30RootChunk7_checked : configuration30RootChunk7.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk8 : List Cell := (rootCells configuration30).drop 64 |>.take 8
theorem configuration30RootChunk8_checked : configuration30RootChunk8.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

def configuration30RootChunk9 : List Cell := (rootCells configuration30).drop 72 |>.take 8
theorem configuration30RootChunk9_checked : configuration30RootChunk9.all (fun a =>
    (neighborCells configuration30).all (cellPairFastB configuration30.sharedPath a)) = true := by decide

theorem placement30_checked : configurationCheckedB configuration30 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration30.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration30 = configuration30RootChunk0 ++ configuration30RootChunk1 ++ configuration30RootChunk2 ++ configuration30RootChunk3 ++ configuration30RootChunk4 ++ configuration30RootChunk5 ++ configuration30RootChunk6 ++ configuration30RootChunk7 ++ configuration30RootChunk8 ++ configuration30RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration30RootChunk0_checked,configuration30RootChunk1_checked,configuration30RootChunk2_checked,configuration30RootChunk3_checked,configuration30RootChunk4_checked,configuration30RootChunk5_checked,configuration30RootChunk6_checked,configuration30RootChunk7_checked,configuration30RootChunk8_checked,configuration30RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
